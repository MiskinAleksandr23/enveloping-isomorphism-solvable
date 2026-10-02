import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestFullOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian

/-! The full physical Jacobian factorization through the actual paired
forest/simple collar overlap, in the existing standard graph coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestFullOverlap
open ClusterFaceOrientation.Interior BoxStokes OrientedFormChangeVariables
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

local instance : DecidableEq (ClusterAngularCoordinates.CoordinateIndex (0 : Fin (n + 1))
    (anchor x o ho) (reference x o ho) (S x o ho) m) := Classical.decEq _

def simpleBasis : Module.Basis (Fin (r + 1)) ℝ (Angular x o ho) :=
  (ClusterAngularCoordinates.coordinateBasis.reindex
    (sourceIndex (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho))).reindex
      (finCongr hdim)

def graphBasis : Module.Basis (Fin (r + 1)) ℝ (GraphForms.Coordinates n m) :=
  (GraphForms.realBasis n m).reindex (finCongr hdim)

def simpleCoordinates : Angular x o ho ≃L[ℝ] Coord (r + 1) :=
  (simpleBasis hdim x o ho).equivFun.toContinuousLinearEquiv

theorem graphCoordinates_eq : (graphBasis hdim).equivFun.toContinuousLinearEquiv =
    ForestGlobalGraphStokes.nativeCoordinates hdim := by
  ext q j
  obtain ⟨j, rfl⟩ := (finCongr hdim).surjective j
  simp only [graphBasis, Module.Basis.equivFun_apply, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply, LinearEquiv.coe_toContinuousLinearEquiv]
  change _ = ForestGlobalGraphStokes.coordinateCast hdim (GraphForms.realCoordinates n m q) (finCongr hdim j)
  rw [ForestGlobalGraphStokes.coordinateCast_apply]
  rfl

private theorem det_in_coordinates {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (b : Module.Basis (Fin (r + 1)) ℝ E) (c : Module.Basis (Fin (r + 1)) ℝ F) (D : E →L[ℝ] F) :
    (c.equivFun.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (D.comp b.equivFun.toContinuousLinearEquiv.symm.toContinuousLinearMap)).det =
        (LinearMap.toMatrix b c D.toLinearMap).det := by
  change LinearMap.det (c.equivFun.toLinearMap.comp (D.toLinearMap.comp b.equivFun.symm.toLinearMap)) = _
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin (r + 1)))]
  congr 1

/-- The target simple chart's physical sign is the actual finite basis sign,
with the native angle-before-radius polar minus sign. -/
def simpleSign : ℝ := -(Equiv.Perm.sign (basisPermutation (m := m)
    (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)) : ℝ)

theorem simpleSign_sq : simpleSign (m := m) x o ho * simpleSign (m := m) x o ho = 1 := by
  simp [simpleSign, ← Int.cast_mul, ← Units.val_mul]

theorem physical_matrix_det (q : Angular x o ho) :
    (LinearMap.toMatrix (simpleBasis hdim x o ho) (graphBasis hdim)
      (fderiv ℝ physicalInsertion q).toLinearMap).det =
        simpleSign (m := m) x o ho * q.toFree.radius ^ (2 * (S x o ho).card - 3) := by
  have hm : LinearMap.toMatrix (simpleBasis hdim x o ho) (graphBasis hdim)
      (fderiv ℝ physicalInsertion q).toLinearMap =
    Matrix.reindex (finCongr hdim) (finCongr hdim)
      (LinearMap.toMatrix
        (ClusterAngularCoordinates.coordinateBasis.reindex
          (sourceIndex (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)))
        (GraphForms.realBasis n m) (fderiv ℝ physicalInsertion q).toLinearMap) := by
    ext j k
    simp [simpleBasis, graphBasis, LinearMap.toMatrix_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
  rw [hm, Matrix.det_reindex_self, det_physicalInsertion (anchor_mem x o ho)
    (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)]
  simp only [simpleSign, ClusterFreeCoordinates.radius, ClusterAngularCoordinates.toFree, mul_neg, neg_mul]

def realOverlap (u : Circle) : Coord (r + 1) → Coord (r + 1) :=
  simpleCoordinates hdim x o ho ∘ overlap hdim x o ho u

theorem contDiffAt_realOverlap (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) :=
  (simpleCoordinates hdim x o ho).contDiff.contDiffAt.comp _ (contDiffAt_overlap hdim x o ho z)

/-- Exact full Jacobian identity; the only differentiability hypothesis is
that of the already explicit overlap, discharged locally above. -/
theorem jacobian_chart_factor (u : Circle) (w : Coord (r + 1))
    (hheight : rawHeight hdim x o w ≠ 0) (hshape : 0 < rawShapeRadius hdim x o ho w)
    (hd : DifferentiableAt ℝ (overlap hdim x o ho u) w) :
    jacobian (ForestGlobalGraphStokes.chart hdim x) w =
      (simpleSign (m := m) x o ho * (PairedForestNormalScale.simpleRadius hdim x o ho w) ^ (2 * (S x o ho).card - 3)) *
        jacobian (realOverlap hdim x o ho u) w := by
  have hloc : (fun y ↦ physicalInsertion (overlap hdim x o ho u y)) =ᶠ[nhds w]
      (fun y ↦ ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)) := by
    have hH := (contDiff_rawHeight hdim x o).continuous.continuousAt.eventually_ne hheight
    have hR : Continuous (rawShapeRadius hdim x o ho) :=
      ((contDiff_rawShape hdim x o ho (reference x o ho)).continuous.sub
        (contDiff_rawShape hdim x o ho (anchor x o ho)).continuous).norm
    filter_upwards [hH, hR.continuousAt.eventually (isOpen_Ioi.mem_nhds hshape)] with y hyH hyR
    exact physicalInsertion_overlap hdim x o ho u y hyH hyR
  have hp : DifferentiableAt ℝ (physicalInsertion : Angular x o ho → GraphForms.Coordinates n m)
      (overlap hdim x o ho u w) :=
    (ClusterStandardCoordinates.freeGraph 0).differentiableAt.comp _
      (InteriorClusterInsertionOrientation.differentiableAt_insertion _)
  let P := (ForestGlobalGraphStokes.nativeCoordinates hdim).toContinuousLinearMap.comp
    ((fderiv ℝ physicalInsertion (overlap hdim x o ho u w)).comp
      (simpleCoordinates hdim x o ho).symm.toContinuousLinearMap)
  have hD : fderiv ℝ (ForestGlobalGraphStokes.chart hdim x) w =
      P.comp (fderiv ℝ (realOverlap hdim x o ho u) w) := by
    have he : (fun y ↦ ForestGlobalGraphStokes.nativeCoordinates hdim (physicalInsertion (overlap hdim x o ho u y))) =ᶠ[nhds w]
        (ForestGlobalGraphStokes.chart hdim x) := hloc.fun_comp (ForestGlobalGraphStokes.nativeCoordinates hdim)
    rw [← he.fderiv_eq]
    rw [show (fun y ↦ ForestGlobalGraphStokes.nativeCoordinates hdim (physicalInsertion (overlap hdim x o ho u y))) =
      ForestGlobalGraphStokes.nativeCoordinates hdim ∘ physicalInsertion ∘ overlap hdim x o ho u from rfl]
    rw [fderiv_comp w (ForestGlobalGraphStokes.nativeCoordinates hdim).differentiableAt (hp.comp w hd),
      fderiv_comp w hp hd, ContinuousLinearEquiv.fderiv,
      realOverlap, fderiv_comp w (simpleCoordinates hdim x o ho).differentiableAt hd,
      ContinuousLinearEquiv.fderiv]
    ext v
    simp [P]
  have hP : P.det = simpleSign (m := m) x o ho *
      (PairedForestNormalScale.simpleRadius hdim x o ho w) ^ (2 * (S x o ho).card - 3) := by
    unfold P
    rw [← graphCoordinates_eq hdim]
    rw [show (simpleCoordinates hdim x o ho) = (simpleBasis hdim x o ho).equivFun.toContinuousLinearEquiv from rfl,
      det_in_coordinates, physical_matrix_det, overlap_radius]
  rw [jacobian, hD]
  change LinearMap.det (P.toLinearMap.comp (fderiv ℝ (realOverlap hdim x o ho u) w).toLinearMap) = _
  rw [LinearMap.det_comp]
  change P.det * (fderiv ℝ (realOverlap hdim x o ho u) w).det = _
  rw [hP]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
