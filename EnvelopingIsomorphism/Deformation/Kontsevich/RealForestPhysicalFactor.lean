import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestAnchorNormalization

/-! Actual physical insertion and outside-anchor normalization of the proper
real collar. The only fixed multiplier is the determinant of its explicit
linear coordinate permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalFactor
open Configuration ForestRadialFaceClassification BoxStokes RealForestNormalScale
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (normalize normalizeReal lower upper)
open RealForestFullOverlap RealForestFullJacobian RealForestAnchorNormalization
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

def physicalOutput : Coord (r+1) ≃L[ℝ] Coord (r+1) :=
  (fullCoordinates hdim x o a b ha hb).symm.trans
    ((RealClusterInsertionCoordinates.outputCoordinates ha hb).symm.trans
      ((ClusterStandardCoordinates.freeGraph b).trans (ForestGlobalGraphStokes.nativeCoordinates hdim)))

def physicalSign : ℝ := (physicalOutput hdim x o a b ha hb).toLinearMap.det /
  |(physicalOutput hdim x o a b ha hb).toLinearMap.det|

theorem physicalOutput_det_ne_zero : (physicalOutput hdim x o a b ha hb).toLinearMap.det ≠ 0 :=
  (physicalOutput hdim x o a b ha hb).toLinearEquiv.isUnit_det'.ne_zero

theorem physicalSign_sq : physicalSign hdim x o a b ha hb * physicalSign hdim x o a b ha hb = 1 := by
  unfold physicalSign
  have hn := physicalOutput_det_ne_zero hdim x o a b ha hb
  have hs := sq_abs ((physicalOutput hdim x o a b ha hb).toLinearMap.det)
  field_simp
  nlinarith

def physicalInsertionReal (y : Coord (r+1)) : Coord (r+1) :=
  ForestGlobalGraphStokes.nativeCoordinates hdim
    (ClusterFaceOrientation.Real.physicalInsertion (lower x o) (upper x o)
      ((fullCoordinates hdim x o a b ha hb).symm y))

theorem differentiableAt_physicalInsertionReal (y : Coord (r+1)) :
    DifferentiableAt ℝ (physicalInsertionReal hdim x o a b ha hb) y := by
  exact (ForestGlobalGraphStokes.nativeCoordinates hdim).differentiableAt.comp y
    (((ClusterStandardCoordinates.freeGraph b).differentiableAt.comp _
      (RealClusterInsertionOrientation.differentiableAt_insertion _ _ _)).comp y
        (fullCoordinates hdim x o a b ha hb).symm.differentiableAt)

theorem det_physicalInsertionReal (q : BoundaryClusterFreeCoordinates b a (labelsSet x o) m) :
    (fderiv ℝ (physicalInsertionReal hdim x o a b ha hb)
      (fullCoordinates hdim x o a b ha hb q)).det =
    (physicalOutput hdim x o a b ha hb).toLinearMap.det *
      q.radius ^ (2 * (labelsSet x o).card + (boundaryClusterBlock (lower x o) (upper x o)).card - 2) := by
  let E := fullCoordinates hdim x o a b ha hb
  let G := RealClusterInsertionJacobian.groupedInsertion (lower x o) (upper x o) ha hb
  let F := fun y => E (G (E.symm y))
  have he : physicalInsertionReal hdim x o a b ha hb =
      physicalOutput hdim x o a b ha hb ∘ F := by
    funext y
    simp [physicalInsertionReal, physicalOutput, F, G, E, RealClusterInsertionJacobian.groupedInsertion,
      ClusterFaceOrientation.Real.physicalInsertion]
  have hG := RealClusterInsertionJacobian.differentiableAt_groupedInsertion (lower x o) (upper x o) ha hb q
  have hG' : DifferentiableAt ℝ G (E.symm (E q)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hG
  have hF : DifferentiableAt ℝ F (E q) := E.differentiableAt.comp _
    (hG'.comp _ E.symm.differentiableAt)
  rw [he, fderiv_comp (E q) (physicalOutput hdim x o a b ha hb).differentiableAt hF,
    ContinuousLinearEquiv.fderiv]
  change LinearMap.det ((physicalOutput hdim x o a b ha hb).toLinearMap.comp
    (fderiv ℝ F (E q)).toLinearMap) = _
  rw [LinearMap.det_comp, GraphForms.det_fderiv_linearConjugate E G q hG,
    RealClusterInsertionJacobian.det_fderiv_groupedInsertion]

private theorem normalize_twice (w v p : ℂ) (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    normalize (normalize w v) (normalize w p) = normalize v p := by
  apply Complex.ext
  · simp only [RealForestSimpleCluster.normalize_re, RealForestSimpleCluster.normalize_im]
    unfold normalizeReal
    rw [RealForestSimpleCluster.normalize_re, RealForestSimpleCluster.normalize_im]
    unfold normalizeReal
    field_simp
    <;> ring
  · simp only [RealForestSimpleCluster.normalize_im]
    field_simp

private theorem normalizeReal_twice (w v : ℂ) (t : ℝ) (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    normalizeReal (normalize w v) (normalizeReal w t) = normalizeReal v t := by
  simp only [normalizeReal, RealForestSimpleCluster.normalize_re, RealForestSimpleCluster.normalize_im]
  field_simp
  <;> ring

def originalCoordinates (y : Coord (r+1)) : GraphForms.Coordinates n m :=
  ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)

def normalizedChart (y : Coord (r+1)) : Coord (r+1) :=
  ForestGlobalGraphStokes.nativeCoordinates hdim (outsideAnchorRaw b (originalCoordinates hdim x y))

theorem originalCoordinates_interior (y : Coord (r+1)) (h0 : 0 < height hdim x 0 y) (j : Fin (n+1)) :
    GraphForms.interiorPoint j (originalCoordinates hdim x y) =
      normalize (position hdim x (Sum.inl (Sum.inl 0)) y) (position hdim x (Sum.inl (Sum.inl j)) y) := by
  cases j using Fin.cases with
  | zero => exact (RealForestSimpleCluster.normalize_self _ h0).symm
  | succ j =>
    simp only [originalCoordinates, GraphForms.interiorPoint_succ, ForestPositiveChartSmooth.forwardCoordinates,
      Equiv.swap_self, Equiv.refl_apply]
    rfl

variable (ho : RealForestCoarsePositions.IsFixed x o)

include ho ha hb in
theorem physicalInsertion_overlap (y : Coord (r+1)) (h0 : 0 < height hdim x 0 y)
    (hB : 0 < height hdim x b y) (hA : 0 < shapeHeight hdim x o a y) :
    ClusterFaceOrientation.Real.physicalInsertion (lower x o) (upper x o) (overlap hdim x o a b y) =
      outsideAnchorRaw b (originalCoordinates hdim x y) := by
  apply Prod.ext
  · funext j
    change _ = normalize (GraphForms.interiorPoint b _) (GraphForms.interiorPoint (b.succAbove j) _)
    rw [originalCoordinates_interior hdim x y h0, originalCoordinates_interior hdim x y h0,
      normalize_twice _ _ _ h0.ne' hB.ne']
    exact insertion_interior hdim x o a b ho ha hb y hB hA (b.succAbove j)
  · funext j
    change _ = normalizeReal (GraphForms.interiorPoint b _) ((originalCoordinates hdim x y).2 j)
    rw [originalCoordinates_interior hdim x y h0]
    change _ = normalizeReal
      (normalize (position hdim x (Sum.inl (Sum.inl 0)) y) (position hdim x (Sum.inl (Sum.inl b)) y))
      (normalizeReal (position hdim x (Sum.inl (Sum.inl 0)) y) (position hdim x (Sum.inl (Sum.inr j)) y).re)
    rw [normalizeReal_twice _ _ _ h0.ne' hB.ne']
    exact insertion_boundary hdim x o a b ho ha y hB hA j

include ho ha hb in
theorem jacobian_normalized_physical (y : Coord (r+1)) (h0 : 0 < height hdim x 0 y)
    (hB : 0 < height hdim x b y) (hA : 0 < shapeHeight hdim x o a y)
    (hd : DifferentiableAt ℝ (overlap hdim x o a b) y) :
    OrientedFormChangeVariables.jacobian (normalizedChart hdim x b) y =
      ((physicalOutput hdim x o a b ha hb).toLinearMap.det *
        (simpleRadius hdim x o a b y) ^
          (2 * (labelsSet x o).card + (boundaryClusterBlock (lower x o) (upper x o)).card - 2)) *
      OrientedFormChangeVariables.jacobian (RealForestFullJacobian.map hdim x o a b ha hb) y := by
  have hloc : physicalInsertionReal hdim x o a b ha hb ∘ RealForestFullJacobian.map hdim x o a b ha hb =ᶠ[nhds y]
      normalizedChart hdim x b := by
    filter_upwards [(contDiff_height hdim x 0).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds h0),
      (contDiff_height hdim x b).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hB),
      (contDiff_shapeHeight hdim x o a).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)] with w hw0 hwB hwA
    simp only [Function.comp_apply, physicalInsertionReal, RealForestFullJacobian.map,
      ContinuousLinearEquiv.symm_apply_apply, normalizedChart]
    rw [physicalInsertion_overlap hdim x o a b ha hb ho w hw0 hwB hwA]
  have hm : DifferentiableAt ℝ (RealForestFullJacobian.map hdim x o a b ha hb) y :=
    (fullCoordinates hdim x o a b ha hb).differentiableAt.comp y hd
  unfold OrientedFormChangeVariables.jacobian
  rw [← hloc.fderiv_eq, fderiv_comp y (differentiableAt_physicalInsertionReal hdim x o a b ha hb _) hm]
  change LinearMap.det ((fderiv ℝ (physicalInsertionReal hdim x o a b ha hb)
    (RealForestFullJacobian.map hdim x o a b ha hb y)).toLinearMap.comp
    (fderiv ℝ (RealForestFullJacobian.map hdim x o a b ha hb) y).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (fderiv ℝ (physicalInsertionReal hdim x o a b ha hb)
    (fullCoordinates hdim x o a b ha hb (overlap hdim x o a b y))).det *
    (fderiv ℝ (RealForestFullJacobian.map hdim x o a b ha hb) y).det = _
  rw [det_physicalInsertionReal, overlap_radius]

def outsideAnchorReal (y : Coord (r+1)) : Coord (r+1) :=
  ForestGlobalGraphStokes.nativeCoordinates hdim
    (outsideAnchorRaw b ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y))

theorem normalizedChart_eq : normalizedChart hdim x b =
    outsideAnchorReal hdim b ∘ ForestGlobalGraphStokes.chart hdim x := by
  funext y
  simp only [Function.comp_apply, outsideAnchorReal, ForestGlobalGraphStokes.chart_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem jacobian_normalized_original (y : Coord (r+1)) (h0 : 0 < height hdim x 0 y)
    (hB : 0 < height hdim x b y) :
    OrientedFormChangeVariables.jacobian (normalizedChart hdim x b) y =
      (1 / (GraphForms.interiorPoint b (originalCoordinates hdim x y)).im ^ (GraphForms.dimension n m + 1)) *
        OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim x) y := by
  have hbpos : 0 < (GraphForms.interiorPoint b (originalCoordinates hdim x y)).im := by
    rw [originalCoordinates_interior hdim x y h0, RealForestSimpleCluster.normalize_im]
    exact div_pos hB h0
  have hd := differentiableAt_outsideAnchorRaw b (originalCoordinates hdim x y) hbpos.ne'
  have hg : DifferentiableAt ℝ (ForestGlobalGraphStokes.chart hdim x) y :=
    ((ForestGlobalGraphStokes.nativeCoordinates hdim).differentiableAt.comp y
      (((ForestPositiveChartSmooth.contDiffAt_forwardCoordinates (ν := ⊤) 0 x _ h0.ne').differentiableAt (by simp)).comp y
        (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.differentiableAt))
  have he : (ForestGlobalGraphStokes.nativeCoordinates hdim).symm
      (ForestGlobalGraphStokes.chart hdim x y) = originalCoordinates hdim x y := by
    rw [ForestGlobalGraphStokes.chart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hf : DifferentiableAt ℝ (outsideAnchorReal hdim b) (ForestGlobalGraphStokes.chart hdim x y) :=
    (ForestGlobalGraphStokes.nativeCoordinates hdim).differentiableAt.comp _
      ((he.symm ▸ hd).comp _ (ForestGlobalGraphStokes.nativeCoordinates hdim).symm.differentiableAt)
  unfold OrientedFormChangeVariables.jacobian
  rw [normalizedChart_eq, fderiv_comp y hf hg]
  change LinearMap.det ((fderiv ℝ (outsideAnchorReal hdim b) (ForestGlobalGraphStokes.chart hdim x y)).toLinearMap.comp
    (fderiv ℝ (ForestGlobalGraphStokes.chart hdim x) y).toLinearMap) = _
  rw [LinearMap.det_comp]
  congr 1
  rw [ForestGlobalGraphStokes.chart_apply]
  change (fderiv ℝ (fun z => ForestGlobalGraphStokes.nativeCoordinates hdim
    (outsideAnchorRaw b ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm z)))
    (ForestGlobalGraphStokes.nativeCoordinates hdim (originalCoordinates hdim x y))).det = _
  exact (GraphForms.det_fderiv_linearConjugate (ForestGlobalGraphStokes.nativeCoordinates hdim)
    (outsideAnchorRaw b) (originalCoordinates hdim x y) hd).trans
    (det_outsideAnchorRaw b _ hbpos.ne')

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalFactor
