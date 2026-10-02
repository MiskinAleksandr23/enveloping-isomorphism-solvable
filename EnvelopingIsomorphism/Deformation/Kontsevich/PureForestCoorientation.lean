import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFullOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoorientation

/-! The pure collar Jacobian factors through one explicit linear extraction
of the original physical coordinates. The original chart orientation extends
to the face by its genuine inward path. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestCoorientation
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestNormalScale OrientedFormChangeVariables
open PureForestSimpleCluster (lower upper)
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin m)
  (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)

def physicalFace : GraphForms.Coordinates n m →L[ℝ] PureForestSimpleOverlap.Face x o a b :=
  LinearMap.toContinuousLinearMap {
    toFun p := ((p.1, p.2 a, fun j ↦ p.2 j.val), 0)
    map_add' p q := by ext <;> simp
    map_smul' c p := by ext <;> simp }

def physicalExtraction : GraphForms.Coordinates n m →L[ℝ] Coord (r+1) :=
  ContinuousLinearMap.pi fun j ↦ Fin.cases
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ ℝ) b) - (ContinuousLinearMap.proj a)).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin m → ℝ)))
    (fun k ↦ (ContinuousLinearMap.proj k).comp
      ((PureForestFaceChangeVariables.simpleCoordinates hdim x o a b ho hl hu hab hcard).toContinuousLinearMap.comp
        (physicalFace x o a b))) j

/-- Concrete shear and coordinate permutation, in the actual inherited real
bases: first boundary b minus boundary a, then the quotient coordinates. -/
def extraction : Coord (r+1) →L[ℝ] Coord (r+1) :=
  (physicalExtraction hdim x o a b ho hl hu hab hcard).comp
    (ForestGlobalGraphStokes.nativeCoordinates hdim).symm.toContinuousLinearMap

include ho hl hu hab hcard in
theorem map_eq_extraction_chart : PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard =
    extraction hdim x o a b ho hl hu hab hcard ∘ ForestGlobalGraphStokes.chart hdim x := by
  funext y
  simp only [Function.comp_apply]
  rw [ForestGlobalGraphStokes.chart_apply]
  simp only [Function.comp_apply, extraction, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  ext j
  cases j using Fin.cases with
  | zero =>
    simp only [PureForestFullOverlap.map, faceEmbedding, Fin.insertNth_apply_same,
      physicalExtraction, ContinuousLinearMap.pi_apply, Fin.cases_zero,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply]
    rw [PureForestNormalScale.simpleRadius_eq_boundary_gap hdim x o a b ho hl hu hab]
    unfold ForestPositiveChartSmooth.forwardCoordinates RealForestNormalScale.height
      RealForestNormalScale.position RealForestNormalScale.fullParameters
      ForestPositiveChartSmooth.anchorPoint ForestPositiveChartSmooth.leafPositions
    simp only [ContinuousLinearMap.coe_snd']
    ring
  | succ j =>
    simp only [PureForestFullOverlap.map, faceEmbedding, Fin.insertNth_zero', Fin.cons_succ, physicalExtraction, ContinuousLinearMap.pi_apply,
      Fin.succAbove_zero, Fin.cases_succ, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe]
    unfold PureForestFaceChangeVariables.simpleCoordinates PureBoundaryGraphIntegral.faceCoordinates
      PureBoundaryGraphQuotient.twoPointCoordinates
    congr 2

include ho hl hu hab hcard in
theorem contDiffAt_original (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (ForestGlobalGraphStokes.chart hdim x) (facePoint hdim x o z.val) := by
  have hh : (ForestPositiveChartSmooth.anchorPoint 0 x
      ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm (facePoint hdim x o z.val))).im ≠ 0 :=
    (PureForestSimpleCluster.anchor_pos hdim x o ho z).ne'
  exact (ForestGlobalGraphStokes.nativeCoordinates hdim).contDiff.contDiffAt.comp _
    ((ForestPositiveChartSmooth.contDiffAt_forwardCoordinates 0 x _ hh).comp _
      (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff.contDiffAt)

include ho hl hu hab hcard in
theorem jacobian_factor (z : ForestRadialFaceLocalization.source hdim x o) :
    jacobian (PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) =
      (extraction hdim x o a b ho hl hu hab hcard).det *
        jacobian (ForestGlobalGraphStokes.chart hdim x) (facePoint hdim x o z.val) := by
  have h := ((extraction hdim x o a b ho hl hu hab hcard).hasFDerivAt.comp (facePoint hdim x o z.val)
    ((contDiffAt_original hdim x o a b ho hl hu hab hcard z).differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [← map_eq_extraction_chart hdim x o a b ho hl hu hab hcard] at h
  unfold jacobian
  rw [h]
  exact LinearMap.det_comp _ _

include ho hl hu hab hcard in
theorem extraction_det_ne_zero (z : ForestRadialFaceLocalization.source hdim x o) :
    (extraction hdim x o a b ho hl hu hab hcard).det ≠ 0 := by
  have hn : jacobian (PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard)
      (facePoint hdim x o z.val) ≠ 0 := by
    rw [PureForestFullOverlap.jacobian_eq_normal_mul_face hdim x o a b ho hl hu hab hcard z]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (PureForestNormalScale.normalScale_face_pos hdim x o a b ho hl hu hab z).ne')
      (PureForestFaceChangeVariables.jacobian_ne_zero hdim x o a b ho hl hu hab hcard z)
  rw [jacobian_factor hdim x o a b ho hl hu hab hcard z] at hn
  exact (mul_ne_zero_iff.mp hn).1

include ho hl hu hab hcard in
theorem original_orientation_at_face (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (ForestGlobalGraphStokes.chart hdim x) (facePoint hdim x o z.val) =
      |jacobian (ForestGlobalGraphStokes.chart hdim x) (facePoint hdim x o z.val)| := by
  have ht := PairedForestOverlapJacobian.inward_tendsto hdim x o z
  have hJ : ContinuousAt (jacobian (ForestGlobalGraphStokes.chart hdim x)) (facePoint hdim x o z.val) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((contDiffAt_original hdim x o a b ho hl hu hab hcard z).continuousAt_fderiv (by simp))
  have heq : (fun t ↦ ε * jacobian (ForestGlobalGraphStokes.chart hdim x)
      (PairedForestOverlapJacobian.inward hdim x o z.val t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun t ↦ |jacobian (ForestGlobalGraphStokes.chart hdim x)
        (PairedForestOverlapJacobian.inward hdim x o z.val t)|) :=
    (PairedForestOverlapJacobian.inward_eventually_positiveRegion hdim x o z hz).mono
      (fun t ht ↦ hε _ ht)
  exact tendsto_nhds_unique ((hJ.const_mul ε).tendsto.comp ht)
    ((hJ.abs.tendsto.comp ht).congr' heq.symm)

include ho hl hu hab hcard in
/-- The existing original-chart orientation determines the full pure collar
orientation up to the determinant of the explicitly defined coordinate shear
and permutation. No new orientation multiplier is a hypothesis. -/
theorem full_orientation_at_face (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) =
      ((extraction hdim x o a b ho hl hu hab hcard).det /
        |(extraction hdim x o a b ho hl hu hab hcard).det|) *
      |jacobian (PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val)| := by
  rw [jacobian_factor hdim x o a b ho hl hu hab hcard z, abs_mul]
  have h := original_orientation_at_face hdim x o a b ho hl hu hab hcard z hz ε hε
  have hn := abs_ne_zero.mpr (extraction_det_ne_zero hdim x o a b ho hl hu hab hcard z)
  field_simp
  linear_combination (extraction hdim x o a b ho hl hu hab hcard).det * h

include ho hl hu hab hcard in
/-- Exact native-to-scalar outward orientation: only the explicit physical
coordinate determinant remains to be evaluated combinatorially. -/
theorem native_face_orientation (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val =
      -((extraction hdim x o a b ho hl hu hab hcard).det /
        |(extraction hdim x o a b ho hl hu hab hcard).det|) *
        |PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val| := by
  have h := RadialFaceJacobian.outward_sign_transport (axis hdim x o) 0
    (fderiv ℝ (PureForestFullOverlap.map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val))
    (PureForestNormalScale.normalScale hdim x o a b (facePoint hdim x o z.val))
    (PureForestNormalScale.normalScale_face_pos hdim x o a b ho hl hu hab z)
    (PureForestFullOverlap.normal_differential hdim x o a b ho hl hu hab hcard z) ε
    ((extraction hdim x o a b ho hl hu hab hcard).det / |(extraction hdim x o a b ho hl hu hab hcard).det|)
    (full_orientation_at_face hdim x o a b ho hl hu hab hcard z hz ε hε)
  rw [PureForestFullOverlap.face_derivative hdim x o a b ho hl hu hab hcard z] at h
  simpa only [Fin.val_zero, pow_zero, neg_mul, mul_neg, mul_one,
    PureForestFaceChangeVariables.jacobian] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestCoorientation
