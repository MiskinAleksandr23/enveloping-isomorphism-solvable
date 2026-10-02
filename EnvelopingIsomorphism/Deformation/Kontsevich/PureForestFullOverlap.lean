import EnvelopingIsomorphism.Deformation.Kontsevich.PureInfinityForestNormalScale
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian

/-! Full pure collar extraction in the same radial-first target coordinates
as the actual boundary integral. Its normal scale and cofactor are derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFullOverlap
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestNormalScale
open PureForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin m)

def faceCoordinates (y : Coord (r+1)) : PureForestSimpleOverlap.Face x o a b :=
  ((fun j ↦ RealForestSimpleCluster.normalize (position hdim x (Sum.inl (Sum.inl 0)) y)
      (position hdim x (Sum.inl (Sum.inl j.succ)) y),
    RealForestSimpleCluster.normalizeReal (position hdim x (Sum.inl (Sum.inl 0)) y)
      (position hdim x (Sum.inl (Sum.inr a)) y).re,
    fun j ↦ RealForestSimpleCluster.normalizeReal (position hdim x (Sum.inl (Sum.inl 0)) y)
      (position hdim x (Sum.inl (Sum.inr j.val)) y).re),
    fun j ↦ ((shapePosition hdim x o (Sum.inl (Sum.inr j.val)) y).re -
      (shapePosition hdim x o (Sum.inl (Sum.inr a)) y).re) /
        PureForestNormalScale.gap hdim x o a b y)

variable (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)

include ho hl hu hab in
theorem faceCoordinates_face (w : Coord r) :
    faceCoordinates hdim x o a b (facePoint hdim x o w) =
      PureForestSimpleCoordinates.coordinates hdim x o a b w := by
  have ha := (RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) a).mpr
    (PureForestSimpleCluster.left_mem x o a b hl hu hab)
  have hi := position_inside_factor hdim x o (facePoint hdim x o w) (Sum.inl (Sum.inr a)) ha
  simp only [facePoint, faceEmbedding, Fin.insertNth_apply_same, zero_mul, zero_smul, add_zero] at hi
  change position hdim x (Sum.inl (Sum.inr a)) (facePoint hdim x o w) =
    nodePosition hdim x o (facePoint hdim x o w) at hi
  unfold faceCoordinates
  rw [hi]
  rfl

include ho hl hu hab in
theorem contDiffAt_faceCoordinates (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (faceCoordinates hdim x o a b) (facePoint hdim x o z.val) := by
  have hc := (contDiff_position hdim x (Sum.inl (Sum.inl 0))).contDiffAt (x := facePoint hdim x o z.val)
  have hp : 0 < (position hdim x (Sum.inl (Sum.inl 0)) (facePoint hdim x o z.val)).im :=
    PureForestSimpleCluster.anchor_pos hdim x o ho z
  have hg : 0 < PureForestNormalScale.gap hdim x o a b (facePoint hdim x o z.val) :=
    PureForestSimpleCluster.gap_pos hdim x o ho a b hl hu hab z
  unfold faceCoordinates
  refine ContDiffAt.prodMk ?_ (contDiffAt_pi.mpr fun j ↦ ?_)
  · refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hc
      (contDiff_position hdim x _).contDiffAt hp) ?_
    exact (RealForestSimpleCoordinates.smooth_normalizeReal hc
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_position hdim x _).contDiffAt) hp).prodMk
      (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalizeReal hc
        (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_position hdim x _).contDiffAt) hp)
  · exact ((Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt).sub
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt)).div
      (PureForestNormalScale.contDiff_gap hdim x o a b).contDiffAt hg.ne'

def map (y : Coord (r+1)) : Coord (r+1) :=
  faceEmbedding 0 (PureForestNormalScale.simpleRadius hdim x o a b y)
    (PureForestFaceChangeVariables.simpleCoordinates hdim x o a b ho hl hu hab hcard
      (faceCoordinates hdim x o a b y))

include ho hl hu hab hcard in
theorem map_face (w : Coord r) : map hdim x o a b ho hl hu hab hcard (facePoint hdim x o w) =
    faceEmbedding 0 0 (PureForestFaceChangeVariables.map hdim x o a b ho hl hu hab hcard w) := by
  rw [map, PureForestNormalScale.simpleRadius_face, faceCoordinates_face hdim x o a b ho hl hu hab]
  rfl

include ho hl hu hab hcard in
theorem contDiffAt_map (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) := by
  have hr := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).contDiff.contDiffAt).mul
    (PureForestNormalScale.contDiffAt_normalScale hdim x o a b ho z)
  change ContDiffAt ℝ ⊤ (PureForestNormalScale.simpleRadius hdim x o a b) (facePoint hdim x o z.val) at hr
  have hf := (PureForestFaceChangeVariables.simpleCoordinates hdim x o a b ho hl hu hab hcard).contDiff.contDiffAt.comp _
    (contDiffAt_faceCoordinates hdim x o a b ho hl hu hab z)
  simp only [Function.comp_def] at hf
  apply contDiffAt_pi.mpr
  intro j
  cases j using Fin.cases with
  | zero => simpa only [map, faceEmbedding, Fin.insertNth_apply_same] using hr
  | succ j => simpa only [map, faceEmbedding, ← Fin.succAbove_zero,
      Fin.insertNth_apply_succAbove] using (contDiffAt_pi.mp hf j)

include ho hl hu hab hcard in
theorem normal_differential (z : ForestRadialFaceLocalization.source hdim x o) (v : Coord (r+1)) :
    fderiv ℝ (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) v 0 =
      PureForestNormalScale.normalScale hdim x o a b (facePoint hdim x o z.val) * v (axis hdim x o) := by
  let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (0 : Fin (r+1))
  have h := (proj.hasFDerivAt.comp (facePoint hdim x o z.val)
    ((contDiffAt_map hdim x o a b ho hl hu hab hcard z).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : proj ∘ map hdim x o a b ho hl hu hab hcard = PureForestNormalScale.simpleRadius hdim x o a b := by
    funext y
    simp [proj, map, faceEmbedding]
  rw [he, PureForestNormalScale.fderiv_simpleRadius_face hdim x o a b ho z] at h
  exact (congrArg (fun L : Coord (r+1) →L[ℝ] ℝ ↦ L v) h).symm

include ho hl hu hab hcard in
theorem face_derivative (z : ForestRadialFaceLocalization.source hdim x o) :
    RadialFaceJacobian.faceDerivative (axis hdim x o) 0
      (fderiv ℝ (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val)) =
        fderiv ℝ (PureForestFaceChangeVariables.map hdim x o a b ho hl hu hab hcard) z.val := by
  have h := (ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1))).hasFDerivAt.comp z.val
    ((((contDiffAt_map hdim x o a b ho hl hu hab hcard z).differentiableAt (by simp)).hasFDerivAt).comp z.val
      (hasFDerivAt_faceEmbedding (axis hdim x o) 0 z.val))
  have he : ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1)) ∘
      map hdim x o a b ho hl hu hab hcard ∘ facePoint hdim x o =
        PureForestFaceChangeVariables.map hdim x o a b ho hl hu hab hcard := by
    funext w
    change ForestRadialFaceImmersion.faceProjection 0 (map hdim x o a b ho hl hu hab hcard (facePoint hdim x o w)) = _
    rw [map_face hdim x o a b ho hl hu hab hcard]
    ext j
    simp [ForestRadialFaceImmersion.faceProjection, faceEmbedding]
  rw [he] at h
  exact h.fderiv.symm

include ho hl hu hab hcard in
/-- The only deleted-axis permutation is explicit; the normal factor is the
proved positive geometric multiplier of the full extracted collar. -/
theorem jacobian_eq_normal_mul_face (z : ForestRadialFaceLocalization.source hdim x o) :
    OrientedFormChangeVariables.jacobian (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) =
      (-1 : ℝ) ^ (axis hdim x o).val *
        PureForestNormalScale.normalScale hdim x o a b (facePoint hdim x o z.val) *
          PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val := by
  rw [OrientedFormChangeVariables.jacobian,
    RadialFaceJacobian.det_eq_normal_mul_face _ 0 _ _ (normal_differential hdim x o a b ho hl hu hab hcard z),
    face_derivative hdim x o a b ho hl hu hab hcard z]
  simp only [Fin.val_zero, Nat.zero_add, PureForestFaceChangeVariables.jacobian]

include ho hl hu hab hcard in
/-- The native outward face multiplier is exactly the radial-first minus
sign times the actual full collar determinant sign. No sign is assumed. -/
theorem outward_jacobian_sign (z : ForestRadialFaceLocalization.source hdim x o) :
    -((-1 : ℝ) ^ (axis hdim x o).val) *
      (PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val /
        |PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val|) =
      -(OrientedFormChangeVariables.jacobian (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val) /
        |OrientedFormChangeVariables.jacobian (map hdim x o a b ho hl hu hab hcard) (facePoint hdim x o z.val)|) := by
  rw [jacobian_eq_normal_mul_face hdim x o a b ho hl hu hab hcard z]
  have hc := PureForestNormalScale.normalScale_face_pos hdim x o a b ho hl hu hab z
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hc]
  have hj := abs_ne_zero.mpr (PureForestFaceChangeVariables.jacobian_ne_zero hdim x o a b ho hl hu hab hcard z)
  field_simp
  <;> ring

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFullOverlap
