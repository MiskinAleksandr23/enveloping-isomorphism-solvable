import EnvelopingIsomorphism.Deformation.Kontsevich.PureInfinityForestNormalScale
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian

/-! Full infinity collar extraction for the one-outside-label stratum, in
its actual radial-first shape coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFullOverlap
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestNormalScale
open InfinityForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)

def faceCoordinates (y : Coord (r+1)) : InfinityForestSimpleOverlap.Face x o q :=
  (fun j ↦ RealForestSimpleCluster.normalize (shapePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (shapePosition hdim x o (Sum.inl (Sum.inl j.val)) y),
    fun j ↦ RealForestSimpleCluster.normalizeReal (shapePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (shapePosition hdim x o (Sum.inl (Sum.inr j.val)) y).re)

variable (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

include hall in
theorem faceCoordinates_face (w : Coord r) :
    faceCoordinates hdim x o q (facePoint hdim x o w) =
      InfinityForestSimpleCoordinates.coordinates hdim x o q w := by
  apply Prod.ext
  · rfl
  · funext j
    change _ = if j.val ∈ boundaryClusterBlock (lower x o) (upper x o) then _ else _
    rw [if_pos (hall j.val j.property)]
    rfl

include ho in
theorem contDiffAt_faceCoordinates (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (faceCoordinates hdim x o q) (facePoint hdim x o z.val) := by
  have hc := (contDiff_shapePosition hdim x o (Sum.inl (Sum.inl 0))).contDiffAt (x := facePoint hdim x o z.val)
  have hp : 0 < (shapePosition hdim x o (Sum.inl (Sum.inl 0)) (facePoint hdim x o z.val)).im :=
    InfinityForestSimpleCluster.shapeAnchor_pos hdim x o ho z
  unfold faceCoordinates
  exact (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hc
      (contDiff_shapePosition hdim x o _).contDiffAt hp).prodMk
    (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalizeReal hc
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt) hp)

def map (y : Coord (r+1)) : Coord (r+1) :=
  faceEmbedding 0 (InfinityForestNormalScale.simpleRadius hdim x o q y)
    (InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall
      (faceCoordinates hdim x o q y))

include ho hq hne hall in
theorem map_face (w : Coord r) : map hdim x o q ho hq hne hall (facePoint hdim x o w) =
    faceEmbedding 0 0 (InfinityForestFaceChangeVariables.map hdim x o q ho hq hne hall w) := by
  rw [map, InfinityForestNormalScale.simpleRadius_face, faceCoordinates_face hdim x o q hall]
  rfl

include ho hq hne hall in
theorem contDiffAt_map (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val) := by
  have hr := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).contDiff.contDiffAt).mul
    (InfinityForestNormalScale.contDiffAt_normalScale hdim x o q ho hq hne z)
  change ContDiffAt ℝ ⊤ (InfinityForestNormalScale.simpleRadius hdim x o q) (facePoint hdim x o z.val) at hr
  have hf := (InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall).contDiff.contDiffAt.comp _
    (contDiffAt_faceCoordinates hdim x o q ho z)
  simp only [Function.comp_def] at hf
  apply contDiffAt_pi.mpr
  intro j
  cases j using Fin.cases with
  | zero => simpa only [map, faceEmbedding, Fin.insertNth_apply_same] using hr
  | succ j => simpa only [map, faceEmbedding, ← Fin.succAbove_zero,
      Fin.insertNth_apply_succAbove] using (contDiffAt_pi.mp hf j)

include ho hq hne hall in
theorem normal_differential (z : ForestRadialFaceLocalization.source hdim x o) (v : Coord (r+1)) :
    fderiv ℝ (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val) v 0 =
      InfinityForestNormalScale.normalScale hdim x o q (facePoint hdim x o z.val) * v (axis hdim x o) := by
  let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (0 : Fin (r+1))
  have h := (proj.hasFDerivAt.comp (facePoint hdim x o z.val)
    ((contDiffAt_map hdim x o q ho hq hne hall z).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : proj ∘ map hdim x o q ho hq hne hall = InfinityForestNormalScale.simpleRadius hdim x o q := by
    funext y
    simp [proj, map, faceEmbedding]
  rw [he, InfinityForestNormalScale.fderiv_simpleRadius_face hdim x o q ho hq hne z] at h
  exact (congrArg (fun L : Coord (r+1) →L[ℝ] ℝ ↦ L v) h).symm

include ho hq hne hall in
theorem face_derivative (z : ForestRadialFaceLocalization.source hdim x o) :
    RadialFaceJacobian.faceDerivative (axis hdim x o) 0
      (fderiv ℝ (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val)) =
        fderiv ℝ (InfinityForestFaceChangeVariables.map hdim x o q ho hq hne hall) z.val := by
  have h := (ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1))).hasFDerivAt.comp z.val
    ((((contDiffAt_map hdim x o q ho hq hne hall z).differentiableAt (by simp)).hasFDerivAt).comp z.val
      (hasFDerivAt_faceEmbedding (axis hdim x o) 0 z.val))
  have he : ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1)) ∘
      map hdim x o q ho hq hne hall ∘ facePoint hdim x o =
        InfinityForestFaceChangeVariables.map hdim x o q ho hq hne hall := by
    funext w
    change ForestRadialFaceImmersion.faceProjection 0 (map hdim x o q ho hq hne hall (facePoint hdim x o w)) = _
    rw [map_face hdim x o q ho hq hne hall]
    ext j
    simp [ForestRadialFaceImmersion.faceProjection, faceEmbedding]
  rw [he] at h
  exact h.fderiv.symm

include ho hq hne hall in
/-- The only deleted-axis permutation is explicit; the normal factor is the
proved positive geometric multiplier of the full extracted collar. -/
theorem jacobian_eq_normal_mul_face (z : ForestRadialFaceLocalization.source hdim x o) :
    OrientedFormChangeVariables.jacobian (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val) =
      (-1 : ℝ) ^ (axis hdim x o).val *
        InfinityForestNormalScale.normalScale hdim x o q (facePoint hdim x o z.val) *
          InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val := by
  rw [OrientedFormChangeVariables.jacobian,
    RadialFaceJacobian.det_eq_normal_mul_face _ 0 _ _ (normal_differential hdim x o q ho hq hne hall z),
    face_derivative hdim x o q ho hq hne hall z]
  simp only [Fin.val_zero, Nat.zero_add, InfinityForestFaceChangeVariables.jacobian]

include ho hq hne hall in
/-- The native outward face multiplier is exactly the radial-first minus
sign times the actual full collar determinant sign. No sign is assumed. -/
theorem outward_jacobian_sign (z : ForestRadialFaceLocalization.source hdim x o) :
    -((-1 : ℝ) ^ (axis hdim x o).val) *
      (InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val /
        |InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val|) =
      -(OrientedFormChangeVariables.jacobian (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val) /
        |OrientedFormChangeVariables.jacobian (map hdim x o q ho hq hne hall) (facePoint hdim x o z.val)|) := by
  rw [jacobian_eq_normal_mul_face hdim x o q ho hq hne hall z]
  have hc := InfinityForestNormalScale.normalScale_face_pos hdim x o q ho hq hne z
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hc]
  have hj := abs_ne_zero.mpr (InfinityForestFaceChangeVariables.jacobian_ne_zero hdim x o q ho hq hne hall z)
  field_simp
  <;> ring

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFullOverlap
