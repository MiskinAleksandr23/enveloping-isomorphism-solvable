import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOrderedAngularForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngleForms

/-! The internal factor of the actual extended harmonic edge form, pulled back
along relabeled rotating normalized planar positions. This identifies the
form itself, before any integration or choice of forest face measure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFacePullback

open InteriorFiberAngleSplit ContinuousAlternatingMap

/-- Actual coarse center and the two normalized velocities of an internal edge. -/
def facePositions {N : ℕ} (σ : Equiv.Perm (Point N)) (s t : Point N) (z : ℂ)
    (x : Parameters N) : VariableClusterFace :=
  (z, (relabeledPoint σ x s, relabeledPoint σ x t))

theorem contDiff_relabeledPoint {N : ℕ} (σ : Equiv.Perm (Point N)) (j : Point N) :
    ContDiff ℝ ⊤ (fun x : Parameters N ↦ relabeledPoint σ x j) :=
  (contDiff_circleParameter.comp contDiff_fst).mul
    ((contDiff_normalizedPoint (σ.symm j)).comp contDiff_snd)

theorem contDiff_facePositions {N : ℕ} (σ : Equiv.Perm (Point N))
    (s t : Point N) (z : ℂ) : ContDiff ℝ ⊤ (facePositions σ s t z) :=
  contDiff_const.prodMk ((contDiff_relabeledPoint σ s).prodMk (contDiff_relabeledPoint σ t))

theorem difference_facePositions {N : ℕ} (σ : Equiv.Perm (Point N)) (s t : Point N) (z : ℂ) :
    variableClusterDifference ∘ facePositions σ s t z = relabeledDifference σ s t := rfl

theorem fderiv_difference_facePositions {N : ℕ} (σ : Equiv.Perm (Point N))
    (s t : Point N) (z : ℂ) (x : Parameters N) :
    variableClusterDifference.comp (fderiv ℝ (facePositions σ s t z) x) =
      fderiv ℝ (relabeledDifference σ s t) x := by
  have h := (variableClusterDifference.hasFDerivAt.comp x
    ((contDiff_facePositions σ s t z).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  rw [difference_facePositions] at h
  exact h.symm

/-- Literal equality with the edge form used in ordered planar vanishing.
The left side is the genuine extended harmonic form restricted to radius zero. -/
theorem internalFace_pullback {N : ℕ} (σ : Equiv.Perm (Point N))
    (s t : Point N) (hst : s ≠ t) (z : ℂ) (hz : 0 < z.im)
    (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    ((variableInternalClusterExtendedForm
      (variableClusterFaceEmbedding (facePositions σ s t z x))).compContinuousLinearMap
        variableClusterFaceEmbedding).compContinuousLinearMap
          (fderiv ℝ (facePositions σ s t z) x) = relabeledEdgeForm σ s t x := by
  have hdiff : relabeledPoint σ x t - relabeledPoint σ x s ≠ 0 := by
    change rotatedDifference (σ.symm s) (σ.symm t) x ≠ 0
    rw [rotatedDifference_factor]
    exact mul_ne_zero (circleParameter_ne_zero x.1)
      (shapeDifference_ne_zero hx (σ.symm.injective.ne hst))
  rw [variableInternalClusterExtendedForm_face _ hz hdiff]
  change (angularForm (relabeledDifference σ s t x)).compContinuousLinearMap
    (variableClusterDifference.comp (fderiv ℝ (facePositions σ s t z) x)) = _
  rw [fderiv_difference_facePositions]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarInnerFacePullback
