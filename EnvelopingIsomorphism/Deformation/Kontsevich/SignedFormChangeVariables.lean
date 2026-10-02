import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Basic

/-! Signed change of variables on connected source regions. The sign is
derived from the actual derivative and the intermediate value theorem. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SignedFormChangeVariables

open Set MeasureTheory OrientedFormChangeVariables BoxStokes
open scoped Topology

variable {d : ℕ} (e : OpenPartialHomeomorph (Coord d) (Coord d))

theorem continuousOn_jacobian (he : ContDiffOn ℝ 1 e e.source) :
    ContinuousOn (jacobian e) e.source :=
  ContinuousLinearMap.continuous_det.comp_continuousOn
    (he.continuousOn_fderiv_of_isOpen e.open_source le_rfl)

theorem jacobian_ne_zero (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (z : Coord d) (hz : z ∈ e.source) :
    jacobian e z ≠ 0 := by
  have h := jacobian_inverse_mul e he hinv z hz
  intro hzero
  simp [hzero] at h

/-- One sign suffices on each genuinely preconnected source region; no sign
on a disconnected chart source is assumed. -/
theorem exists_sign (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (s : Set (Coord d)) (hse : s ⊆ e.source) (hconn : IsPreconnected s) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ z ∈ s, ε * jacobian e z = |jacobian e z| := by
  obtain hpos | hneg := hconn.mapsTo_Ioi_or_Iio
    ((continuousOn_jacobian e he).mono hse)
    (fun z hz => jacobian_ne_zero e he hinv z (hse hz))
  · refine ⟨1, Or.inl rfl, fun z hz => ?_⟩
    rw [one_mul, abs_of_pos (hpos hz)]
  · refine ⟨-1, Or.inr rfl, fun z hz => ?_⟩
    rw [neg_one_mul, abs_of_neg (hneg hz)]

/-- The orientation multiplier converts the true signed pullback integral
to the original integral. This includes negatively oriented charts. -/
theorem sign_mul_integral_pullback_eq_image (he : ContDiffOn ℝ 1 e e.source)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source)
    (ε : ℝ) (hε : ∀ z ∈ s, ε * jacobian e z = |jacobian e z|)
    (ω : TopForm d) :
    ε * (∫ z in s, density (pullback e ω) z) = ∫ y in e '' s, density ω y := by
  rw [← integral_const_mul,
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (hasFDerivWithinAt_on_subset e he hse) (e.injOn.mono hse) (density ω)]
  apply setIntegral_congr_fun hs
  intro z hz
  change ε * density (pullback e ω) z = |jacobian e z| • density ω (e z)
  rw [density_pullback, ← mul_assoc, hε z hz, smul_eq_mul]

theorem exists_signed_integral_identity (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source)
    (hconn : IsPreconnected s) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ z ∈ s, ε * jacobian e z = |jacobian e z|) ∧
      ∀ ω : TopForm d,
        ε * (∫ z in s, density (pullback e ω) z) = ∫ y in e '' s, density ω y := by
  obtain ⟨ε, hε, hsign⟩ := exists_sign e he hinv s hse hconn
  exact ⟨ε, hε, hsign, sign_mul_integral_pullback_eq_image e he s hs hse ε hsign⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.SignedFormChangeVariables
