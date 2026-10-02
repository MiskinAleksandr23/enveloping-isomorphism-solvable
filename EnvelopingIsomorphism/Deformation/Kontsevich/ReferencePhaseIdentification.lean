import EnvelopingIsomorphism.Deformation.Kontsevich.ReferenceNormIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits

/-! Exact identification from a fixed nonzero real reference and a variable imaginary
height. These are finite algebraic formulas used by boundary-anchored infinity
charts, including height zero. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology

/-- Two boundary targets measured from the reflected interior anchor. -/
def boundaryRatioTriple {n m : ℕ} (a : Fin n) (j k : Fin m) : Configuration.DoubledTriple n m :=
  ⟨(Sum.inr a, Sum.inl (Sum.inr j), Sum.inl (Sum.inr k)), by simp⟩

theorem realReference_add_mul_I_ne_zero {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    (s : ℂ) + (r : ℂ) * Complex.I ≠ 0 := by
  intro h
  apply hs
  simpa using congrArg Complex.re h

theorem complexPhase_realReference_re {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    (complexPhase ((s : ℂ) + (r : ℂ) * Complex.I) : ℂ).re =
      s / ‖(s : ℂ) + (r : ℂ) * Complex.I‖ := by
  rw [complexPhase_coe (realReference_add_mul_I_ne_zero hs r)]
  simp

theorem complexPhase_realReference_im {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    (complexPhase ((s : ℂ) + (r : ℂ) * Complex.I) : ℂ).im =
      r / ‖(s : ℂ) + (r : ℂ) * Complex.I‖ := by
  rw [complexPhase_coe (realReference_add_mul_I_ne_zero hs r)]
  simp

theorem complexPhase_realReference_re_ne_zero {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    (complexPhase ((s : ℂ) + (r : ℂ) * Complex.I) : ℂ).re ≠ 0 := by
  rw [complexPhase_realReference_re hs]
  exact div_ne_zero hs (norm_ne_zero_iff.mpr (realReference_add_mul_I_ne_zero hs r))

/-- The signed real reference fixes the scale; only its phase and nonzero real component are needed. -/
def recoverReferenceHeight (s : ℝ) (θ : Circle) : ℝ := s * (θ : ℂ).im / (θ : ℂ).re

theorem recoverReferenceHeight_phase {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    recoverReferenceHeight s (complexPhase ((s : ℂ) + (r : ℂ) * Complex.I)) = r := by
  rw [recoverReferenceHeight, complexPhase_realReference_re hs, complexPhase_realReference_im hs]
  have hn := norm_ne_zero_iff.mpr (realReference_add_mul_I_ne_zero hs r)
  field_simp [hs, hn]

theorem continuousAt_recoverReferenceHeight (s : ℝ) (θ : Circle) (hθ : (θ : ℂ).re ≠ 0) :
    ContinuousAt (recoverReferenceHeight s) θ := by
  exact (continuousAt_const.mul (Complex.continuous_im.comp continuous_subtype_val).continuousAt).div
    (Complex.continuous_re.comp continuous_subtype_val).continuousAt hθ

theorem continuousOn_recoverReferenceHeight (s : ℝ) :
    ContinuousOn (recoverReferenceHeight s) {θ : Circle | (θ : ℂ).re ≠ 0} :=
  fun θ hθ ↦ (continuousAt_recoverReferenceHeight s θ hθ).continuousWithinAt

theorem normalizedNormRatio_lt_one_right {z w : ℂ} (hw : w ≠ 0) :
    (normalizedNormRatio z w : ℝ) < 1 :=
  referenceNormRatio_lt_one (norm_pos_iff.mpr hw) z

/-- A nonzero reference vector gives exact finite identification from the stored phase and norm ratio. -/
theorem recoverRelativePosition_normalizedNormRatio {z w : ℂ} (hw : w ≠ 0) :
    (‖w‖ : ℂ) * recoverRelativePosition (complexPhase z) (normalizedNormRatio z w) = z :=
  recoverRelativePosition_referenceNormRatio (norm_pos_iff.mpr hw) z

end EnvelopingIsomorphism.Deformation.Kontsevich
