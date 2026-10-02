import EnvelopingIsomorphism.Deformation.Kontsevich.RelativeCoordinateIdentification

/-! Relative complex coordinates with an arbitrary positive reference length. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

def referenceNormRatio (R : ℝ) (z : ℂ) : ℝ := ‖z‖ / (‖z‖ + R)

theorem referenceNormRatio_lt_one {R : ℝ} (hR : 0 < R) (z : ℂ) :
    referenceNormRatio R z < 1 := by
  apply (div_lt_one (add_pos_of_nonneg_of_pos (norm_nonneg z) hR)).mpr
  linarith

theorem referenceNormRatio_div {R : ℝ} (hR : 0 < R) (z : ℂ) :
    R * (referenceNormRatio R z / (1 - referenceNormRatio R z)) = ‖z‖ := by
  have hsum : ‖z‖ + R ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg z) hR)
  have hd : 1 - referenceNormRatio R z = R / (‖z‖ + R) := by
    unfold referenceNormRatio
    field_simp
    ring
  rw [hd, referenceNormRatio]
  field_simp

/-- Explicit inverse, continuous wherever the compact ratio is less than one. -/
theorem recoverRelativePosition_referenceNormRatio {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (R : ℂ) * recoverRelativePosition (complexPhase z) (referenceNormRatio R z) = z := by
  rw [recoverRelativePosition, ← mul_assoc, ← Complex.ofReal_mul, referenceNormRatio_div hR,
    norm_mul_complexPhase]

theorem complex_eq_of_phase_referenceNormRatio {R : ℝ} (hR : 0 < R) {z w : ℂ}
    (hphase : complexPhase z = complexPhase w)
    (hratio : referenceNormRatio R z = referenceNormRatio R w) : z = w := by
  rw [← recoverRelativePosition_referenceNormRatio hR z,
    ← recoverRelativePosition_referenceNormRatio hR w, hphase, hratio]

end EnvelopingIsomorphism.Deformation.Kontsevich
