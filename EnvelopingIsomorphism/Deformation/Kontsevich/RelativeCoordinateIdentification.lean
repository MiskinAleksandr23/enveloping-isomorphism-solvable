import EnvelopingIsomorphism.Deformation.Kontsevich.Phase

/-! Reconstruct a relative complex position from its direction and its
distance ratio to a reference pair of unit length. These are actual coordinates
used in the compactification, not additional boundary data. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

theorem norm_mul_complexPhase (z : ℂ) :
    (‖z‖ : ℂ) * (complexPhase z : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [complexPhase_coe hz]
    have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp

/-- The compact distance ratio when the reference distance is one. -/
def unitNormRatio (z : ℂ) : ℝ := ‖z‖ / (‖z‖ + 1)

theorem unitNormRatio_nonneg (z : ℂ) : 0 ≤ unitNormRatio z :=
  div_nonneg (norm_nonneg z) (by positivity)

theorem unitNormRatio_lt_one (z : ℂ) : unitNormRatio z < 1 := by
  apply (div_lt_one (by positivity : 0 < ‖z‖ + 1)).mpr
  linarith

theorem one_sub_unitNormRatio (z : ℂ) : 1 - unitNormRatio z = 1 / (‖z‖ + 1) := by
  unfold unitNormRatio
  have h : ‖z‖ + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem norm_eq_unitNormRatio_div (z : ℂ) :
    ‖z‖ = unitNormRatio z / (1 - unitNormRatio z) := by
  rw [one_sub_unitNormRatio, unitNormRatio]
  have h : ‖z‖ + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- Explicit reconstruction from the compact direction and unit-reference ratio. -/
def recoverRelativePosition (θ : Circle) (r : ℝ) : ℂ :=
  ((r / (1 - r) : ℝ) : ℂ) * (θ : ℂ)

/-- The inverse coordinate formula is continuous throughout the finite-ratio chart. -/
theorem continuous_recoverRelativePosition :
    Continuous (fun p : Circle × Set.Iio (1 : ℝ) ↦ recoverRelativePosition p.1 p.2) := by
  have hr : Continuous (fun p : Circle × Set.Iio (1 : ℝ) ↦ (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hd : ∀ p : Circle × Set.Iio (1 : ℝ), 1 - (p.2 : ℝ) ≠ 0 :=
    fun p ↦ ne_of_gt (sub_pos.mpr p.2.property)
  exact (Complex.continuous_ofReal.comp (hr.div (continuous_const.sub hr) hd)).mul
    (continuous_subtype_val.comp continuous_fst)

theorem recoverRelativePosition_phase_ratio (z : ℂ) :
    recoverRelativePosition (complexPhase z) (unitNormRatio z) = z := by
  rw [recoverRelativePosition, ← norm_eq_unitNormRatio_div, norm_mul_complexPhase]

theorem complex_eq_of_phase_unitNormRatio {z w : ℂ}
    (hphase : complexPhase z = complexPhase w) (hratio : unitNormRatio z = unitNormRatio w) :
    z = w := by
  rw [← recoverRelativePosition_phase_ratio z, ← recoverRelativePosition_phase_ratio w,
    hphase, hratio]

/-- Unbundled form for direct application to the stored triple ratios. -/
theorem complex_eq_of_phase_ratio {z w : ℂ}
    (hphase : complexPhase z = complexPhase w)
    (hratio : ‖z‖ / (‖z‖ + 1) = ‖w‖ / (‖w‖ + 1)) : z = w :=
  complex_eq_of_phase_unitNormRatio hphase hratio

/-- No finite-dimensionality or finiteness of the index type is needed to
recover a normalized array from these relative coordinates. -/
theorem normalized_positions_eq {ι : Type*} (a b : ι) (v w : ι → ℂ)
    (hva : v a = 0) (hwa : w a = 0) (hvb : ‖v b‖ = 1) (hwb : ‖w b‖ = 1)
    (hphase : ∀ i, i ≠ a → complexPhase (v i - v a) = complexPhase (w i - w a))
    (hratio : ∀ i, i ≠ a →
      ‖v i - v a‖ / (‖v i - v a‖ + ‖v b - v a‖) =
      ‖w i - w a‖ / (‖w i - w a‖ + ‖w b - w a‖)) : v = w := by
  funext i
  by_cases hi : i = a
  · simp only [hi, hva, hwa]
  · apply complex_eq_of_phase_ratio
    · simpa only [hva, hwa, sub_zero] using hphase i hi
    · simpa only [hva, hwa, sub_zero, hvb, hwb] using hratio i hi

end EnvelopingIsomorphism.Deformation.Kontsevich
