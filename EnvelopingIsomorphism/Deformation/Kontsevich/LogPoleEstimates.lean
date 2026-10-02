import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadiusForm

/-! Concrete logarithmic-pole estimates in one complex normal coordinate.
The measure is actual two-dimensional Lebesgue volume on ℂ. No configuration
compactification or vanishing-integral hypothesis is used. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogPole

open Filter MeasureTheory Set Metric
open scoped Topology

/-- A positive radial power dominates every fixed power of the absolute logarithm. -/
theorem tendsto_rpow_mul_abs_log_pow (a : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => r ^ s * |Real.log r| ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (a : ℝ) (neg_neg_of_pos hs)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Real.rpow_natCast, Real.rpow_neg hr.le, div_inv_eq_mul, mul_comm]

/-- The radial boundary factor tends to zero, including logarithmic power zero. -/
theorem tendsto_radius_mul_abs_log_pow (a : ℕ) :
    Tendsto (fun r : ℝ => r * |Real.log r| ^ a) (𝓝[>] 0) (𝓝 0) := by
  simpa only [Real.rpow_one] using tendsto_rpow_mul_abs_log_pow a (s := 1) zero_lt_one

/-- Near zero the fixed logarithmic power is bounded by one square-root pole. -/
theorem exists_log_power_bound (a : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → |Real.log r| ^ a ≤ r ^ (-(1 / 2 : ℝ)) := by
  have h := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (a : ℝ)
    (by norm_num : (-(1 / 2 : ℝ)) < 0)
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] 0, |Real.log r| ^ a ≤ r ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [h.bound zero_lt_one, self_mem_nhdsWithin] with r hr hrpos
    simpa only [Real.rpow_natCast, one_mul,
      Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) a),
      Real.norm_of_nonneg (Real.rpow_nonneg hrpos.le _)] using hr
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
  exact ⟨δ, hδ, fun r hr hrδ => hδbound ⟨hr, hrδ⟩⟩

/-- The nonnegative density of a logarithmic pole, with the library's harmless
value zero at the origin. -/
def density (a : ℕ) (z : ℂ) : ℝ := |Real.log ‖z‖| ^ a / ‖z‖

@[simp] theorem density_zero (a : ℕ) : density a 0 = 0 := by simp [density]

theorem density_nonneg (a : ℕ) (z : ℂ) : 0 ≤ density a z := by
  exact div_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)

@[fun_prop] theorem measurable_density (a : ℕ) : Measurable (density a) := by
  have hlog : Measurable (fun z : ℂ => Real.log ‖z‖) := Real.measurable_log.comp measurable_norm
  change Measurable (fun z : ℂ => |Real.log ‖z‖| ^ a / ‖z‖)
  convert (hlog.norm.pow_const a).div (measurable_norm : Measurable (norm : ℂ → ℝ)) using 1
  funext z
  simp only [Pi.div_apply, Real.norm_eq_abs]

theorem continuousAt_density (a : ℕ) {z : ℂ} (hz : z ≠ 0) : ContinuousAt (density a) z := by
  have hn : ContinuousAt (fun z : ℂ => ‖z‖) z := continuous_norm.continuousAt
  exact ((hn.log (norm_ne_zero_iff.mpr hz)).abs.pow a).div hn (norm_ne_zero_iff.mpr hz)

theorem continuousOn_density_punctured (a : ℕ) : ContinuousOn (density a) ({0}ᶜ : Set ℂ) := by
  intro z hz
  exact (continuousAt_density a hz).continuousWithinAt

/-- A true integrable neighborhood of the pole, by comparison with ‖z‖^(-3/2).
The comparison exponent is strictly below the real dimension 2. -/
theorem exists_integrableOn_ball (a : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ IntegrableOn (density a) (ball (0 : ℂ) δ) volume := by
  obtain ⟨δ, hδ, hbound⟩ := exists_log_power_bound a
  refine ⟨δ, hδ, ?_⟩
  apply MeasureTheory.integrableOn_ball_of_norm_le_rpow
    (E := ℂ) (F := ℝ) (μ := volume) (C := 1) (α := (3 / 2 : ℝ))
    (by simp [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) _ (measurable_density a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
  rw [Real.norm_of_nonneg (density_nonneg a z), one_mul]
  by_cases hz0 : z = 0
  · rw [hz0, density_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hrδ : ‖z‖ < δ := by simpa only [mem_ball, dist_zero_right] using hz
  calc
    density a z ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) / ‖z‖ :=
      div_le_div_of_nonneg_right (hbound ‖z‖ hr hrδ) hr.le
    _ = ‖z‖ ^ (-(1 / 2 : ℝ)) / ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = ‖z‖ ^ (-(1 / 2 : ℝ) - 1) := (Real.rpow_sub hr _ _).symm
    _ = ‖z‖ ^ (-(3 / 2 : ℝ)) := by
      congr 1
      ring

/-- The assigned value at zero and the actual punctured density together
form a locally Lebesgue-integrable function on the whole complex plane. -/
theorem locallyIntegrable_density (a : ℕ) : LocallyIntegrable (density a) (volume : Measure ℂ) := by
  intro z
  by_cases hz : z = 0
  · subst z
    obtain ⟨δ, hδ, hInt⟩ := exists_integrableOn_ball a
    exact ⟨ball 0 δ, ball_mem_nhds 0 hδ, hInt⟩
  have hInt := (continuousOn_density_punctured a).integrableAt_nhdsWithin
    isClosed_singleton.isOpen_compl.measurableSet hz (μ := volume)
  rwa [nhdsWithin_eq_nhds.mpr (isClosed_singleton.isOpen_compl.mem_nhds hz)] at hInt

/-- Absolute area-integrability on every bounded disk. -/
theorem integrableOn_density_ball (a : ℕ) (ε : ℝ) :
    IntegrableOn (density a) (ball (0 : ℂ) ε) volume :=
  ((locallyIntegrable_density a).integrableOn_isCompact (isCompact_closedBall (0 : ℂ) ε)).mono_set
    ball_subset_closedBall

/-- The requested genuine logarithmic-pole estimate on a punctured disk.
No value assigned to the density at zero affects this statement. -/
theorem integrableOn_log_pole_puncturedDisc (a : ℕ) (ε : ℝ) :
    IntegrableOn (fun z : ℂ => |Real.log ‖z‖| ^ a / ‖z‖)
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ε} volume := by
  apply (integrableOn_density_ball a ε).mono_set
  intro z hz
  simpa only [mem_ball, dist_zero_right] using hz.2

/-- The integral of the nonnegative pole density is genuinely finite. -/
theorem lintegral_log_pole_puncturedDisc_lt_top (a : ℕ) (ε : ℝ) :
    (∫⁻ z : ℂ in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ε},
      ENNReal.ofReal (|Real.log ‖z‖| ^ a / ‖z‖)) < ⊤ :=
  (integrableOn_log_pole_puncturedDisc a ε).setLIntegral_lt_top

/-- Actual Cartesian coefficients of log-polynomial multiples of the radial
one-form are Lebesgue integrable on every bounded disk. -/
theorem integrableOn_log_pow_mul_logRadiusForm (a : ℕ) (ε : ℝ) (v : Fin 1 → ℂ) :
    IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ a * logRadiusForm z v)
      (ball (0 : ℂ) ε) volume := by
  have hlog : Measurable (fun z : ℂ => Real.log ‖z‖) := Real.measurable_log.comp measurable_norm
  have hform : Measurable (fun z : ℂ => logRadiusForm z v) := by
    simp only [logRadiusForm_apply]
    fun_prop
  apply ((integrableOn_density_ball a ε).const_mul ‖v 0‖).mono'
    ((hlog.pow_const a).mul hform).aestronglyMeasurable.restrict
  apply Filter.Eventually.of_forall
  intro z
  change ‖(Real.log ‖z‖) ^ a * logRadiusForm z v‖ ≤ ‖v 0‖ * density a z
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |Real.log ‖z‖| ^ a * |logRadiusForm z v| ≤
        |Real.log ‖z‖| ^ a * (‖v 0‖ / ‖z‖) :=
      mul_le_mul_of_nonneg_left (abs_logRadiusForm_le z v) (pow_nonneg (abs_nonneg _) _)
    _ = ‖v 0‖ * density a z := by simp only [density, div_eq_mul_inv]; ring

/-- The same L¹ coefficient estimate for the actual angular one-form.
This does not assert a distributional closedness statement at the pole. -/
theorem integrableOn_log_pow_mul_angularForm (a : ℕ) (ε : ℝ) (v : Fin 1 → ℂ) :
    IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ a * angularForm z v)
      (ball (0 : ℂ) ε) volume := by
  have hlog : Measurable (fun z : ℂ => Real.log ‖z‖) := Real.measurable_log.comp measurable_norm
  have hform : Measurable (fun z : ℂ => angularForm z v) := by
    simp only [angularForm_apply]
    fun_prop
  apply ((integrableOn_density_ball a ε).const_mul ‖v 0‖).mono'
    ((hlog.pow_const a).mul hform).aestronglyMeasurable.restrict
  apply Filter.Eventually.of_forall
  intro z
  change ‖(Real.log ‖z‖) ^ a * angularForm z v‖ ≤ ‖v 0‖ * density a z
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |Real.log ‖z‖| ^ a * |angularForm z v| ≤
        |Real.log ‖z‖| ^ a * (‖v 0‖ / ‖z‖) :=
      mul_le_mul_of_nonneg_left (abs_angularForm_le z v) (pow_nonneg (abs_nonneg _) _)
    _ = ‖v 0‖ * density a z := by simp only [density, div_eq_mul_inv]; ring

end EnvelopingIsomorphism.Deformation.Kontsevich.LogPole
