import EnvelopingIsomorphism.Deformation.Kontsevich.CircleAngleForm
import EnvelopingIsomorphism.Deformation.Kontsevich.LogPoleEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Vanishing logarithmic boundary integrals on shrinking circles

The integrand is the actual evaluation of a continuous real one-form on the
derivative of `θ ↦ r * exp(I * θ)`. The derivative contributes the small factor
`r`; fixed logarithmic powers cannot cancel it. The radial logarithmic form has
identically zero pullback on these circles.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogCircle

set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set Metric
open scoped Topology

/-- Genuine positive-angle parameterization of the circle of radius `|r|`. -/
def shrinkingCircle (r θ : ℝ) : ℂ := (r : ℂ) * circleParameter θ

def shrinkingCircleTangent (r θ : ℝ) : ℝ →L[ℝ] ℂ :=
  (shrinkingCircle r θ * Complex.I) • Complex.ofRealCLM

@[simp] theorem shrinkingCircleTangent_apply (r θ v : ℝ) :
    shrinkingCircleTangent r θ v = shrinkingCircle r θ * Complex.I * (v : ℂ) := rfl

theorem hasFDerivAt_shrinkingCircle (r θ : ℝ) :
    HasFDerivAt (shrinkingCircle r) (shrinkingCircleTangent r θ) θ := by
  have h := (hasFDerivAt_circleParameter θ).const_smul (r : ℂ)
  have heq : (r : ℂ) • circleParameter = shrinkingCircle r := rfl
  rw [heq] at h
  simpa only [shrinkingCircle, shrinkingCircleTangent, circleParameterTangent,
    smul_smul, mul_assoc] using h

@[fun_prop] theorem continuous_shrinkingCircle (r : ℝ) : Continuous (shrinkingCircle r) :=
  continuous_const.mul contDiff_circleParameter.continuous

@[simp] theorem norm_circleParameter (θ : ℝ) : ‖circleParameter θ‖ = 1 := by
  rw [circleParameter_eq]
  simp

@[simp] theorem norm_shrinkingCircle (r θ : ℝ) : ‖shrinkingCircle r θ‖ = |r| := by
  simp [shrinkingCircle]

theorem norm_shrinkingCircle_of_nonneg {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖shrinkingCircle r θ‖ = r := by rw [norm_shrinkingCircle, abs_of_nonneg hr]

@[simp] theorem norm_shrinkingCircleTangent_one (r θ : ℝ) :
    ‖shrinkingCircleTangent r θ 1‖ = |r| := by
  simp [shrinkingCircleTangent_apply]

theorem log_norm_shrinkingCircle {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    Real.log ‖shrinkingCircle r θ‖ = Real.log r := by
  rw [norm_shrinkingCircle_of_nonneg hr]

@[fun_prop] theorem continuous_shrinkingCircle_velocity (r : ℝ) :
    Continuous (fun θ => shrinkingCircleTangent r θ 1) := by
  simp only [shrinkingCircleTangent_apply, Complex.ofReal_one, mul_one]
  exact (continuous_shrinkingCircle r).mul continuous_const

/-- Actual pullback of the one-form, evaluated on the positive angular unit tangent. -/
def pullback (η : ℂ → ℂ →L[ℝ] ℝ) (r θ : ℝ) : ℝ :=
  η (shrinkingCircle r θ) (shrinkingCircleTangent r θ 1)

theorem pullback_eq_fderiv (η : ℂ → ℂ →L[ℝ] ℝ) (r θ : ℝ) :
    pullback η r θ = η (shrinkingCircle r θ) (fderiv ℝ (shrinkingCircle r) θ 1) := by
  rw [(hasFDerivAt_shrinkingCircle r θ).fderiv]
  rfl

def logIntegrand (a : ℕ) (η : ℂ → ℂ →L[ℝ] ℝ) (r θ : ℝ) : ℝ :=
  (Real.log ‖shrinkingCircle r θ‖) ^ a * pullback η r θ

/-- The actual oriented boundary integral over one full positive turn. -/
def boundaryIntegral (a : ℕ) (η : ℂ → ℂ →L[ℝ] ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), logIntegrand a η r θ

theorem norm_pullback_le {η : ℂ → ℂ →L[ℝ] ℝ} {C r : ℝ} (hr : 0 ≤ r)
    (hη : ∀ θ : ℝ, ‖η (shrinkingCircle r θ)‖ ≤ C) (θ : ℝ) :
    ‖pullback η r θ‖ ≤ C * r := by
  calc
    ‖pullback η r θ‖ ≤ ‖η (shrinkingCircle r θ)‖ * ‖shrinkingCircleTangent r θ 1‖ :=
      (η (shrinkingCircle r θ)).le_opNorm _
    _ = ‖η (shrinkingCircle r θ)‖ * r := by
      rw [norm_shrinkingCircleTangent_one, abs_of_nonneg hr]
    _ ≤ C * r := mul_le_mul_of_nonneg_right (hη θ) hr

theorem norm_logIntegrand_le (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ} {C r : ℝ} (hr : 0 ≤ r)
    (hη : ∀ θ : ℝ, ‖η (shrinkingCircle r θ)‖ ≤ C) (θ : ℝ) :
    ‖logIntegrand a η r θ‖ ≤ |Real.log r| ^ a * C * r := by
  rw [logIntegrand, norm_mul, norm_pow, Real.norm_eq_abs, log_norm_shrinkingCircle hr]
  calc
    |Real.log r| ^ a * ‖pullback η r θ‖ ≤ |Real.log r| ^ a * (C * r) :=
      mul_le_mul_of_nonneg_left (norm_pullback_le hr hη θ) (pow_nonneg (abs_nonneg _) _)
    _ = _ := by ring

/-- The true angular integral has the radius-logarithm bound, with its exact
circle length constant. This estimate does not require an integrability premise. -/
theorem norm_boundaryIntegral_le (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ} {C r : ℝ}
    (hr : 0 ≤ r) (hη : ∀ θ : ℝ, ‖η (shrinkingCircle r θ)‖ ≤ C) :
    ‖boundaryIntegral a η r‖ ≤ 2 * Real.pi * C * (r * |Real.log r| ^ a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (fun θ _ => norm_logIntegrand_le a hr hη θ)
  change ‖boundaryIntegral a η r‖ ≤ (|Real.log r| ^ a * C * r) * |2 * Real.pi - 0| at h
  calc
    ‖boundaryIntegral a η r‖ ≤ (|Real.log r| ^ a * C * r) * |2 * Real.pi - 0| := h
    _ = _ := by
      rw [sub_zero, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
      ring

theorem norm_boundaryIntegral_le_of_ball_bound (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {C R r : ℝ} (hη : ∀ z ∈ ball (0 : ℂ) R, ‖η z‖ ≤ C)
    (hr : 0 ≤ r) (hrR : r < R) :
    ‖boundaryIntegral a η r‖ ≤ 2 * Real.pi * C * (r * |Real.log r| ^ a) := by
  apply norm_boundaryIntegral_le a hr
  intro θ
  apply hη
  simpa only [mem_ball, dist_zero_right, norm_shrinkingCircle_of_nonneg hr] using hrR

/-- Local boundedness is enough for the no-residue limit of the actual integral. -/
theorem tendsto_boundaryIntegral_of_bound (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {C R : ℝ} (hR : 0 < R) (hη : ∀ z ∈ ball (0 : ℂ) R, ‖η z‖ ≤ C) :
    Tendsto (boundaryIntegral a η) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm'
    (show ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖boundaryIntegral a η r‖ ≤ 2 * Real.pi * C * (r * |Real.log r| ^ a) from ?_)
  · simpa only [mul_zero] using
      (LogPole.tendsto_radius_mul_abs_log_pow a).const_mul (2 * Real.pi * C)
  · filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    exact norm_boundaryIntegral_le_of_ball_bound a hη hr.1.le hr.2

/-- Continuity at the origin supplies an actual uniform operator-norm bound
on a positive-radius ball. -/
theorem exists_ball_bound_of_continuousAt {η : ℂ → ℂ →L[ℝ] ℝ}
    (hη : ContinuousAt η 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∀ z ∈ ball (0 : ℂ) R, ‖η z‖ ≤ C := by
  have hevent : ∀ᶠ z : ℂ in 𝓝 0, ‖η z‖ < ‖η 0‖ + 1 :=
    hη.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨R, hR, hb⟩ := Metric.mem_nhds_iff.mp hevent
  exact ⟨‖η 0‖ + 1, by positivity, R, hR, fun z hz => (hb hz).le⟩

theorem continuous_logIntegrand_of_continuousOn (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {R r : ℝ} (hη : ContinuousOn η (ball (0 : ℂ) R)) (hr : 0 ≤ r) (hrR : r < R) :
    Continuous (logIntegrand a η r) := by
  have hηc : Continuous (fun θ => η (shrinkingCircle r θ)) :=
    hη.comp_continuous (continuous_shrinkingCircle r) (fun θ => by
      simpa only [mem_ball, dist_zero_right, norm_shrinkingCircle_of_nonneg hr] using hrR)
  have hp : Continuous (pullback η r) := hηc.clm_apply (continuous_shrinkingCircle_velocity r)
  change Continuous (fun θ => (Real.log ‖shrinkingCircle r θ‖) ^ a * pullback η r θ)
  simp only [log_norm_shrinkingCircle hr]
  exact continuous_const.mul hp

/-- Actual integrability follows from continuity of the one-form on a ball
containing this circle. No integrability premise is imposed on the integral. -/
theorem intervalIntegrable_logIntegrand (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ} {R r : ℝ}
    (hη : ContinuousOn η (ball (0 : ℂ) R)) (hr : 0 ≤ r) (hrR : r < R) :
    IntervalIntegrable (logIntegrand a η r) volume 0 (2 * Real.pi) :=
  (continuous_logIntegrand_of_continuousOn a hη hr hrR).intervalIntegrable 0 (2 * Real.pi)

theorem eventually_intervalIntegrable_logIntegrand (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {R : ℝ} (hR : 0 < R) (hη : ContinuousOn η (ball (0 : ℂ) R)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, IntervalIntegrable (logIntegrand a η r) volume 0 (2 * Real.pi) := by
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact intervalIntegrable_logIntegrand a hη hr.1.le hr.2

/-- The actual one-form boundary integral tends to zero whenever the one-form
is continuous on a neighborhood of the origin. -/
theorem tendsto_boundaryIntegral_of_continuousOn (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {R : ℝ} (hR : 0 < R) (hη : ContinuousOn η (ball (0 : ℂ) R)) :
    Tendsto (boundaryIntegral a η) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, δ, hδ, hb⟩ := exists_ball_bound_of_continuousAt
    (hη.continuousAt (ball_mem_nhds (0 : ℂ) hR))
  exact tendsto_boundaryIntegral_of_bound a hδ hb

/-- A complete local no-residue statement: the genuine angular integrals are
integrable for all sufficiently small positive radii and converge to zero. -/
theorem noResidue_of_continuousOn (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {R : ℝ} (hR : 0 < R) (hη : ContinuousOn η (ball (0 : ℂ) R)) :
    (∀ᶠ r : ℝ in 𝓝[>] 0, IntervalIntegrable (logIntegrand a η r) volume 0 (2 * Real.pi)) ∧
      Tendsto (boundaryIntegral a η) (𝓝[>] 0) (𝓝 0) :=
  ⟨eventually_intervalIntegrable_logIntegrand a hR hη,
    tendsto_boundaryIntegral_of_continuousOn a hR hη⟩

/-- The same limit displayed directly as the genuine one-form pullback integral,
with the library derivative of the actual circle map. -/
theorem tendsto_integral_log_oneForm (a : ℕ) {η : ℂ → ℂ →L[ℝ] ℝ}
    {R : ℝ} (hR : 0 < R) (hη : ContinuousOn η (ball (0 : ℂ) R)) :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Real.log ‖shrinkingCircle r θ‖) ^ a *
        η (shrinkingCircle r θ) (fderiv ℝ (shrinkingCircle r) θ 1)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_boundaryIntegral_of_continuousOn a hR hη
  change Tendsto (fun r => boundaryIntegral a η r) (𝓝[>] 0) (𝓝 0) at h
  simpa only [boundaryIntegral, logIntegrand, pullback_eq_fderiv] using h

/-- The radial form has exactly zero angular pullback. This holds also at the
library's harmless zero-radius value, and in particular at every positive radius. -/
theorem logRadiusForm_shrinkingCircle (r θ : ℝ) :
    (logRadiusForm (shrinkingCircle r θ)).compContinuousLinearMap
      (shrinkingCircleTangent r θ) = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, logRadiusForm_apply]
  change (shrinkingCircleTangent r θ (v 0) / shrinkingCircle r θ).re = 0
  rw [shrinkingCircleTangent_apply]
  by_cases hz : shrinkingCircle r θ = 0
  · simp [hz]
  · rw [mul_assoc, mul_div_cancel_left₀ _ hz]
    simp

theorem logRadiusForm_shrinkingCircle_fderiv (r θ : ℝ) :
    (logRadiusForm (shrinkingCircle r θ)).compContinuousLinearMap
      (fderiv ℝ (shrinkingCircle r) θ) = 0 := by
  rw [(hasFDerivAt_shrinkingCircle r θ).fderiv]
  exact logRadiusForm_shrinkingCircle r θ

end EnvelopingIsomorphism.Deformation.Kontsevich.LogCircle
