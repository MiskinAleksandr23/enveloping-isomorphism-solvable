import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The radial logarithmic form is the genuine differential of log |z|,
without any choice of complex logarithm branch. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

/-- The radial counterpart of `angularLinearCoefficient`. -/
def radialLinearCoefficient : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ) Complex.reCLM).comp
    (ContinuousLinearMap.mul ℝ ℂ)

def radialCoefficient : ℂ →L[ℝ] ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp radialLinearCoefficient

@[simp] theorem radialLinearCoefficient_apply (a v : ℂ) :
    radialLinearCoefficient a v = (a * v).re := rfl

@[simp] theorem radialCoefficient_apply (a : ℂ) (v : Fin 1 → ℂ) :
    radialCoefficient a v = (a * v 0).re := rfl

def logRadiusForm (z : ℂ) : ℂ [⋀^Fin 1]→L[ℝ] ℝ := radialCoefficient z⁻¹

@[simp] theorem logRadiusForm_apply (z : ℂ) (v : Fin 1 → ℂ) :
    logRadiusForm z v = (v 0 / z).re := by
  simp [logRadiusForm, div_eq_mul_inv, mul_comm]

theorem contDiffAt_logRadiusForm {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ⊤ logRadiusForm z :=
  radialCoefficient.contDiff.contDiffAt.comp z (contDiffAt_id.inv hz)

theorem hasFDerivAt_logRadiusForm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt logRadiusForm
      (radialCoefficient.comp (-((ContinuousLinearMap.mulLeftRight ℝ ℂ) z⁻¹) z⁻¹)) z :=
  radialCoefficient.hasFDerivAt.comp z (hasFDerivAt_inv' hz)

theorem extDeriv_logRadiusForm {z : ℂ} (hz : z ≠ 0) : extDeriv logRadiusForm z = 0 := by
  rw [extDeriv, (hasFDerivAt_logRadiusForm hz).fderiv]
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    radialCoefficient, radialLinearCoefficient, ContinuousLinearMap.mulLeftRight, Fin.removeNth,
    Complex.mul_im, Complex.mul_re]
  ring

/-- The real logarithm of the radius has derivative Re(dz/z) at every nonzero point. -/
theorem hasFDerivAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ Real.log ‖w‖) (radialLinearCoefficient z⁻¹) z := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.log hn).const_smul (1 / 2 : ℝ)
  have he : (1 / 2 : ℝ) • ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) =
      radialLinearCoefficient z⁻¹ := by
    ext v
    simp only [two_smul, smul_apply, add_apply, smul_eq_mul, innerSL_apply_apply,
      real_inner_eq_re_inner ℂ, RCLike.inner_apply, radialLinearCoefficient_apply]
    change (1 / 2 : ℝ) * ((‖z‖ ^ 2)⁻¹ *
      ((v * (starRingEnd ℂ) z).re + (v * (starRingEnd ℂ) z).re)) =
      (z⁻¹ * v).re
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_eq_norm_sq]
    ring
  rw [he] at h
  have hfun : ((1 / 2 : ℝ) • fun w : ℂ ↦ Real.log (‖w‖ ^ 2)) =
      (fun w : ℂ ↦ Real.log ‖w‖) := by
    funext w
    simp [Real.log_pow, smul_eq_mul]
  rw [hfun] at h
  exact h

theorem fderiv_log_norm {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun w : ℂ ↦ Real.log ‖w‖) z = radialLinearCoefficient z⁻¹ :=
  (hasFDerivAt_log_norm hz).fderiv

/-- The logarithmic interpretation is preserved by actual differentiable pullback. -/
theorem hasFDerivAt_log_norm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {D : E →L[ℝ] ℂ} {x : E} (hf : HasFDerivAt f D x) (hne : f x ≠ 0) :
    HasFDerivAt (fun y ↦ Real.log ‖f y‖) ((radialLinearCoefficient (f x)⁻¹).comp D) x :=
  (hasFDerivAt_log_norm hne).comp x hf

theorem logRadiusForm_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {D : E →L[ℝ] ℂ} {x : E} (hf : HasFDerivAt f D x) (hne : f x ≠ 0) :
    (logRadiusForm (f x)).compContinuousLinearMap D =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
        (fderiv ℝ (fun y ↦ Real.log ‖f y‖) x) := by
  rw [(hasFDerivAt_log_norm_comp hf hne).fderiv]
  ext v
  rfl

/-- The pointwise logarithmic pole bound used in local integrability estimates. -/
theorem abs_logRadiusForm_le (z : ℂ) (v : Fin 1 → ℂ) :
    |logRadiusForm z v| ≤ ‖v 0‖ / ‖z‖ := by
  rw [logRadiusForm_apply, ← norm_div]
  exact Complex.abs_re_le_norm _

theorem abs_angularForm_le (z : ℂ) (v : Fin 1 → ℂ) :
    |angularForm z v| ≤ ‖v 0‖ / ‖z‖ := by
  rw [angularForm_apply, ← norm_div]
  exact Complex.abs_im_le_norm _

end EnvelopingIsomorphism.Deformation.Kontsevich
