import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Exact angular-form normalization on the real-angle parameter of the circle. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

set_option backward.isDefEq.respectTransparency false

/-- The complex representative of the standard positive real-angle circle parameter. -/
def circleParameter (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

theorem circleParameter_eq (θ : ℝ) : circleParameter θ = (Circle.exp θ : ℂ) := by
  simp only [circleParameter, Circle.coe_exp, mul_comm Complex.I]

theorem circleParameter_ne_zero (θ : ℝ) : circleParameter θ ≠ 0 := Complex.exp_ne_zero _

theorem contDiff_circleParameter : ContDiff ℝ ⊤ circleParameter :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

def circleParameterTangent (θ : ℝ) : ℝ →L[ℝ] ℂ :=
  (circleParameter θ * Complex.I) • Complex.ofRealCLM

@[simp] theorem circleParameterTangent_apply (θ v : ℝ) :
    circleParameterTangent θ v = circleParameter θ * Complex.I * (v : ℂ) := rfl

theorem hasFDerivAt_circleParameter (θ : ℝ) :
    HasFDerivAt circleParameter (circleParameterTangent θ) θ := by
  have h : HasFDerivAt (fun t : ℝ ↦ Complex.I * (t : ℂ))
      (Complex.I • Complex.ofRealCLM) θ :=
    Complex.ofRealCLM.hasFDerivAt.const_smul Complex.I
  unfold circleParameterTangent circleParameter
  simpa only [smul_smul] using h.cexp

/-- Pulling darg back by the positive angular parameter gives +dθ exactly. -/
theorem angularForm_circleParameter (θ : ℝ) :
    (angularForm (circleParameter θ)).compContinuousLinearMap (circleParameterTangent θ) =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ) := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  change (circleParameterTangent θ (v 0) / circleParameter θ).im = v 0
  rw [circleParameterTangent_apply]
  have heq : (circleParameter θ * Complex.I * ((v 0 : ℝ) : ℂ)) / circleParameter θ =
      Complex.I * ((v 0 : ℝ) : ℂ) := by
    rw [mul_assoc, mul_div_cancel_left₀ _ (circleParameter_ne_zero θ)]
  rw [heq]
  simp

theorem angularForm_circleExp_fderiv (θ : ℝ) :
    (angularForm (Circle.exp θ : ℂ)).compContinuousLinearMap
        (fderiv ℝ (fun t : ℝ ↦ (Circle.exp t : ℂ)) θ) =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ) := by
  have heq : (fun t : ℝ ↦ (Circle.exp t : ℂ)) = circleParameter :=
    funext (fun t ↦ (circleParameter_eq t).symm)
  rw [heq, (hasFDerivAt_circleParameter θ).fderiv]
  rw [← circleParameter_eq θ]
  exact angularForm_circleParameter θ

end EnvelopingIsomorphism.Deformation.Kontsevich
