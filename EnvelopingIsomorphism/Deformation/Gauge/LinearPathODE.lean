import EnvelopingIsomorphism.Deformation.Gauge.TaylorPath

/-! Uniqueness for actual module-valued complete polynomial paths with positive operator velocity. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- A polynomial-coefficient operator path acts by the two finite convolutions. -/
def pathOperator (L : ModulePath k (Module.End k V)) : ModulePath k V →ₗ[PowerSeries k] ModulePath k V :=
  extendBilinear
    (PolynomialModuleCalculus.extendBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)) L

@[simp] theorem coeffV_pathOperator (L : ModulePath k (Module.End k V))
    (b : ModulePath k V) (n : ℕ) :
    coeffV n (pathOperator L b) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      PolynomialModuleCalculus.extendBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
        (coeffV ij.1 L) (coeffV ij.2 b) := rfl

variable [Algebra ℚ k]

/-- Every coefficient of the path equation is determined by preceding t-coefficients
and by its value at s=0. The coefficient module need not be a ring. -/
theorem path_unique {L : ModulePath k (Module.End k V)} (hL : coeffV 0 L = 0)
    {b c : ModulePath k V}
    (hb : PolynomialModuleCalculus.seriesDerivative b = pathOperator L b)
    (hc : PolynomialModuleCalculus.seriesDerivative c = pathOperator L c)
    (h0 : PolynomialModuleCalculus.seriesEval 0 b = PolynomialModuleCalculus.seriesEval 0 c) : b = c := by
  apply PowerSeriesModule.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply PolynomialModuleCalculus.ext_of_derivative_eval_zero
    · have hbn := congrArg (coeffV n) hb
      have hcn := congrArg (coeffV n) hc
      rw [PolynomialModuleCalculus.coeff_seriesDerivative, coeffV_pathOperator] at hbn hcn
      rw [hbn, hcn]
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ hij
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hi : i = 0
      · subst i
        rw [hL, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
      · rw [ih j (by omega)]
    · have he := congrArg (coeffV n) h0
      simpa only [PolynomialModuleCalculus.coeff_seriesEval] using he

end EnvelopingIsomorphism.Deformation.Gauge
