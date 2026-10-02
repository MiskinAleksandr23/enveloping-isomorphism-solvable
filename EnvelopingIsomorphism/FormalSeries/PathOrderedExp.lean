import EnvelopingIsomorphism.FormalSeries.PolynomialIntegral
import EnvelopingIsomorphism.FormalSeries.Endomorphism

/-! Path-ordered exponentials in a complete positive formal filtration.

The path parameter s is polynomial in each fixed t-degree. The coefficients
may lie in a noncommutative rational algebra. Every integration and every sum
is finite at a fixed t-degree; no analytic topology or existence theorem is used.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PathOrderedExp

open PowerSeries

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- Polynomial dependence on s and complete formal dependence on t. -/
abbrev PathSeries (R : Type*) [Semiring R] := PowerSeries (Polynomial R)

/-- Differentiate in the polynomial path parameter, fixing the formal variable. -/
def parameterDerivative : PathSeries R →ₗ[ℚ] PathSeries R where
  toFun F := PowerSeries.mk fun n ↦ Polynomial.derivative (coeff n F)
  map_add' F G := by ext n; simp
  map_smul' c F := by ext n; simp

@[simp] theorem coeff_parameterDerivative (F : PathSeries R) (n : ℕ) :
    coeff n (parameterDerivative F) = Polynomial.derivative (coeff n F) := by
  simp [parameterDerivative]

@[simp] theorem parameterDerivative_one : parameterDerivative (1 : PathSeries R) = 0 := by
  ext n
  by_cases hn : n = 0 <;> simp [hn]

/-- The path derivative obeys the noncommutative Leibniz rule. -/
theorem parameterDerivative_mul (F G : PathSeries R) :
    parameterDerivative (F * G) = parameterDerivative F * G + F * parameterDerivative G := by
  ext n
  simp only [coeff_parameterDerivative, PowerSeries.coeff_mul, map_add,
    Polynomial.derivative_sum, Polynomial.derivative_mul, Finset.sum_add_distrib]

/-- Evaluation at s=0. This is a ring homomorphism for noncommutative R. -/
def atZero : PathSeries R →+* PowerSeries R := PowerSeries.map Polynomial.constantCoeff

@[simp] theorem coeff_atZero (F : PathSeries R) (n : ℕ) :
    coeff n (atZero F) = (coeff n F).coeff 0 := rfl

/-- Evaluation at a rational path parameter, whose image is central in R. -/
def evaluation (s : ℚ) : PathSeries R →+* PowerSeries R :=
  PowerSeries.map (Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap ℚ R s)
    (fun a ↦ (Algebra.commutes s a).symm))

@[simp] theorem coeff_evaluation (s : ℚ) (F : PathSeries R) (n : ℕ) :
    coeff n (evaluation s F) =
      (coeff n F).eval₂ (RingHom.id R) (algebraMap ℚ R s) := rfl

theorem evaluation_zero (F : PathSeries R) : evaluation 0 F = atZero F := by
  ext n
  simp [Polynomial.eval₂_at_zero]

/-- Recursive coefficients of the left path-ordered exponential. The term
`X_(i+1) * G_(n-i)` retains the noncommutative multiplication order. -/
def solutionCoeff (X : PathSeries R) : ℕ → Polynomial R
  | 0 => 1
  | n + 1 => PolynomialIntegral.integral
      (∑ i ∈ Finset.range (n + 1), coeff (i + 1) X * solutionCoeff X (n - i))
termination_by n => n
decreasing_by omega

@[simp] theorem solutionCoeff_zero (X : PathSeries R) : solutionCoeff X 0 = 1 := by
  rw [solutionCoeff]

theorem solutionCoeff_succ (X : PathSeries R) (n : ℕ) :
    solutionCoeff X (n + 1) = PolynomialIntegral.integral
      (∑ i ∈ Finset.range (n + 1), coeff (i + 1) X * solutionCoeff X (n - i)) := by
  rw [solutionCoeff]

/-- The complete path-ordered exponential defined by the finite recursions. -/
def solution (X : PathSeries R) : PathSeries R := PowerSeries.mk (solutionCoeff X)

@[simp] theorem coeff_solution (X : PathSeries R) (n : ℕ) :
    coeff n (solution X) = solutionCoeff X n := PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_solution (X : PathSeries R) : constantCoeff (solution X) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_solution, solutionCoeff_zero]

/-- The complete solution starts at the identity for s=0. -/
@[simp] theorem atZero_solution (X : PathSeries R) : atZero (solution X) = 1 := by
  ext n
  rw [coeff_atZero, coeff_solution]
  cases n with
  | zero => simp
  | succ n => simp [solutionCoeff_succ]

@[simp] theorem evaluation_zero_solution (X : PathSeries R) : evaluation 0 (solution X) = 1 := by
  rw [evaluation_zero, atZero_solution]

/-- The constructed series satisfies the actual noncommutative differential
equation dG/ds = X G. Positivity in t is the only convergence hypothesis. -/
theorem solution_differential (X : PathSeries R) (hX : constantCoeff X = 0) :
    parameterDerivative (solution X) = X * solution X := by
  have hX₀ : coeff 0 X = 0 := by simpa only [coeff_zero_eq_constantCoeff] using hX
  ext n
  rw [coeff_parameterDerivative, coeff_solution]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, hX]
  | succ n =>
    rw [solutionCoeff_succ, PolynomialIntegral.derivative_integral, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_succ]
    simp only [hX₀, zero_mul, zero_add,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_solution]

/-- Solutions with the same initial value are equal. The proof only compares
previous t-coefficients and polynomial derivatives, so it is fully algebraic. -/
theorem eq_of_differential_initial {X F G : PathSeries R} (hX : constantCoeff X = 0)
    (hF : parameterDerivative F = X * F) (hG : parameterDerivative G = X * G)
    (h₀ : atZero F = atZero G) : F = G := by
  have hX₀ : coeff 0 X = 0 := by simpa only [coeff_zero_eq_constantCoeff] using hX
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply PolynomialIntegral.ext_of_derivative_coeff_zero
    · have hFn := congrArg (coeff n) hF
      have hGn := congrArg (coeff n) hG
      rw [coeff_parameterDerivative] at hFn hGn
      rw [hFn, hGn, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ hij
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hi : i = 0
      · simp [hi, hX₀]
      · rw [ih j (by omega)]
    · have h := congrArg (coeff n) h₀
      simpa only [coeff_atZero] using h

theorem solution_unique (X : PathSeries R) (hX : constantCoeff X = 0)
    (G : PathSeries R) (hG : parameterDerivative G = X * G) (hG₀ : atZero G = 1) :
    G = solution X :=
  eq_of_differential_initial hX hG (solution_differential X hX)
    (hG₀.trans (atZero_solution X).symm)

/-- The inverse path has the reverse right differential equation, with the
sign needed in genuine gauge transport. -/
theorem inverse_differential (X : PathSeries R) (hX : constantCoeff X = 0) :
    parameterDerivative (inverseOne (solution X)) = -inverseOne (solution X) * X := by
  have h := congrArg parameterDerivative (inverseOne_mul (constantCoeff_solution X))
  rw [parameterDerivative_mul, parameterDerivative_one, solution_differential X hX] at h
  have h' := congrArg (fun F : PathSeries R ↦ F * inverseOne (solution X)) h
  simp only [add_mul, mul_assoc, mul_inverseOne (constantCoeff_solution X),
    mul_one, zero_mul] at h'
  have heq := eq_neg_of_add_eq_zero_left h'
  simpa only [neg_mul] using heq

/-- The prescribed velocity is recovered from the actual unit path. -/
theorem logarithmicDerivative (X : PathSeries R) (hX : constantCoeff X = 0) :
    parameterDerivative (solution X) * inverseOne (solution X) = X := by
  rw [solution_differential X hX, mul_assoc, mul_inverseOne (constantCoeff_solution X), mul_one]

/-- Existence and uniqueness of a complete polynomial-in-s solution. -/
theorem existsUnique_solution (X : PathSeries R) (hX : constantCoeff X = 0) :
    ∃! G : PathSeries R, atZero G = 1 ∧ parameterDerivative G = X * G := by
  refine ⟨solution X, ⟨atZero_solution X, solution_differential X hX⟩, ?_⟩
  rintro G ⟨hG₀, hG⟩
  exact solution_unique X hX G hG hG₀

/-- The whole path lies in the actual unit group `1 + t R[s][[t]]`. -/
def pathUnit (X : PathSeries R) : (PathSeries R)ˣ :=
  unitOfConstantOne (solution X) (constantCoeff_solution X)

@[simp] theorem coe_pathUnit (X : PathSeries R) : (pathUnit X : PathSeries R) = solution X := rfl

/-- The genuine gauge element at s=1, together with its inverse. -/
def endpointUnit (X : PathSeries R) : (PowerSeries R)ˣ :=
  Units.map (evaluation (R := R) 1).toMonoidHom (pathUnit X)

@[simp] theorem coe_endpointUnit (X : PathSeries R) :
    (endpointUnit X : PowerSeries R) = evaluation 1 (solution X) := rfl

@[simp] theorem coe_endpointUnit_inv (X : PathSeries R) :
    (↑((endpointUnit X)⁻¹) : PowerSeries R) = evaluation 1 (inverseOne (solution X)) := rfl

theorem isUnit_endpoint (X : PathSeries R) : IsUnit (evaluation 1 (solution X)) :=
  (endpointUnit X).isUnit

@[simp] theorem constantCoeff_endpoint (X : PathSeries R) :
    constantCoeff (evaluation 1 (solution X)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_evaluation, coeff_solution, solutionCoeff_zero]
  simp

end EnvelopingIsomorphism.FormalSeries.PathOrderedExp
