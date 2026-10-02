import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat

/-! Polynomial integration with zero constant term over a possibly
noncommutative rational algebra. No analytic integration is used. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PolynomialIntegral

open Polynomial

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- Integrate each monomial, retaining zero integration constant. -/
def integral : Polynomial R →ₗ[ℚ] Polynomial R :=
  Polynomial.lsum fun n ↦ ((n + 1 : ℚ)⁻¹) • (Polynomial.monomial (n + 1)).restrictScalars ℚ

theorem integral_apply (p : Polynomial R) :
    integral p = p.sum (fun n a ↦ ((n + 1 : ℚ)⁻¹) • Polynomial.monomial (n + 1) a) := rfl

@[simp] theorem integral_monomial (n : ℕ) (a : R) :
    integral (Polynomial.monomial n a) = ((n + 1 : ℚ)⁻¹) • Polynomial.monomial (n + 1) a := by
  rw [integral_apply, Polynomial.sum_monomial_index]
  simp

private theorem inverse_smul_mul_nat_succ (a : R) (n : ℕ) :
    ((n + 1 : ℚ)⁻¹) • (a * (n + 1 : R)) = a := by
  have hnat : a * (n + 1 : R) = (n + 1 : ℚ) • a := by
    rw [← Nat.cast_succ, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ]
    simp
  rw [hnat, inv_smul_smul₀ (by positivity)]

/-- Differentiation undoes this purely algebraic polynomial integral. -/
@[simp] theorem derivative_integral (p : Polynomial R) :
    Polynomial.derivative (integral p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    rw [integral_monomial, Polynomial.derivative_smul, Polynomial.derivative_monomial_succ]
    rw [← map_rat_smul, inverse_smul_mul_nat_succ]

/-- The integration constant is always zero. -/
@[simp] theorem constantCoeff_integral (p : Polynomial R) : (integral p).coeff 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a => simp [integral_monomial, Polynomial.coeff_monomial]

/-- A polynomial over a rational algebra is determined by its derivative and
constant coefficient, including for noncommutative coefficient rings. -/
theorem ext_of_derivative_coeff_zero {p q : Polynomial R}
    (hd : p.derivative = q.derivative) (hc : p.coeff 0 = q.coeff 0) : p = q := by
  ext n
  cases n with
  | zero => exact hc
  | succ n =>
    have h := congrArg (fun r : R ↦ ((n + 1 : ℚ)⁻¹) • r)
      (congrArg (fun P : Polynomial R ↦ P.coeff n) hd)
    simpa only [Polynomial.coeff_derivative, inverse_smul_mul_nat_succ] using h

/-- The zero-constant integral is uniquely characterized by its derivative. -/
theorem integral_unique {p q : Polynomial R} (hd : q.derivative = p)
    (hc : q.coeff 0 = 0) : q = integral p :=
  ext_of_derivative_coeff_zero (hd.trans (derivative_integral p).symm)
    (hc.trans (constantCoeff_integral p).symm)

end EnvelopingIsomorphism.FormalSeries.PolynomialIntegral
