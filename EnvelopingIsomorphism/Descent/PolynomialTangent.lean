import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring

/-! Differentiating polynomial families of Lie morphisms using their first coefficient. -/

namespace EnvelopingIsomorphism.Descent

open Finset Polynomial
open scoped BigOperators

universe u v w
variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {ι : Type w}

/-- The coefficient of an endomorphism-valued polynomial given as a finite scalar sum. -/
def operatorCoeff (s : Finset ι) (p : ι → k[X]) (T : ι → Module.End k L) (n : ℕ) :
    Module.End k L :=
  ∑ i ∈ s, (p i).coeff n • T i

private theorem scalar_coeff (s : Finset ι) (p : ι → k[X]) (T : ι → Module.End k L)
    (φ : Module.Dual k L) (x : L) (n : ℕ) :
    (∑ i ∈ s, C (φ (T i x)) * p i).coeff n = φ (operatorCoeff s p T n x) := by
  simp [operatorCoeff, coeff_C_mul, map_sum, mul_comm]

private theorem scalar_eval (s : Finset ι) (p : ι → k[X]) (T : ι → Module.End k L)
    (φ : Module.Dual k L) (x : L) (a : k) :
    (∑ i ∈ s, C (φ (T i x)) * p i).eval a =
      φ ((∑ i ∈ s, (p i).eval a • T i) x) := by
  simp [eval_finsetSum, map_sum, mul_comm]

private theorem bracket_coeff_one (s : Finset ι) (p : ι → k[X])
    (T : ι → Module.End k L) (φ : Module.Dual k L) (x y : L) :
    (∑ i ∈ s, ∑ j ∈ s, C (φ ⁅T i x, T j y⁆) * (p i * p j)).coeff 1 =
      φ ⁅operatorCoeff s p T 0 x, operatorCoeff s p T 1 y⁆ +
        φ ⁅operatorCoeff s p T 1 x, operatorCoeff s p T 0 y⁆ := by
  simp only [finsetSum_coeff, coeff_C_mul]
  simp only [mul_coeff_one, mul_add, sum_add_distrib,
    operatorCoeff, LinearMap.sum_apply, LinearMap.smul_apply, sum_lie_sum,
    smul_lie, lie_smul, map_sum, map_smul, smul_eq_mul]
  congr 1 <;> apply sum_congr rfl <;> intro i hi <;> apply sum_congr rfl <;> intro j hj <;> ring

private theorem bracket_eval (s : Finset ι) (p : ι → k[X])
    (T : ι → Module.End k L) (φ : Module.Dual k L) (x y : L) (a : k) :
    (∑ i ∈ s, ∑ j ∈ s, C (φ ⁅T i x, T j y⁆) * (p i * p j)).eval a =
      φ ⁅(∑ i ∈ s, (p i).eval a • T i) x, (∑ i ∈ s, (p i).eval a • T i) y⁆ := by
  simp only [eval_finsetSum, eval_mul, eval_C,
    LinearMap.sum_apply, LinearMap.smul_apply, sum_lie_sum,
    smul_lie, lie_smul, map_sum, map_smul, smul_eq_mul]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- A polynomial family preserving brackets at every natural parameter and equal to the
identity at zero has a Lie derivation as its first coefficient. -/
theorem operatorCoeff_one_leibniz
    (s : Finset ι) (p : ι → k[X]) (T : ι → Module.End k L)
    (hzero : operatorCoeff s p T 0 = 1)
    (hlie : ∀ (n : ℕ) (x y : L),
      (∑ i ∈ s, (p i).eval (n : k) • T i) ⁅x, y⁆ =
        ⁅(∑ i ∈ s, (p i).eval (n : k) • T i) x,
          (∑ i ∈ s, (p i).eval (n : k) • T i) y⁆)
    (x y : L) :
    operatorCoeff s p T 1 ⁅x, y⁆ =
      ⁅operatorCoeff s p T 1 x, y⁆ + ⁅x, operatorCoeff s p T 1 y⁆ := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro φ
  have hp : (∑ i ∈ s, C (φ (T i ⁅x, y⁆)) * p i) =
      ∑ i ∈ s, ∑ j ∈ s, C (φ ⁅T i x, T j y⁆) * (p i * p j) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := k))).mono
    rintro _ ⟨n, rfl⟩
    rw [Set.mem_setOf_eq, scalar_eval, bracket_eval]
    exact congrArg φ (hlie n x y)
  have hc := congrArg (fun q : k[X] => q.coeff 1) hp
  rw [scalar_coeff, bracket_coeff_one, hzero] at hc
  simpa only [map_sub, map_add, Module.End.one_apply, add_comm,
    sub_eq_zero] using hc

/-- The derivation obtained by taking the tangent of a finite polynomial family. -/
def polynomialTangent
    (s : Finset ι) (p : ι → k[X]) (T : ι → Module.End k L)
    (hzero : operatorCoeff s p T 0 = 1)
    (hlie : ∀ (n : ℕ) (x y : L),
      (∑ i ∈ s, (p i).eval (n : k) • T i) ⁅x, y⁆ =
        ⁅(∑ i ∈ s, (p i).eval (n : k) • T i) x,
          (∑ i ∈ s, (p i).eval (n : k) • T i) y⁆) : LieDerivation k L L where
  toLinearMap := operatorCoeff s p T 1
  leibniz' x y := by
    rw [operatorCoeff_one_leibniz s p T hzero hlie]
    rw [← lie_skew y (operatorCoeff s p T 1 x)]
    abel

end EnvelopingIsomorphism.Descent
