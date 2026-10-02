import EnvelopingIsomorphism.Descent.FilteredAutomorphism
import EnvelopingIsomorphism.Descent.PolynomialTangent
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-! Finite exponentials and logarithmic tangent operators for filtration-raising maps. -/

namespace EnvelopingIsomorphism.Descent

open Finset
open scoped BigOperators
open Polynomial

universe u v
variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [LieAlgebra ℚ L]

/-- The polynomial in the parameter with values `n.choose j` at natural parameters. -/
noncomputable def binomialPolynomial (j : ℕ) : k[X] :=
  C ((j.factorial : k)⁻¹) * descPochhammer k j

@[simp] theorem binomialPolynomial_zero : binomialPolynomial (k := k) 0 = 1 := by
  simp [binomialPolynomial]

@[simp] theorem binomialPolynomial_one : binomialPolynomial (k := k) 1 = X := by
  simp [binomialPolynomial]

@[simp] theorem binomialPolynomial_eval_nat (j n : ℕ) :
    (binomialPolynomial (k := k) j).eval (n : k) = (n.choose j : k) := by
  simp only [binomialPolynomial, eval_mul, eval_C]
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

@[simp] theorem binomialPolynomial_coeff_zero (j : ℕ) :
    (binomialPolynomial (k := k) j).coeff 0 = if j = 0 then 1 else 0 := by
  rw [coeff_zero_eq_eval_zero, ← Nat.cast_zero, binomialPolynomial_eval_nat]
  by_cases hj : j = 0
  · subst j; simp
  · rw [if_neg hj, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]

/-- The binomial expansion can be cut off at any nilpotence bound. -/
theorem binomial_sum_eq_pow {N : ℕ} {T : Module.End k L} (hT : T ^ N = 0) (n : ℕ) :
    (∑ j ∈ range N, (binomialPolynomial (k := k) j).eval (n : k) • T ^ j) =
      (T + 1) ^ n := by
  simp only [binomialPolynomial_eval_nat]
  have heq : (∑ j ∈ range N, (n.choose j : k) • T ^ j) =
      ∑ j ∈ range (n + 1), (n.choose j : k) • T ^ j := by
    rcases le_total N (n + 1) with hN | hn
    · apply sum_subset (range_mono hN)
      intro j hj hjN
      have hj' : N ≤ j := by simpa only [mem_range, not_lt] using hjN
      rw [pow_eq_zero_of_le hj' hT, smul_zero]
    · symm
      apply sum_subset (range_mono hn)
      intro j hj hjn
      have hj' : n < j := by simp only [mem_range, not_lt] at hjn; omega
      simp [Nat.choose_eq_zero_of_lt hj']
  rw [heq, (Commute.one_right T).add_pow]
  apply sum_congr rfl
  intro j hj
  simp [← nsmul_eq_mul', Nat.cast_smul_eq_nsmul]

/-- The finite logarithmic tangent of a unipotent Lie automorphism. Its coefficients
are the linear coefficients of the polynomials `binom(s,j)`; no analytic limit is used. -/
noncomputable def binomialLogDerivation (u : L ≃ₗ⁅k⁆ L) (N : ℕ)
    (hN : (u.toLinearMap - 1) ^ (N + 2) = 0) : LieDerivation k L L :=
  polynomialTangent (range (N + 2)) binomialPolynomial
    (fun j => (u.toLinearMap - 1) ^ j)
    (by simp [operatorCoeff])
    (by
      intro n x y
      rw [binomial_sum_eq_pow hN n, sub_add_cancel, ← lieEquiv_pow_toLinearMap]
      exact (u ^ n).map_lie x y)

namespace FiniteFiltration

variable (F : FiniteFiltration k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The linear space of derivations increasing filtration by `r`. -/
def raisingDerivations (r : ℕ) : Submodule k (LieDerivation k L L) :=
  (F.raisingSubmodule r).comap (LieDerivation.toLinearMapLieHom k L).toLinearMap

@[simp] theorem mem_raisingDerivations {r : ℕ} {D : LieDerivation k L L} :
    D ∈ F.raisingDerivations r ↔ D.toLinearMap ∈ F.raisingSubmodule r := Iff.rfl

/-- The finite exponential agrees with `1+T` in the next filtration layer. -/
theorem exp_firstOrder {r : ℕ} (hr : 1 ≤ r) {T : Module.End k L}
    (hT : T ∈ F.raisingSubmodule r) :
    IsNilpotent.exp T - 1 - T ∈ F.raisingSubmodule (r + 1) := by
  have hpow : T ^ (2 + F.length) = 0 :=
    pow_eq_zero_of_le (by omega) (F.pow_length_eq_zero hr hT)
  have heq : IsNilpotent.exp T - 1 - T =
      ∑ i ∈ range F.length, ((2 + i).factorial : ℚ)⁻¹ • T ^ (2 + i) := by
    rw [IsNilpotent.exp_eq_sum hpow, sum_range_add]
    simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, pow_one, Nat.factorial_one]
    abel
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  have h := (F.raisingSubmodule (r + 1)).smul_mem
    ((((2 + i).factorial : ℚ)⁻¹ : ℚ) : k) (F.pow_mem_succ (n := 2 + i) hr (by omega) hT)
  simpa only [ratCast_smul_eq k ℚ, Rat.cast_id] using h

theorem exp_sub_one_mem {r : ℕ} (hr : 1 ≤ r) {T : Module.End k L}
    (hT : T ∈ F.raisingSubmodule r) :
    IsNilpotent.exp T - 1 ∈ F.raisingSubmodule r := by
  have hrem := F.raising_antitone (Nat.le_succ r) (F.exp_firstOrder hr hT)
  simpa only [sub_add_cancel] using (F.raisingSubmodule r).add_mem hrem hT

theorem lieDerivation_exp_firstOrder {r : ℕ} (hr : 1 ≤ r)
    (D : LieDerivation k L L) (hD : D ∈ F.raisingDerivations r) :
    (D.exp (F.isNilpotent hr hD)).toLinearMap - 1 - D.toLinearMap ∈
      F.raisingSubmodule (r + 1) :=
  F.exp_firstOrder hr hD

theorem lieDerivation_exp_mem {r : ℕ} (D : LieDerivation k L L)
    (hD : D ∈ F.raisingDerivations (r + 1)) :
    D.exp (F.isNilpotent (by omega) hD) ∈ F.automorphismSubgroup r :=
  F.exp_sub_one_mem (by omega) hD

/-- The logarithmic tangent of a filtration-raising Lie automorphism. -/
noncomputable def logDerivation {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r) : LieDerivation k L L :=
  binomialLogDerivation u F.length
    (pow_eq_zero_of_le (by omega) (F.pow_length_eq_zero hr hu))

theorem logDerivation_toLinearMap {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    (F.logDerivation hr u hu).toLinearMap =
      ∑ j ∈ range (F.length + 2), (binomialPolynomial (k := k) j).coeff 1 •
        (u.toLinearMap - 1) ^ j := rfl

theorem logDerivation_firstOrder {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    (F.logDerivation hr u hu).toLinearMap - (u.toLinearMap - 1) ∈
      F.raisingSubmodule (r + 1) := by
  have heq : (F.logDerivation hr u hu).toLinearMap - (u.toLinearMap - 1) =
      ∑ j ∈ range F.length, (binomialPolynomial (k := k) (2 + j)).coeff 1 •
        (u.toLinearMap - 1) ^ (2 + j) := by
    rw [F.logDerivation_toLinearMap hr u hu, Nat.add_comm F.length 2, sum_range_add]
    simp [sum_range_succ, Polynomial.coeff_one]
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  exact (F.raisingSubmodule (r + 1)).smul_mem _
    (F.pow_mem_succ (n := 2 + j) hr (by omega) hu)

theorem logDerivation_mem {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    F.logDerivation hr u hu ∈ F.raisingDerivations r := by
  have hrem := F.raising_antitone (Nat.le_succ r) (F.logDerivation_firstOrder hr u hu)
  have h := (F.raisingSubmodule r).add_mem hrem hu
  simpa only [sub_add_cancel, mem_raisingDerivations] using h

end FiniteFiltration

end EnvelopingIsomorphism.Descent
