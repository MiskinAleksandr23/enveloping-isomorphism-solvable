import EnvelopingIsomorphism.FormalSeries.Endomorphism
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

/-!
# Genuine monomial exponentials and linear intertwiners

The coefficient rings of the operator series need not be commutative.
Intertwining is proved first for powers and then for the actual finite
coefficient sums defining the complete exponential.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

set_option backward.isDefEq.respectTransparency false

open PowerSeries PowerSeriesModule
open scoped BigOperators

theorem noncomm_monomial_pow {R : Type*} [Semiring R] (N : ℕ) (x : R) (m : ℕ) :
    (monomial N x) ^ m = monomial (m * N) (x ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, monomial_mul_monomial, Nat.succ_mul, pow_succ]

section Intertwining

variable {k V W : Type*} [CommRing k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem intertwines_end_pow (T : V →ₗ[k] W) (D : Module.End k V) (E : Module.End k W)
    (h : ∀ v, T (D v) = E (T v)) (m : ℕ) (v : V) : T ((D ^ m) v) = (E ^ m) (T v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change T (D ((D ^ m) v)) = E ((E ^ m) (T v))
    rw [h, ih]

variable [Algebra ℚ k]
  [Module ℚ V] [IsScalarTower ℚ k V] [SMulCommClass k ℚ V]
  [Module ℚ W] [IsScalarTower ℚ k W] [SMulCommClass k ℚ W]

/-- Each actual exponential coefficient respects a linear intertwiner. -/
theorem intertwines_exp_monomial_coeff (T : V →ₗ[k] W) (D : Module.End k V) (E : Module.End k W)
    (h : ∀ v, T (D v) = E (T v)) (N m : ℕ) (v : V) :
    T ((coeff m (exp (monomial N D))) v) = (coeff m (exp (monomial N E))) (T v) := by
  simp only [exp, coeff_sumPowers, noncomm_monomial_pow, coeff_monomial]
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, map_rat_smul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp [intertwines_end_pow T D E h]

/-- The complete exponential action commutes with coefficientwise extension of a real intertwiner. -/
theorem map_actV_exp_monomial (T : V →ₗ[k] W) (D : Module.End k V) (E : Module.End k W)
    (h : ∀ v, T (D v) = E (T v)) (N : ℕ) (x : PowerSeriesModule k V) :
    PowerSeriesModule.map T (actV (exp (monomial N D)) x) =
      actV (exp (monomial N E)) (PowerSeriesModule.map T x) := by
  apply PowerSeriesModule.ext
  intro n
  rw [coeffV_map, coeffV_actV, map_sum, coeffV_actV]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  rw [coeffV_map]
  exact intertwines_exp_monomial_coeff T D E h N i (coeffV j x)

end Intertwining

end EnvelopingIsomorphism.FormalSeries
