import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel

/-!
Finite averaging for additive cocycles.  The action is linear over `ℚ`, which
allows semilinear Galois actions over a larger characteristic-zero field.
-/

namespace EnvelopingIsomorphism.Descent

open scoped BigOperators

universe u v

variable {Γ : Type u} [Group Γ] [Fintype Γ]
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

/-- The average used to trivialize an additive cocycle. -/
def cocycleAverage (a : Γ → V) : V :=
  (Fintype.card Γ : ℚ)⁻¹ • ∑ σ, a σ

/-- Averaging a finite additive cocycle gives the indicated coboundary. -/
theorem additive_cocycle_average
    (ρ : Γ →* Module.End ℚ V) (a : Γ → V)
    (ha : ∀ σ τ, a (σ * τ) = a σ + ρ σ (a τ)) (σ : Γ) :
    a σ = cocycleAverage a - ρ σ (cocycleAverage a) := by
  classical
  have hcard : (Fintype.card Γ : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ τ, a τ) =
      (Fintype.card Γ : ℚ) • a σ + ρ σ (∑ τ, a τ) := by
    calc
      (∑ τ, a τ) = ∑ τ, a (σ * τ) := (Equiv.sum_comp (Equiv.mulLeft σ) a).symm
      _ = ∑ τ, (a σ + ρ σ (a τ)) := by simp_rw [ha]
      _ = (Fintype.card Γ : ℚ) • a σ + ρ σ (∑ τ, a τ) := by
        simp [Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul]
  have havg : cocycleAverage a = a σ + ρ σ (cocycleAverage a) := by
    calc
      cocycleAverage a = (Fintype.card Γ : ℚ)⁻¹ •
          ((Fintype.card Γ : ℚ) • a σ + ρ σ (∑ τ, a τ)) := by
        exact congrArg ((Fintype.card Γ : ℚ)⁻¹ • ·) hsum
      _ = a σ + ρ σ (cocycleAverage a) := by
        simp [smul_add, smul_smul, hcard, cocycleAverage]
  exact (eq_sub_iff_add_eq).mpr havg.symm

/-- Every additive cocycle for a finite group on a rational vector space is a
coboundary; the sign matches `a σ = b⁻¹ * σ(b)` in multiplicative notation. -/
theorem additive_cocycle_exists
    (ρ : Γ →* Module.End ℚ V) (a : Γ → V)
    (ha : ∀ σ τ, a (σ * τ) = a σ + ρ σ (a τ)) :
    ∃ b : V, ∀ σ, a σ = ρ σ b - b := by
  refine ⟨-cocycleAverage a, fun σ => ?_⟩
  rw [map_neg]
  simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using additive_cocycle_average ρ a ha σ

end EnvelopingIsomorphism.Descent
