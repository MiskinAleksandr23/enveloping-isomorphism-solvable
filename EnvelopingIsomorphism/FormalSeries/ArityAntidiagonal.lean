import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Literal finite reindexing between a bounded arity grid and its total-arity antidiagonals. -/

namespace EnvelopingIsomorphism.FormalSeries.ArityAntidiagonal

open scoped BigOperators
open Finset.HasAntidiagonal

variable {W : Type*} [AddCommMonoid W]

/-- The finite grid entries whose total arity is strictly below N. -/
def triangle (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 + p.2 < N)

@[simp] theorem mem_triangle (N : ℕ) (p : ℕ × ℕ) :
    p ∈ triangle N ↔ p.1 + p.2 < N := by
  rcases p with ⟨a, b⟩
  simp only [triangle, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The actual finite bijection sends (a,b) to the antidiagonal indexed by a+b.
No support or vanishing condition is needed on the function inside the triangle. -/
theorem sum_triangle_eq_sum_antidiagonal (N : ℕ) (f : ℕ → ℕ → W) :
    (∑ p ∈ triangle N, f p.1 p.2) =
      ∑ m ∈ Finset.range N, ∑ p ∈ antidiagonal m, f p.1 p.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun p : ℕ × ℕ => (⟨p.1 + p.2, p⟩ : (m : ℕ) × (ℕ × ℕ)))
    (fun p => p.2)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
    exact ⟨(mem_triangle N p).mp hp, trivial⟩
  · rintro ⟨m, p⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hp
    exact (mem_triangle N p).mpr (hp.2 ▸ hp.1)
  · intro p hp
    rfl
  · rintro ⟨m, p⟩ hp
    have he := (Finset.mem_sigma.mp hp).2
    have hm : p.1 + p.2 = m := Finset.mem_antidiagonal.mp he
    cases hm
    rfl
  · intro p hp
    rfl

/-- A rectangular finite sum with zero terms outside the support triangle is
exactly the finite sum by total arity. This includes the empty N=0 grid. -/
theorem sum_range_square_eq_sum_antidiagonal (N : ℕ) (f : ℕ → ℕ → W)
    (hzero : ∀ a b, N ≤ a + b → f a b = 0) :
    (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, f a b) =
      ∑ m ∈ Finset.range N, ∑ p ∈ antidiagonal m, f p.1 p.2 := by
  rw [← Finset.sum_product (Finset.range N) (Finset.range N) (fun p : ℕ × ℕ => f p.1 p.2)]
  calc
    (∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), f p.1 p.2) =
        ∑ p ∈ triangle N, f p.1 p.2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      exact hzero p.1 p.2 (Nat.le_of_not_gt (fun h => hnot ((mem_triangle N p).mpr h)))
    _ = _ := sum_triangle_eq_sum_antidiagonal N f

end EnvelopingIsomorphism.FormalSeries.ArityAntidiagonal
