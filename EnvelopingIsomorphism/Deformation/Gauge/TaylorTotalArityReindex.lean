import EnvelopingIsomorphism.Deformation.Gauge.TaylorIndexReindex
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Finite total-arity reindexing with a proved cutoff. -/

namespace EnvelopingIsomorphism.Deformation.Gauge
open scoped BigOperators

variable {W : Type*} [AddCommMonoid W]

/-- Sum every total arity and then regroup by positive perturbation arity.
Terms beyond the common total cutoff are explicitly required to vanish. -/
theorem taylor_total_arity_reindex (f : ℕ → ℕ → W) (D M : ℕ)
    (ht : ∀ r j, D < r → f r j = 0)
    (hm : ∀ r j, M ≤ r + j → f r j = 0) :
    (∑ m ∈ Finset.range M, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      if p.1 = 0 then 0 else f p.1 p.2) =
      ∑ n ∈ Finset.range D, ∑ j ∈ Finset.range M, f (n + 1) j := by
  classical
  simp_rw [← taylor_range_antidiagonal_reindex f D _ ht]
  have hinner (m : ℕ) (hmM : m ∈ Finset.range M) (n : ℕ) :
      (∑ j ∈ Finset.range (m + 1), if n + 1 + j = m then f (n + 1) j else 0) =
      ∑ j ∈ Finset.range M, if n + 1 + j = m then f (n + 1) j else 0 := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hmM)))
    intro j hj hjm
    have hjm' : m + 1 ≤ j := by simpa using hjm
    exact if_neg (by omega)
  calc
    _ = ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range D,
        ∑ j ∈ Finset.range M, if n + 1 + j = m then f (n + 1) j else 0 := by
      apply Finset.sum_congr rfl
      intro m hmM
      apply Finset.sum_congr rfl
      intro n hn
      exact hinner m hmM n
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single (n + 1 + j)]
      · simp
      · intro m hmM hne
        exact if_neg (Ne.symm hne)
      · intro hnot
        have hge : M ≤ n + 1 + j := by simpa using hnot
        rw [hm (n + 1) j hge]
        simp

end EnvelopingIsomorphism.Deformation.Gauge
