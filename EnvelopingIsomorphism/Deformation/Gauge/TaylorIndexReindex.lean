import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
Finite index bookkeeping for positive-arity Taylor coefficients. No
Maurer–Cartan, multilinearity, or module assumptions enter the reindexing.
-/

namespace EnvelopingIsomorphism.Deformation.Gauge

open scoped BigOperators

variable {W : Type*} [AddCommMonoid W]

private theorem sum_range_eq_single_complement (f : ℕ → ℕ → W)
    (n m : ℕ) (hn : n ≤ m) :
    (∑ j ∈ Finset.range (m + 1), if n + j = m then f n j else 0) = f n (m - n) := by
  calc
    (∑ j ∈ Finset.range (m + 1), if n + j = m then f n j else 0) =
        if n + (m - n) = m then f n (m - n) else 0 := by
      apply Finset.sum_eq_single
      · intro j _ hj
        have hne : n + j ≠ m := by omega
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    _ = f n (m - n) := by simp [Nat.add_sub_of_le hn]

/-- Reindex a positive-arity, arity-truncated Taylor sum by `n+j=m`.
The explicit zero branch excludes arity zero without imposing any condition
on the values `f 0 j`. Only terms with `n>d` must vanish. -/
theorem taylor_range_antidiagonal_reindex (f : ℕ → ℕ → W) (d m : ℕ)
    (hcut : ∀ n j, d < n → f n j = 0) :
    (∑ a ∈ Finset.range d, ∑ j ∈ Finset.range (m + 1),
      if a + 1 + j = m then f (a + 1) j else 0) =
      ∑ nj ∈ Finset.HasAntidiagonal.antidiagonal m,
        if nj.1 = 0 then 0 else f nj.1 nj.2 := by
  classical
  let g (a : ℕ) : W :=
    ∑ j ∈ Finset.range (m + 1), if a + 1 + j = m then f (a + 1) j else 0
  have hg_m (a : ℕ) (ha : m ≤ a) : g a = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hne : a + 1 + j ≠ m := by omega
    simp [hne]
  have hg_d (a : ℕ) (ha : d ≤ a) : g a = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hcut (a + 1) j (by omega)]
    simp
  have hsum : (∑ a ∈ Finset.range d, g a) = ∑ a ∈ Finset.range m, g a := by
    by_cases hdm : d ≤ m
    · apply Finset.sum_subset (Finset.range_mono hdm)
      intro a _ had
      exact hg_d a (by simpa only [Finset.mem_range, not_lt] using had)
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt (Nat.lt_of_not_ge hdm)))
      intro a _ ham
      exact hg_m a (by simpa only [Finset.mem_range, not_lt] using ham)
  calc
    (∑ a ∈ Finset.range d, ∑ j ∈ Finset.range (m + 1),
        if a + 1 + j = m then f (a + 1) j else 0) =
        ∑ a ∈ Finset.range m, g a := hsum
    _ = ∑ a ∈ Finset.range m, f (a + 1) (m - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_range_eq_single_complement f (a + 1) m (by
        have := Finset.mem_range.mp ha
        omega)
    _ = ∑ nj ∈ Finset.HasAntidiagonal.antidiagonal m,
        if nj.1 = 0 then 0 else f nj.1 nj.2 := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
      simp

end EnvelopingIsomorphism.Deformation.Gauge
