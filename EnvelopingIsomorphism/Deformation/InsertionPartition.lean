import Mathlib.Algebra.BigOperators.Fin

/-! The finite before/inside/after partition of a composite insertion row. -/

namespace EnvelopingIsomorphism.Deformation

variable {T : Type*} [AddCommMonoid T]

/-- After replacing outer slot i by n+1 slots, every slot of the composite is
uniquely before i, inside the inserted block, or after it. All displayed maps
are total on their finite source types; filtering carries no hidden casts. -/
theorem sum_insertion_slots (m n : ℕ) (i : Fin (m + 1)) (F : Fin ((m + n) + 1) → T) :
    (∑ j, F j) =
      (∑ j : Fin (m + 1) with j < i, F ⟨(j : ℕ), by omega⟩) +
      (∑ k : Fin (n + 1), F ⟨(i : ℕ) + (k : ℕ), by omega⟩) +
      (∑ j : Fin (m + 1) with i < j, F ⟨(j : ℕ) + n, by omega⟩) := by
  classical
  let B : Finset (Fin ((m + n) + 1)) := Finset.univ.filter (fun j ↦ (j : ℕ) < (i : ℕ))
  let I : Finset (Fin ((m + n) + 1)) :=
    Finset.univ.filter (fun j ↦ (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + n)
  let A : Finset (Fin ((m + n) + 1)) :=
    Finset.univ.filter (fun j ↦ (i : ℕ) + n < (j : ℕ))
  have hBI : Disjoint B I := by
    apply Finset.disjoint_left.mpr
    intro j hj hji
    simp only [B, I, Finset.mem_filter, Finset.mem_univ, true_and] at hj hji
    omega
  have hBIA : Disjoint (B ∪ I) A := by
    apply Finset.disjoint_left.mpr
    intro j hj hja
    simp only [B, I, A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj hja
    omega
  have hcover : (B ∪ I) ∪ A = Finset.univ := by
    ext j
    simp only [B, I, A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  have hbefore :
      (∑ j : Fin (m + 1) with j < i, F ⟨(j : ℕ), by omega⟩) = ∑ j ∈ B, F j := by
    apply Finset.sum_bij (fun (j : Fin (m + 1)) _ ↦ (⟨(j : ℕ), by omega⟩ : Fin ((m + n) + 1)))
    · intro j hj
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hj).2
    · intro a ha b hb hab
      apply Fin.ext
      exact congrArg (fun z : Fin ((m + n) + 1) ↦ z.val) hab
    · intro j hj
      have hj' : (j : ℕ) < (i : ℕ) := by simpa [B] using hj
      let a : Fin (m + 1) := ⟨(j : ℕ), by omega⟩
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj'
      · exact Fin.ext rfl
    · intro j hj
      rfl
  have hinside :
      (∑ k : Fin (n + 1), F ⟨(i : ℕ) + (k : ℕ), by omega⟩) = ∑ j ∈ I, F j := by
    apply Finset.sum_bij (fun (k : Fin (n + 1)) _ ↦
      (⟨(i : ℕ) + (k : ℕ), by omega⟩ : Fin ((m + n) + 1)))
    · intro k hk
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro a ha b hb hab
      apply Fin.ext
      have heq := congrArg Fin.val hab
      change (i : ℕ) + (a : ℕ) = (i : ℕ) + (b : ℕ) at heq
      omega
    · intro j hj
      have hj' : (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + n := by simpa [I] using hj
      let a : Fin (n + 1) := ⟨(j : ℕ) - (i : ℕ), by omega⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      change (i : ℕ) + ((j : ℕ) - (i : ℕ)) = (j : ℕ)
      omega
    · intro k hk
      rfl
  have hafter :
      (∑ j : Fin (m + 1) with i < j, F ⟨(j : ℕ) + n, by omega⟩) = ∑ j ∈ A, F j := by
    apply Finset.sum_bij (fun (j : Fin (m + 1)) _ ↦ (⟨(j : ℕ) + n, by omega⟩ : Fin ((m + n) + 1)))
    · intro j hj
      have hj' : i < j := (Finset.mem_filter.mp hj).2
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      change (i : ℕ) + n < (j : ℕ) + n
      omega
    · intro a ha b hb hab
      apply Fin.ext
      have heq := congrArg Fin.val hab
      change (a : ℕ) + n = (b : ℕ) + n at heq
      omega
    · intro j hj
      have hj' : (i : ℕ) + n < (j : ℕ) := by simpa [A] using hj
      let a : Fin (m + 1) := ⟨(j : ℕ) - n, by omega⟩
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (i : ℕ) < (j : ℕ) - n
        omega
      · apply Fin.ext
        change (j : ℕ) - n + n = (j : ℕ)
        omega
    · intro j hj
      rfl
  rw [hbefore, hinside, hafter, ← Finset.sum_union hBI, ← Finset.sum_union hBIA, hcover]

end EnvelopingIsomorphism.Deformation
