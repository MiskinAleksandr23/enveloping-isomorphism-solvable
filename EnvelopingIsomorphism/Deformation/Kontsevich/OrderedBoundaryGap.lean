import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPattern

/-! The physical insertion slot of an empty real boundary block. Equality
of the empty masks alone does not determine this slot; the collision center
and the ordered boundary values do. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OrderedBoundaryGap

open scoped Classical

def IsGap {m : ℕ} (p : Fin m → ℝ) (c : ℝ) (s : Fin (m + 1)) : Prop :=
  (∀ j, j.val < s.val → p j < c) ∧
    (∀ j, s.val ≤ j.val → c < p j)

theorem exists_gap {m : ℕ} (p : Fin m → ℝ) (hp : StrictMono p)
    (c : ℝ) (hne : ∀ j, p j ≠ c) : ∃ s : Fin (m + 1), IsGap p c s := by
  induction m with
  | zero => exact ⟨0, (fun j _ => Fin.elim0 j), (fun j _ => Fin.elim0 j)⟩
  | succ m ih =>
    by_cases hzero : p 0 < c
    · have ht : StrictMono (fun j : Fin m => p j.succ) := by
        intro j k hjk
        apply hp
        simpa only [Fin.lt_def, Fin.val_succ] using Nat.succ_lt_succ hjk
      obtain ⟨s, hs⟩ := ih (fun j : Fin m => p j.succ) ht (fun j => hne j.succ)
      refine ⟨s.succ, ?_, ?_⟩
      · intro j hj
        cases j using Fin.cases with
        | zero => exact hzero
        | succ j => exact hs.1 j (by simpa only [Fin.val_succ, Nat.succ_lt_succ_iff] using hj)
      · intro j hj
        cases j using Fin.cases with
        | zero => simp only [Fin.val_zero, Fin.val_succ] at hj; omega
        | succ j => exact hs.2 j (by simpa only [Fin.val_succ, Nat.succ_le_succ_iff] using hj)
    · have hc : c < p 0 := lt_of_le_of_ne (le_of_not_gt hzero) (Ne.symm (hne 0))
      refine ⟨0, ?_, ?_⟩
      · intro j hj
        simp only [Fin.val_zero] at hj
        omega
      · intro j _
        exact hc.trans_le (hp.monotone (Fin.zero_le j))

theorem gap_unique {m : ℕ} {p : Fin m → ℝ} {c : ℝ} {s t : Fin (m + 1)}
    (hs : IsGap p c s) (ht : IsGap p c t) : s = t := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hst | hts
  · let j : Fin m := ⟨s.val, by have := t.isLt; omega⟩
    exact (lt_asymm (ht.1 j hst) (hs.2 j le_rfl))
  · let j : Fin m := ⟨t.val, by have := s.isLt; omega⟩
    exact (lt_asymm (hs.1 j hts) (ht.2 j le_rfl))

theorem existsUnique_gap {m : ℕ} (p : Fin m → ℝ) (hp : StrictMono p)
    (c : ℝ) (hne : ∀ j, p j ≠ c) : ∃! s : Fin (m + 1), IsGap p c s := by
  obtain ⟨s, hs⟩ := exists_gap p hp c hne
  exact ⟨s, hs, fun _ ht => gap_unique ht hs⟩

def slot {m : ℕ} (p : Fin m → ℝ) (hp : StrictMono p)
    (c : ℝ) (hne : ∀ j, p j ≠ c) : Fin (m + 1) :=
  (exists_gap p hp c hne).choose

theorem slot_isGap {m : ℕ} (p : Fin m → ℝ) (hp : StrictMono p)
    (c : ℝ) (hne : ∀ j, p j ≠ c) : IsGap p c (slot p hp c hne) :=
  (exists_gap p hp c hne).choose_spec

theorem slot_empty_block {m : ℕ} (p : Fin m → ℝ) (hp : StrictMono p)
    (c : ℝ) (hne : ∀ j, p j ≠ c) :
    boundaryClusterBlock (slot p hp c hne) (slot p hp c hne) = ∅ := by
  ext j
  simp only [mem_boundaryClusterBlock, Finset.notMem_empty, iff_false]
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich.OrderedBoundaryGap
