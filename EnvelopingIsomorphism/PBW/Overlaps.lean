import EnvelopingIsomorphism.PBW.Words

/-!
# Positions of two adjacent replacements in a word

Two adjacent pairs have the same position, overlap in one letter, or are
disjoint.  These lemmas expose the corresponding word decompositions for the
PBW compatibility proof.
-/

namespace EnvelopingIsomorphism.PBW

variable {α : Type*}

/-- Classification with the first replacement no further right than the second. -/
theorem adjacent_pair_overlap_cases
    {p q s t : List α} {i j k l : α}
    (h : p ++ i :: j :: s = q ++ k :: l :: t) (hlen : p.length ≤ q.length) :
    (p = q ∧ i = k ∧ j = l ∧ s = t) ∨
      (q = p ++ [i] ∧ j = k ∧ s = l :: t) ∨
        ∃ m : List α, q = p ++ i :: j :: m ∧ s = m ++ k :: l :: t := by
  have hp : p <+: p ++ i :: j :: s := ⟨_, rfl⟩
  have hq : q <+: p ++ i :: j :: s := ⟨_, h.symm⟩
  obtain ⟨r, hr⟩ := List.prefix_of_prefix_length_le hp hq hlen
  subst q
  rw [List.append_assoc, List.append_cancel_left_eq] at h
  cases r with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact Or.inl ⟨by simp, h.1, h.2.1, h.2.2⟩
  | cons a r =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases r with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h
          exact Or.inr (Or.inl ⟨rfl, h.1, h.2⟩)
      | cons b m =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          exact Or.inr (Or.inr ⟨m, rfl, h⟩)

/-- Symmetric classification of two adjacent pairs in the same word. -/
theorem adjacent_decompositions
    {p q s t : List α} {i j k l : α}
    (h : p ++ i :: j :: s = q ++ k :: l :: t) :
    (p = q ∧ i = k ∧ j = l ∧ s = t) ∨
      (q = p ++ [i] ∧ j = k ∧ s = l :: t) ∨
      (p = q ++ [k] ∧ l = i ∧ t = j :: s) ∨
      (∃ m : List α, q = p ++ i :: j :: m ∧ s = m ++ k :: l :: t) ∨
      (∃ m : List α, p = q ++ k :: l :: m ∧ t = m ++ i :: j :: s) := by
  rcases Nat.le_total p.length q.length with hlen | hlen
  · rcases adjacent_pair_overlap_cases h hlen with hsame | hover | hdisjoint
    · exact Or.inl hsame
    · exact Or.inr (Or.inl hover)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hdisjoint)))
  · rcases adjacent_pair_overlap_cases h.symm hlen with hsame | hover | hdisjoint
    · rcases hsame with ⟨hp, hi, hj, hs⟩
      exact Or.inl ⟨hp.symm, hi.symm, hj.symm, hs.symm⟩
    · exact Or.inr (Or.inr (Or.inl hover))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hdisjoint)))

end EnvelopingIsomorphism.PBW
