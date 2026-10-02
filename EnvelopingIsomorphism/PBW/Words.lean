import Mathlib.Data.List.Count
import Mathlib.Data.List.Pairwise
import Mathlib.Order.RelClasses

/-!
# Ordered words and the terminating PBW measure

The adjacent PBW replacement either swaps an inverted pair or replaces two
letters by one.  Length followed lexicographically by the inversion count
therefore decreases in both cases.  The alphabet need not be finite.
-/

namespace EnvelopingIsomorphism.PBW

variable {α : Type*} [LinearOrder α]

/-- The number of strictly inverted pairs of positions in a word. -/
def inversionCount : List α → ℕ
  | [] => 0
  | i :: s => s.countP (fun j => decide (j < i)) + inversionCount s

@[simp] theorem inversionCount_nil : inversionCount ([] : List α) = 0 := rfl

@[simp] theorem inversionCount_cons (i : α) (s : List α) :
    inversionCount (i :: s) = s.countP (fun j => decide (j < i)) + inversionCount s := rfl

/-- Compatibility spelling for the two-component word measure. -/
abbrev inversions := @inversionCount

/-- Swapping a strict adjacent inversion removes exactly one inversion. -/
theorem inversionCount_swap (p s : List α) {i j : α} (hji : j < i) :
    inversionCount (p ++ i :: j :: s) = inversionCount (p ++ j :: i :: s) + 1 := by
  induction p with
  | nil =>
      simp [inversionCount, hji, not_lt.mpr hji.le]
      omega
  | cons a p ih =>
      simp only [List.cons_append, inversionCount_cons, List.countP_append,
        List.countP_cons] at *
      omega

theorem inversionCount_swap_lt (p s : List α) {i j : α} (hji : j < i) :
    inversionCount (p ++ j :: i :: s) < inversionCount (p ++ i :: j :: s) := by
  rw [inversionCount_swap p s hji]
  omega

/-- The lexicographic termination measure for PBW replacements. -/
def wordMeasure (w : List α) : ℕ × ℕ := (w.length, inversionCount w)

/-- Strict descent of the length/inversion measure. -/
def WordLT (u v : List α) : Prop :=
  Prod.Lex (· < ·) (· < ·) (wordMeasure u) (wordMeasure v)

theorem wordLT_wellFounded : WellFounded (WordLT (α := α)) :=
  InvImage.wf wordMeasure (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

theorem wordLT_of_length_lt {u v : List α} (h : u.length < v.length) : WordLT u v :=
  Prod.Lex.left _ _ h

theorem wordLT_of_length_eq_of_inversionCount_lt {u v : List α}
    (hlen : u.length = v.length) (hinv : inversionCount u < inversionCount v) :
    WordLT u v := by
  unfold WordLT wordMeasure
  rw [hlen]
  exact Prod.Lex.right _ hinv

/-- The quadratic, swapped term in the PBW relation has smaller measure. -/
theorem wordLT_swap (p s : List α) {i j : α} (hji : j < i) :
    WordLT (p ++ j :: i :: s) (p ++ i :: j :: s) := by
  apply wordLT_of_length_eq_of_inversionCount_lt
  · simp
  · exact inversionCount_swap_lt p s hji

omit [LinearOrder α] in
theorem length_replacePair_lt (p s : List α) (i j k : α) :
    (p ++ k :: s).length < (p ++ i :: j :: s).length := by
  simp

/-- Every linear bracket term in the PBW relation has smaller measure. -/
theorem wordLT_replacePair (p s : List α) (i j k : α) :
    WordLT (p ++ k :: s) (p ++ i :: j :: s) :=
  wordLT_of_length_lt (length_replacePair_lt p s i j k)

/-- Every word which is not ordered contains a strictly inverted adjacent pair. -/
theorem exists_adjacent_inversion (w : List α) :
    ¬ w.Pairwise (· ≤ ·) →
      ∃ (p : List α) (i j : α) (s : List α), w = p ++ i :: j :: s ∧ j < i := by
  induction w with
  | nil => simp
  | cons i t ih =>
      intro h
      cases t with
      | nil => simp at h
      | cons j s =>
          by_cases hji : j < i
          · exact ⟨[], i, j, s, rfl, hji⟩
          · have hs : ¬ (j :: s).Pairwise (· ≤ ·) := by
              intro hs
              exact h (List.Pairwise.cons_cons_of_trans (not_lt.mp hji) hs)
            obtain ⟨p, a, b, t, hp, hab⟩ := ih hs
            exact ⟨i :: p, a, b, t, by simp [hp], hab⟩

theorem pairwise_iff_no_adjacent_inversion (w : List α) :
    w.Pairwise (· ≤ ·) ↔
      ¬ ∃ (p : List α) (i j : α) (s : List α), w = p ++ i :: j :: s ∧ j < i := by
  constructor
  · rintro h ⟨p, i, j, s, rfl, hji⟩
    have hij := (List.pairwise_cons_cons_iff_of_trans.mp
      (List.pairwise_append.mp h).2.1).1
    exact (not_lt.mpr hij) hji
  · intro h
    by_contra hn
    exact h (exists_adjacent_inversion w hn)

theorem pairwise_iff_adjacent_le (w : List α) :
    w.Pairwise (· ≤ ·) ↔
      ∀ (p : List α) (i j : α) (s : List α), w = p ++ i :: j :: s → i ≤ j := by
  rw [pairwise_iff_no_adjacent_inversion]
  simp only [not_exists, not_and, not_lt]

theorem inversionCount_eq_zero_iff (w : List α) :
    inversionCount w = 0 ↔ w.Pairwise (· ≤ ·) := by
  induction w with
  | nil => simp
  | cons i s ih =>
      simp [inversionCount_cons, List.countP_eq_zero,
        List.pairwise_cons, ih]

end EnvelopingIsomorphism.PBW
