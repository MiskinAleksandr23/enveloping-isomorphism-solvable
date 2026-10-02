import EnvelopingIsomorphism.PBW.Words
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort

/-!
# The exponent index of an ordered word

The existing multiset/finitely-supported-function equivalence and multiset
sorting identify ordered PBW words with the usual monomial indices `α →₀ ℕ`.
-/

namespace EnvelopingIsomorphism.PBW

variable {α : Type*} [LinearOrder α]

/-- The multiplicities of all letters in a word. -/
noncomputable def wordIndex (w : List α) : α →₀ ℕ :=
  (w : Multiset α).toFinsupp

@[simp] theorem wordIndex_apply (w : List α) (i : α) : wordIndex w i = w.count i := by
  simp [wordIndex]

@[simp] theorem wordIndex_nil : wordIndex ([] : List α) = 0 :=
  Multiset.toFinsupp_zero

@[simp] theorem wordIndex_append (u v : List α) :
    wordIndex (u ++ v) = wordIndex u + wordIndex v := by
  simp only [wordIndex, ← Multiset.coe_add, Multiset.toFinsupp_add]

@[simp] theorem wordIndex_singleton (i : α) : wordIndex [i] = Finsupp.single i 1 :=
  Multiset.toFinsupp_singleton i

@[simp] theorem wordIndex_cons (i : α) (s : List α) :
    wordIndex (i :: s) = Finsupp.single i 1 + wordIndex s := by
  simpa using wordIndex_append [i] s

theorem wordIndex_eq_iff_perm {u v : List α} : wordIndex u = wordIndex v ↔ u.Perm v := by
  exact Multiset.toFinsupp.injective.eq_iff.trans Multiset.coe_eq_coe

theorem wordIndex_sum (w : List α) : (wordIndex w).sum (fun _ n => n) = w.length :=
  Multiset.toFinsupp_sum_eq _

/-- The unique ordered word with the prescribed letter multiplicities. -/
noncomputable def orderedWord (m : α →₀ ℕ) : List α :=
  m.toMultiset.sort (· ≤ ·)

theorem pairwise_orderedWord (m : α →₀ ℕ) : (orderedWord m).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

@[simp] theorem wordIndex_orderedWord (m : α →₀ ℕ) : wordIndex (orderedWord m) = m := by
  simp [wordIndex, orderedWord]

theorem orderedWord_wordIndex {w : List α} (hw : w.Pairwise (· ≤ ·)) :
    orderedWord (wordIndex w) = w := by
  simp only [orderedWord, wordIndex, Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) hw

theorem eq_of_wordIndex_eq {u v : List α} (hu : u.Pairwise (· ≤ ·))
    (hv : v.Pairwise (· ≤ ·)) (h : wordIndex u = wordIndex v) : u = v :=
  (wordIndex_eq_iff_perm.mp h).eq_of_pairwise' hu hv

theorem length_orderedWord (m : α →₀ ℕ) :
    (orderedWord m).length = m.sum (fun _ n => n) := by
  simp [orderedWord, Finsupp.card_toMultiset, Function.id_def]

/-- Ordered words as a subtype of words. -/
def OrderedWord (α : Type*) [LinearOrder α] := {w : List α // w.Pairwise (· ≤ ·)}

/-- Ordered words and finitely supported exponent indices are equivalent. -/
noncomputable def orderedWordEquiv : OrderedWord α ≃ (α →₀ ℕ) where
  toFun w := wordIndex w.1
  invFun m := ⟨orderedWord m, pairwise_orderedWord m⟩
  left_inv w := Subtype.ext (orderedWord_wordIndex w.2)
  right_inv := wordIndex_orderedWord

end EnvelopingIsomorphism.PBW
