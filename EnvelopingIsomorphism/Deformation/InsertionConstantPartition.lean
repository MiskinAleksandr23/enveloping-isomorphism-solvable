import Mathlib.Algebra.BigOperators.Fin

/-! Deleting one outer slot: the two surviving regions for constant insertion. -/

namespace EnvelopingIsomorphism.Deformation

variable {T : Type*} [AddCommMonoid T]

/-- A sum over the slots left after deleting j splits into original slots before
and after j. Dependent conditionals expose exactly the bounds needed by each map. -/
theorem sum_deleted_slot (m : ℕ) (j : Fin ((m + 1) + 1)) (F : Fin (m + 1) → T) :
    (∑ k, F k) =
      (∑ i : Fin ((m + 1) + 1), if h : i < j then F ⟨(i : ℕ), by omega⟩ else 0) +
      (∑ i : Fin ((m + 1) + 1), if h : j < i then F ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
  classical
  let B (i : Fin ((m + 1) + 1)) := if h : i < j then F ⟨(i : ℕ), by omega⟩ else 0
  let A (i : Fin ((m + 1) + 1)) := if h : j < i then F ⟨(i : ℕ) - 1, by omega⟩ else 0
  let G (i : Fin ((m + 1) + 1)) := B i + A i
  have hGj : G j = 0 := by simp [G, B, A]
  have hG (k : Fin (m + 1)) : G (j.succAbove k) = F k := by
    by_cases h : k.castSucc < j
    · rw [Fin.succAbove_of_castSucc_lt j k h]
      have h' : ¬ j < k.castSucc := not_lt_of_ge h.le
      simp only [G, B, A, dif_pos h, dif_neg h', add_zero]
      rfl
    · have h' : j ≤ k.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc j k h']
      have hlt : j < k.succ := lt_of_le_of_lt h' k.castSucc_lt_succ
      have hnlt : ¬ k.succ < j := not_lt_of_ge hlt.le
      simp only [G, B, A, dif_neg hnlt, dif_pos hlt, zero_add]
      rfl
  have hs := Fin.sum_univ_succAbove G j
  rw [hGj, zero_add] at hs
  simp only [hG] at hs
  calc
    (∑ k, F k) = ∑ i, G i := hs.symm
    _ = _ := Finset.sum_add_distrib

end EnvelopingIsomorphism.Deformation
