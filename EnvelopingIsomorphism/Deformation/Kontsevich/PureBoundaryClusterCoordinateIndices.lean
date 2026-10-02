import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-! The coordinates remaining after fixing the global interior anchor and
both endpoint shape coordinates of a pure boundary cluster. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

abbrev PureBoundaryInteriorIndex {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}
abbrev PureBoundaryFreeIndex {m : ℕ} (a b : Fin m) := {j : Fin m // j ≠ a ∧ j ≠ b}

theorem card_pureBoundaryInteriorIndex {n : ℕ} (i : Fin n) :
    Fintype.card (PureBoundaryInteriorIndex i) = n - 1 := by
  have h : Fintype.card (PureBoundaryInteriorIndex i) = (Finset.univ.erase i).card := by
    apply Fintype.card_of_subtype
    intro j
    simp
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem card_pureBoundaryFreeIndex {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    Fintype.card (PureBoundaryFreeIndex a b) = m - 2 := by
  have h : Fintype.card (PureBoundaryFreeIndex a b) = ((Finset.univ.erase a).erase b).card := by
    apply Fintype.card_of_subtype
    intro j
    simp [and_comm]
  rw [h, Finset.card_erase_of_mem (by simp [hab.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich
