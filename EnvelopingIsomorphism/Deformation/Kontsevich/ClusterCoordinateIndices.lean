import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! Finite free-coordinate labels for one normalized interior cluster. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

/-- Coarse interior coordinates retain the cluster representative and all
outside labels, then remove the global normalization anchor. -/
def ClusterCoarseIndex {n : ℕ} (i a : Fin n) (S : Finset (Fin n)) :=
  {j : Fin n // (j = a ∨ j ∉ S) ∧ j ≠ i}

/-- Shape coordinates remove both normalization labels from the cluster. -/
def ClusterShapeIndex {n : ℕ} (a b : Fin n) (S : Finset (Fin n)) :=
  {j : Fin n // j ∈ S ∧ j ≠ a ∧ j ≠ b}

instance {n : ℕ} (i a : Fin n) (S : Finset (Fin n)) : Fintype (ClusterCoarseIndex i a S) :=
  inferInstanceAs (Fintype {j : Fin n // (j = a ∨ j ∉ S) ∧ j ≠ i})

instance {n : ℕ} (a b : Fin n) (S : Finset (Fin n)) : Fintype (ClusterShapeIndex a b S) :=
  inferInstanceAs (Fintype {j : Fin n // j ∈ S ∧ j ≠ a ∧ j ≠ b})

/-- The coarse count holds whether the global anchor is in or outside S. -/
theorem card_clusterCoarseIndex {n : ℕ} (i a : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) (hanchor : i ∈ S → a = i) :
    Fintype.card (ClusterCoarseIndex i a S) = n - S.card := by
  have hcard : Fintype.card (ClusterCoarseIndex i a S) = ((insert a Sᶜ).erase i).card := by
    apply Fintype.card_of_subtype
    intro j
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_compl, and_comm]
  have ha' : a ∉ Sᶜ := by simpa using ha
  have hi : i ∈ insert a Sᶜ := by
    by_cases hiS : i ∈ S
    · rw [hanchor hiS]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_compl.mpr hiS)
  rw [hcard, Finset.card_erase_of_mem hi, Finset.card_insert_of_notMem ha',
    Nat.add_sub_cancel_right, Finset.card_compl, Fintype.card_fin]

/-- The two distinct marked cluster labels account for exactly two coordinates. -/
theorem card_clusterShapeIndex {n : ℕ} (a b : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    Fintype.card (ClusterShapeIndex a b S) = S.card - 2 := by
  have hcard : Fintype.card (ClusterShapeIndex a b S) = ((S.erase a).erase b).card := by
    apply Fintype.card_of_subtype
    intro j
    simp only [Finset.mem_erase, and_comm, and_left_comm, and_assoc]
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
  rw [hcard, Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha, Nat.sub_sub]

end EnvelopingIsomorphism.Deformation.Kontsevich
