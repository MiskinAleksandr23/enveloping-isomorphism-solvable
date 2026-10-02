import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! Finite free-coordinate labels for one real-boundary cluster. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

/-- Stationary interior labels outside the cluster, except for the global anchor. -/
def BoundaryClusterCoarseIndex {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :=
  {j : Fin n // j ∉ S ∧ j ≠ i}

/-- Interior shape labels in the cluster, except for its normalized anchor. -/
def BoundaryClusterShapeIndex {n : ℕ} (a : Fin n) (S : Finset (Fin n)) :=
  {j : Fin n // j ∈ S ∧ j ≠ a}

instance {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    Fintype (BoundaryClusterCoarseIndex i S) :=
  inferInstanceAs (Fintype {j : Fin n // j ∉ S ∧ j ≠ i})

instance {n : ℕ} (a : Fin n) (S : Finset (Fin n)) :
    Fintype (BoundaryClusterShapeIndex a S) :=
  inferInstanceAs (Fintype {j : Fin n // j ∈ S ∧ j ≠ a})

theorem card_boundaryClusterCoarseIndex {n : ℕ} (i : Fin n) (S : Finset (Fin n))
    (hi : i ∉ S) : Fintype.card (BoundaryClusterCoarseIndex i S) = n - S.card - 1 := by
  have hcard : Fintype.card (BoundaryClusterCoarseIndex i S) = (Sᶜ.erase i).card := by
    apply Fintype.card_of_subtype
    intro j
    simp only [Finset.mem_erase, Finset.mem_compl, and_comm]
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_compl.mpr hi),
    Finset.card_compl, Fintype.card_fin]

theorem card_boundaryClusterShapeIndex {n : ℕ} (a : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) : Fintype.card (BoundaryClusterShapeIndex a S) = S.card - 1 := by
  have hcard : Fintype.card (BoundaryClusterShapeIndex a S) = (S.erase a).card := by
    apply Fintype.card_of_subtype
    intro j
    simp only [Finset.mem_erase, and_comm]
  rw [hcard, Finset.card_erase_of_mem ha]

/-- The inside and outside anchors remove exactly two complex coordinates. -/
theorem card_boundaryClusterCoarseIndex_add_shapeIndex {n : ℕ}
    (i a : Fin n) (S : Finset (Fin n)) (hi : i ∉ S) (ha : a ∈ S) :
    Fintype.card (BoundaryClusterCoarseIndex i S) +
      Fintype.card (BoundaryClusterShapeIndex a S) = n - 2 := by
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hC : 0 < Sᶜ.card := Finset.card_pos.mpr ⟨i, Finset.mem_compl.mpr hi⟩
  rw [Finset.card_compl, Fintype.card_fin] at hC
  rw [card_boundaryClusterCoarseIndex i S hi, card_boundaryClusterShapeIndex a S ha]
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich
