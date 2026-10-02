import EnvelopingIsomorphism.Deformation.PreLieExpansion
import EnvelopingIsomorphism.Deformation.InsertionPartition

/-!
The graded pre-Lie identity for genuine full cochains of positive arity.
Nested terms cancel using the inside-slot bijection.  The two disjoint regions
are exchanged by swapping the original outer slots, with the Koszul sign.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

def insertionBeforeSum (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    Curried R A ((m + n) + (r + 1)) :=
  ∑ i : Fin (m + 1), ∑ j : Fin (m + 1) with j < i,
    (((-1 : R) ^ (i.val * n)) * ((-1 : R) ^ (j.val * r))) •
      insertionTwice m n r f g h i ⟨j.val, by omega⟩

def insertionAfterSum (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    Curried R A ((m + n) + (r + 1)) :=
  ∑ i : Fin (m + 1), ∑ j : Fin (m + 1) with i < j,
    (((-1 : R) ^ (i.val * n)) * ((-1 : R) ^ ((j.val + n) * r))) •
      insertionTwice m n r f g h i ⟨j.val + n, by omega⟩

theorem curriedAssociator_eq_disjoint (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedAssociator m n r f g h =
      insertionBeforeSum m n r f g h + insertionAfterSum m n r f g h := by
  rw [curriedAssociator_eq_sum]
  have hrow (i : Fin (m + 1)) := sum_insertion_slots m n i
    (fun j => (((-1 : R) ^ (i.val * n)) * ((-1 : R) ^ (j.val * r))) •
      insertionTwice m n r f g h i j)
  simp only [insertionTwice_inside, insertionSign_nested] at hrow
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold insertionBeforeSum insertionAfterSum
  abel

theorem insertionBeforeSum_swap (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    insertionBeforeSum m n r f g h = (-1 : R) ^ (n * r) •
      curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
        (insertionAfterSum m r n f h g) := by
  unfold insertionBeforeSum insertionAfterSum
  simp only [map_sum, Finset.smul_sum, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hji
  · rw [insertionTwice_before m n r f g h i j hji,
      insertionSign_before i.val j.val n r]
    simp only [map_smul, smul_smul]
  · simp only [map_zero, smul_zero]

theorem insertionAfterSum_swap (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    insertionAfterSum m n r f g h = (-1 : R) ^ (n * r) •
      curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
        (insertionBeforeSum m r n f h g) := by
  unfold insertionBeforeSum insertionAfterSum
  simp only [map_sum, Finset.smul_sum, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · rw [insertionTwice_after m n r f g h i j hij,
      insertionSign_after i.val j.val n r]
    simp only [map_smul, smul_smul]
  · simp only [map_zero, smul_zero]

/-- The Gerstenhaber insertion product satisfies the graded pre-Lie identity. -/
theorem curriedAssociator_graded_symm (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedAssociator m n r f g h = (-1 : R) ^ (n * r) •
      curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
        (curriedAssociator m r n f h g) := by
  rw [curriedAssociator_eq_disjoint, curriedAssociator_eq_disjoint, map_add, smul_add,
    insertionBeforeSum_swap m n r f g h, insertionAfterSum_swap m n r f g h]
  exact add_comm _ _

end EnvelopingIsomorphism.Deformation
