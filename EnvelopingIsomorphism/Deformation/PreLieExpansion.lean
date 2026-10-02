import EnvelopingIsomorphism.Deformation.InsertionAtComposition
import EnvelopingIsomorphism.Deformation.InsertionSigns

/-! Finite double-sum expansion of the genuine Gerstenhaber associator. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Apply two partial insertions consecutively, using a fixed parenthesization of total arity. -/
def insertionTwice (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1))
    (i : Fin (m + 1)) (j : Fin ((m + n) + 1)) : Curried R A ((m + n) + (r + 1)) :=
  curriedInsertAt (m + n) (r + 1) j (curriedInsertAt m (n + 1) i f g) h

/-- Insert into the inner operation first, transported to the same total arity. -/
def insertionNested (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1))
    (i : Fin (m + 1)) (j : Fin (n + 1)) : Curried R A ((m + n) + (r + 1)) :=
  curriedCongr (Nat.add_assoc m n (r + 1)).symm
    (curriedInsertAt m (n + (r + 1)) i f (curriedInsertAt n (r + 1) j g h))

theorem insertionTwice_inside (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1))
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    insertionTwice m n r f g h i ⟨i.val + j.val, by omega⟩ =
      insertionNested m n r f g h i j := by
  have hn := curriedInsertAt_nested m n (r + 1) i j f g h
  exact eq_of_heq ((curriedCongr_heq (Nat.add_assoc m n (r + 1)) _).symm.trans
    ((heq_of_eq hn).trans (curriedCongr_heq (Nat.add_assoc m n (r + 1)).symm _).symm))

theorem insertionTwice_after (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1))
    (i j : Fin (m + 1)) (hij : i < j) :
    insertionTwice m n r f g h i ⟨j.val + n, by omega⟩ =
      curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
        (insertionTwice m r n f h g j ⟨i.val, by omega⟩) := by
  cases m with
  | zero => have hi := i.isLt; have hj := j.isLt; omega
  | succ m =>
    have hd := curriedInsertAt_disjoint m (n + 1) (r + 1) i j hij f g h
    have hl := curriedInsertAt_heq (by omega : (m + 1) + n = m + (n + 1)) rfl
      (⟨j.val + n, by omega⟩ : Fin (((m + 1) + n) + 1))
      (⟨j.val + (n + 1) - 1, by omega⟩ : Fin ((m + (n + 1)) + 1))
      (by change j.val + n = j.val + (n + 1) - 1; omega)
      (curriedInsertAt (m + 1) (n + 1) i f g)
      (curriedCongr (Nat.add_right_comm m 1 (n + 1)) (curriedInsertAt (m + 1) (n + 1) i f g))
      (curriedCongr_heq _ _).symm h h HEq.rfl
    have hr := curriedInsertAt_heq (by omega : m + (r + 1) = (m + 1) + r) rfl
      (⟨i.val, by omega⟩ : Fin ((m + (r + 1)) + 1))
      (⟨i.val, by omega⟩ : Fin (((m + 1) + r) + 1)) rfl
      (curriedCongr (Nat.add_right_comm m 1 (r + 1)) (curriedInsertAt (m + 1) (r + 1) j f h))
      (curriedInsertAt (m + 1) (r + 1) j f h) (curriedCongr_heq _ _) g g HEq.rfl
    exact eq_of_heq (hl.trans ((curriedCongr_heq
      (Nat.add_right_comm m (n + 1) (r + 1)) _).symm.trans
        ((heq_of_eq hd).trans (hr.trans (curriedCongr_heq (by omega) _).symm))))

theorem insertionTwice_before (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1))
    (i j : Fin (m + 1)) (hji : j < i) :
    insertionTwice m n r f g h i ⟨j.val, by omega⟩ =
      curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
        (insertionTwice m r n f h g j ⟨i.val + r, by omega⟩) := by
  have hd := insertionTwice_after m r n f h g j i hji
  exact eq_of_heq (((heq_of_eq hd).trans (curriedCongr_heq (by omega) _)).symm.trans
    (curriedCongr_heq (by omega) _).symm)

/-- The associator of the signed insertion product in a fixed total arity. -/
def curriedAssociator (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    Curried R A ((m + n) + (r + 1)) :=
  curriedPreLie (r + 1) (m + n) (curriedPreLie (n + 1) m f g) h -
    curriedCongr (Nat.add_assoc m n (r + 1)).symm
      (curriedPreLie (n + (r + 1)) m f (curriedPreLie (r + 1) n g h))

theorem curriedAssociator_eq_sum (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedAssociator m n r f g h =
      (∑ i : Fin (m + 1), ∑ j : Fin ((m + n) + 1),
        (((-1 : R) ^ (i.val * n)) * ((-1 : R) ^ (j.val * r))) •
          insertionTwice m n r f g h i j) -
      (∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
        (((-1 : R) ^ (i.val * (n + r))) * ((-1 : R) ^ (j.val * r))) •
          insertionNested m n r f g h i j) := by
  unfold curriedAssociator
  congr 1
  · rw [curriedPreLie_pos_eq_sum m n]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    simp_rw [curriedPreLie_pos_eq_sum (m + n) r]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  · change curriedCongr (Nat.add_assoc m n (r + 1)).symm
      (curriedPreLie ((n + r) + 1) m f (curriedPreLie (r + 1) n g h)) = _
    rw [curriedPreLie_pos_eq_sum m (n + r)]
    simp_rw [curriedPreLie_pos_eq_sum n r]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
    rfl

end EnvelopingIsomorphism.Deformation
