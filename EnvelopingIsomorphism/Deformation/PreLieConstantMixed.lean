import EnvelopingIsomorphism.Deformation.PreLieConstants
import EnvelopingIsomorphism.Deformation.InsertionConstantPartition

/-! Mixed positive/constant boundary of the actual graded pre-Lie law. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

def insertionPositiveThenConstant (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (g : Curried R A (r + 1)) (a : A)
    (i : Fin ((m + 1) + 1)) (j : Fin (((m + 1) + r) + 1)) : Curried R A ((m + 1) + r) :=
  curriedInsertAt ((m + 1) + r) 0 j (curriedInsertAt (m + 1) (r + 1) i f g) a

def insertionConstantThenPositive (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (a : A) (g : Curried R A (r + 1))
    (j : Fin ((m + 1) + 1)) (i : Fin (m + 1)) : Curried R A ((m + 1) + r) :=
  curriedCongr (Nat.add_right_comm m r 1)
    (curriedInsertAt m (r + 1) i (curriedInsertAt (m + 1) 0 j f a) g)

theorem insertionPositiveThenConstant_inside (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A (r + 1)) (a : A)
    (i : Fin ((m + 1) + 1)) (j : Fin (r + 1)) :
    insertionPositiveThenConstant m r f g a i ⟨i.val + j.val, by omega⟩ =
      curriedInsertAt (m + 1) r i f (curriedInsertAt r 0 j g a) := by
  convert curriedInsertAt_nested (m + 1) r 0 i j f g a using 1 <;> rfl

theorem insertionPositiveThenConstant_after (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A (r + 1)) (a : A)
    (i j : Fin ((m + 1) + 1)) (hij : i < j) :
    insertionPositiveThenConstant m r f g a i ⟨j.val + r, by omega⟩ =
      insertionConstantThenPositive m r f a g j ⟨i.val, by omega⟩ := by
  have hd := curriedInsertAt_disjoint m (r + 1) 0 i j hij f g a
  have hl := curriedInsertAt_heq (by omega : (m + 1) + r = m + (r + 1)) (rfl : 0 = 0)
    (⟨j.val + r, by omega⟩ : Fin (((m + 1) + r) + 1))
    (⟨j.val + (r + 1) - 1, by omega⟩ : Fin ((m + (r + 1)) + 1))
    (by change j.val + r = j.val + (r + 1) - 1; omega)
    (curriedInsertAt (m + 1) (r + 1) i f g)
    (curriedCongr (Nat.add_right_comm m 1 (r + 1)) (curriedInsertAt (m + 1) (r + 1) i f g))
    (curriedCongr_heq _ _).symm a a HEq.rfl
  have hr := curriedInsertAt_heq (by omega : m + 0 = m) (rfl : r + 1 = r + 1)
    (⟨i.val, by omega⟩ : Fin ((m + 0) + 1)) (⟨i.val, by omega⟩ : Fin (m + 1)) rfl
    (curriedCongr (Nat.add_right_comm m 1 0) (curriedInsertAt (m + 1) 0 j f a))
    (curriedInsertAt (m + 1) 0 j f a) (curriedCongr_heq _ _) g g HEq.rfl
  exact eq_of_heq (hl.trans ((curriedCongr_heq (Nat.add_right_comm m (r + 1) 0) _).symm.trans
    ((heq_of_eq hd).trans (hr.trans (curriedCongr_heq (Nat.add_right_comm m r 1) _).symm))))

theorem insertionPositiveThenConstant_before (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A (r + 1)) (a : A)
    (i j : Fin ((m + 1) + 1)) (hji : j < i) :
    insertionPositiveThenConstant m r f g a i ⟨j.val, by omega⟩ =
      insertionConstantThenPositive m r f a g j ⟨i.val - 1, by omega⟩ := by
  have hd := curriedInsertAt_before m (r + 1) 0 i j hji f g a
  have hl := curriedInsertAt_heq (by omega : (m + 1) + r = m + (r + 1)) (rfl : 0 = 0)
    (⟨j.val, by omega⟩ : Fin (((m + 1) + r) + 1))
    (⟨j.val, by omega⟩ : Fin ((m + (r + 1)) + 1)) rfl
    (curriedInsertAt (m + 1) (r + 1) i f g)
    (curriedCongr (Nat.add_right_comm m 1 (r + 1)) (curriedInsertAt (m + 1) (r + 1) i f g))
    (curriedCongr_heq _ _).symm a a HEq.rfl
  have hr := curriedInsertAt_heq (by omega : m + 0 = m) (rfl : r + 1 = r + 1)
    (⟨i.val + 0 - 1, by omega⟩ : Fin ((m + 0) + 1))
    (⟨i.val - 1, by omega⟩ : Fin (m + 1)) rfl
    (curriedCongr (Nat.add_right_comm m 1 0) (curriedInsertAt (m + 1) 0 j f a))
    (curriedInsertAt (m + 1) 0 j f a) (curriedCongr_heq _ _) g g HEq.rfl
  exact eq_of_heq (hl.trans ((curriedCongr_heq (Nat.add_right_comm m (r + 1) 0) _).symm.trans
    ((heq_of_eq hd).trans (hr.trans (curriedCongr_heq (Nat.add_right_comm m r 1) _).symm))))

def curriedConstantAssociator (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (g : Curried R A (r + 1)) (a : A) : Curried R A ((m + 1) + r) :=
  curriedPreLie 0 ((m + 1) + r) (curriedPreLie (r + 1) (m + 1) f g) a -
    curriedPreLie r (m + 1) f (curriedPreLie 0 r g a)

theorem curriedConstantAssociator_eq_sum (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A (r + 1)) (a : A) :
    curriedConstantAssociator m r f g a =
      (∑ i : Fin ((m + 1) + 1), ∑ j : Fin (((m + 1) + r) + 1),
        ((-1 : R) ^ (i.val * r) * (-1 : R) ^ j.val) •
          insertionPositiveThenConstant m r f g a i j) -
      (∑ i : Fin ((m + 1) + 1), ∑ j : Fin (r + 1),
        ((-1 : R) ^ (i.val * (r + 1)) * (-1 : R) ^ j.val) •
          curriedInsertAt (m + 1) r i f (curriedInsertAt r 0 j g a)) := by
  unfold curriedConstantAssociator
  congr 1
  · rw [curriedPreLie_pos_eq_sum (m + 1) r]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    simp_rw [curriedPreLie_eq_sum_apply ((m + 1) + r) 0]
    simp only [Nat.zero_add, Nat.mul_one, Finset.smul_sum, smul_smul]
    rfl
  · rw [curriedPreLie_eq_sum_apply (m + 1) r]
    simp_rw [curriedPreLie_eq_sum_apply r 0]
    simp only [Nat.zero_add, Nat.mul_one, map_sum, map_smul, Finset.smul_sum, smul_smul]

def constantBeforeSum (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (g : Curried R A (r + 1)) (a : A) : Curried R A ((m + 1) + r) :=
  ∑ i : Fin ((m + 1) + 1), ∑ j : Fin ((m + 1) + 1) with j < i,
    ((-1 : R) ^ (i.val * r) * (-1 : R) ^ j.val) •
      insertionPositiveThenConstant m r f g a i ⟨j.val, by omega⟩

def constantAfterSum (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (g : Curried R A (r + 1)) (a : A) : Curried R A ((m + 1) + r) :=
  ∑ i : Fin ((m + 1) + 1), ∑ j : Fin ((m + 1) + 1) with i < j,
    ((-1 : R) ^ (i.val * r) * (-1 : R) ^ (j.val + r)) •
      insertionPositiveThenConstant m r f g a i ⟨j.val + r, by omega⟩

theorem curriedConstantAssociator_eq_disjoint (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A (r + 1)) (a : A) :
    curriedConstantAssociator m r f g a = constantBeforeSum m r f g a + constantAfterSum m r f g a := by
  rw [curriedConstantAssociator_eq_sum]
  have hrow (i : Fin ((m + 1) + 1)) := sum_insertion_slots (m + 1) r i
    (fun j ↦ ((-1 : R) ^ (i.val * r) * (-1 : R) ^ j.val) •
      insertionPositiveThenConstant m r f g a i j)
  have hsign (i j : ℕ) : (-1 : R) ^ (i * r) * (-1 : R) ^ (i + j) =
      (-1 : R) ^ (i * (r + 1)) * (-1 : R) ^ j := by
    simpa only [Nat.mul_one] using insertionSign_nested (R := R) i j r 1
  simp only [insertionPositiveThenConstant_inside, hsign] at hrow
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold constantBeforeSum constantAfterSum
  abel

theorem constantFirst_eq_sum (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (a : A) (g : Curried R A (r + 1)) :
    curriedCongr (Nat.add_right_comm m r 1)
      (curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g) =
      ∑ j : Fin ((m + 1) + 1), ∑ i : Fin (m + 1),
        ((-1 : R) ^ j.val * (-1 : R) ^ (i.val * r)) •
          insertionConstantThenPositive m r f a g j i := by
  rw [curriedPreLie_eq_sum_apply (m + 1) 0]
  simp only [Nat.zero_add, Nat.mul_one, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [curriedPreLie_pos_eq_sum m r]
  simp only [Finset.smul_sum, map_sum, map_smul, smul_smul]
  rfl

theorem insertionSign_constant_before (i j r : ℕ) (hi : 0 < i) :
    (-1 : R) ^ r * ((-1 : R) ^ j * (-1 : R) ^ ((i - 1) * r)) =
      (-1 : R) ^ (i * r) * (-1 : R) ^ j := by
  have hp : i * r = (i - 1) * r + r := by
    calc
      i * r = ((i - 1) + 1) * r := congrArg (· * r) (by omega)
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]
  rw [hp, pow_add]
  ac_rfl

theorem insertionSign_constant_after (i j r : ℕ) :
    (-1 : R) ^ r * ((-1 : R) ^ j * (-1 : R) ^ (i * r)) =
      (-1 : R) ^ (i * r) * (-1 : R) ^ (j + r) := by
  rw [pow_add]
  ac_rfl

theorem constantFirst_signed_eq_disjoint (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (a : A) (g : Curried R A (r + 1)) :
    (-1 : R) ^ r • curriedCongr (Nat.add_right_comm m r 1)
      (curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g) =
      constantAfterSum m r f g a + constantBeforeSum m r f g a := by
  rw [constantFirst_eq_sum]
  simp only [Finset.smul_sum, smul_smul]
  have hrow (j : Fin ((m + 1) + 1)) := sum_deleted_slot m j
    (fun i ↦ ((-1 : R) ^ r * ((-1 : R) ^ j.val * (-1 : R) ^ (i.val * r))) •
      insertionConstantThenPositive m r f a g j i)
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  congr 1
  · unfold constantAfterSum
    rw [Finset.sum_comm]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · rw [insertionPositiveThenConstant_after m r f g a i j hij]
      rw [insertionSign_constant_after]
    · rfl
  · unfold constantBeforeSum
    rw [Finset.sum_comm]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hji
    · rw [insertionPositiveThenConstant_before m r f g a i j hji]
      rw [insertionSign_constant_before i.val j.val r (by omega)]
    · rfl

/-- Mixed associator form of the graded pre-Lie law, with one inner cochain constant. -/
theorem curriedConstantAssociator_signed (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (g : Curried R A (r + 1)) (a : A) :
    curriedConstantAssociator m r f g a =
      (-1 : R) ^ r • curriedCongr (Nat.add_right_comm m r 1)
        (curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g) := by
  rw [curriedConstantAssociator_eq_disjoint, constantFirst_signed_eq_disjoint]
  exact add_comm _ _

/-- The requested constant-first form, including unary positive inner cochains (r=0). -/
theorem curriedPreLie_constant_mixed (m r : ℕ) (f : Curried R A ((m + 1) + 1))
    (a : A) (g : Curried R A (r + 1)) :
    curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g =
      (-1 : R) ^ r • curriedCongr (Nat.add_right_comm m 1 r)
        (curriedPreLie 0 ((m + 1) + r) (curriedPreLie (r + 1) (m + 1) f g) a -
          curriedPreLie r (m + 1) f (curriedPreLie 0 r g a)) := by
  have h := congrArg
    (fun z : Curried R A ((m + 1) + r) ↦
      (-1 : R) ^ r • curriedCongr (Nat.add_right_comm m 1 r) z)
    (curriedConstantAssociator_signed m r f g a)
  simp only [map_smul, smul_smul, insertionSign_square, one_smul] at h
  have hcancel :
      curriedCongr (Nat.add_right_comm m 1 r)
        (curriedCongr (Nat.add_right_comm m r 1)
          (curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g)) =
      curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g :=
    (curriedCongr_trans (Nat.add_right_comm m r 1) (Nat.add_right_comm m 1 r) _).trans rfl
  rw [hcancel] at h
  exact h.symm

end EnvelopingIsomorphism.Deformation
