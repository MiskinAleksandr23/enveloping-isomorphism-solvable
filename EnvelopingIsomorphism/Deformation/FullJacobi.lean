import EnvelopingIsomorphism.Deformation.FullBracket

/-! Integer-degree Jacobi identities and the vanishing pieces of the full complex. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

@[simp] theorem fullBracket_zero_left (p q : ℤ) (g : FullCochain R A q) :
    fullBracket p q (0 : FullCochain R A p) g = 0 := by
  rw [map_zero, LinearMap.zero_apply]

@[simp] theorem fullBracket_zero_right (p q : ℤ) (f : FullCochain R A p) :
    fullBracket p q f (0 : FullCochain R A q) = 0 := map_zero _

def fullJacobiator (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) : FullCochain R A ((p + q) + r) :=
  fullCochainCongr (add_assoc p q r).symm
    (fullBracket p (q + r) f (fullBracket q r g h)) -
      fullBracket (p + q) r (fullBracket p q f g) h -
    koszulSign R p q • fullCochainCongr (by omega : q + (p + r) = (p + q) + r)
      (fullBracket q (p + r) g (fullBracket p r f h))

theorem fullJacobiator_nat (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    fullJacobiator (m : ℤ) (n : ℤ) (r : ℤ) f g h = 0 := by
  have hL := fullCochainCongr_nat (R := R) (A := A)
    (congrArg Int.ofNat (Nat.add_assoc m n r).symm)
    (curriedBracket m (n + r) f (curriedBracket n r g h))
  have hR := fullCochainCongr_nat (R := R) (A := A)
    (congrArg Int.ofNat (show n + (m + r) = (m + n) + r by omega))
    (curriedBracket n (m + r) g (curriedBracket m r f h))
  have hK := koszulSign_nat (R := R) m n
  unfold fullJacobiator
  change fullCochainCongr (congrArg Int.ofNat (Nat.add_assoc m n r).symm)
      (curriedBracket m (n + r) f (curriedBracket n r g h)) -
      curriedBracket (m + n) r (curriedBracket m n f g) h -
    koszulSign R (m : ℤ) (n : ℤ) •
      fullCochainCongr (congrArg Int.ofNat (show n + (m + r) = (m + n) + r by omega))
        (curriedBracket n (m + r) g (curriedBracket m r f h)) = 0
  rw [hL, hR, hK]
  exact curriedJacobiator_zero m n r f g h

theorem fullJacobiator_below_first (n : ℕ) (q r : ℤ)
    (f : FullCochain R A (Int.negSucc (n + 1))) (g : FullCochain R A q)
    (h : FullCochain R A r) : fullJacobiator (Int.negSucc (n + 1)) q r f g h = 0 := by
  unfold fullJacobiator
  rw [fullBracket_below_left n (q + r) f (fullBracket q r g h),
    fullBracket_below_left n q f g, fullBracket_below_left n r f h,
    fullBracket_zero_left, fullBracket_zero_right]
  simp only [map_zero, smul_zero, sub_zero]

theorem fullJacobiator_below_second (p : ℤ) (n : ℕ) (r : ℤ)
    (f : FullCochain R A p) (g : FullCochain R A (Int.negSucc (n + 1)))
    (h : FullCochain R A r) : fullJacobiator p (Int.negSucc (n + 1)) r f g h = 0 := by
  unfold fullJacobiator
  rw [fullBracket_below_left n r g h, fullBracket_below_right p n f g,
    fullBracket_below_left n (p + r) g (fullBracket p r f h),
    fullBracket_zero_left, fullBracket_zero_right]
  simp only [map_zero, smul_zero, sub_zero]

theorem fullJacobiator_below_third (p q : ℤ) (n : ℕ)
    (f : FullCochain R A p) (g : FullCochain R A q)
    (h : FullCochain R A (Int.negSucc (n + 1))) :
    fullJacobiator p q (Int.negSucc (n + 1)) f g h = 0 := by
  unfold fullJacobiator
  rw [fullBracket_below_right q n g h,
    fullBracket_below_right (p + q) n (fullBracket p q f g) h,
    fullBracket_below_right p n f h, fullBracket_zero_right, fullBracket_zero_right]
  simp only [map_zero, smul_zero, sub_zero]

end EnvelopingIsomorphism.Deformation
