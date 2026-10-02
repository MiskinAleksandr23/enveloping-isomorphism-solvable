import EnvelopingIsomorphism.Deformation.FullPreLie

/-! The insertion associator with genuine integer degrees and its established cases. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

theorem fullPreLie_cast_left {p p' q : ℤ} (hp : p = p')
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullPreLie p' q (fullCochainCongr hp f) g =
      fullCochainCongr (congrArg (· + q) hp) (fullPreLie p q f g) := by
  subst p'
  rfl

theorem fullPreLie_cast_right {p q q' : ℤ} (hq : q = q')
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullPreLie p q' f (fullCochainCongr hq g) =
      fullCochainCongr (congrArg (p + ·) hq) (fullPreLie p q f g) := by
  subst q'
  rfl

def fullAssociator (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) : FullCochain R A ((p + q) + r) :=
  fullPreLie (p + q) r (fullPreLie p q f g) h -
    fullCochainCongr (add_assoc p q r).symm (fullPreLie p (q + r) f (fullPreLie q r g h))

theorem fullAssociator_nat (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    fullAssociator (m : ℤ) (n : ℤ) (r : ℤ) f g h = curriedAssociator m n r f g h := by
  have hc := fullCochainCongr_nat (R := R) (A := A)
    (congrArg Int.ofNat (Nat.add_assoc m n r).symm)
    (curriedPreLie (n + (r + 1)) m f (curriedPreLie (r + 1) n g h))
  change curriedPreLie (r + 1) (m + n) (curriedPreLie (n + 1) m f g) h -
      fullCochainCongr (congrArg Int.ofNat (Nat.add_assoc m n r).symm)
        (curriedPreLie (n + (r + 1)) m f (curriedPreLie (r + 1) n g h)) = _
  rw [hc]
  rfl

theorem fullAssociator_nat_symm (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    fullAssociator (m : ℤ) (n : ℤ) (r : ℤ) f g h = koszulSign R n r •
      fullCochainCongr (by omega : (((m : ℤ) + r) + n) = ((m : ℤ) + n) + r)
        (fullAssociator (m : ℤ) (r : ℤ) (n : ℤ) f h g) := by
  rw [fullAssociator_nat, fullAssociator_nat, koszulSign_nat]
  have hc := fullCochainCongr_nat (R := R) (A := A)
    (congrArg Int.ofNat (Nat.add_right_comm m r n)) (curriedAssociator m r n f h g)
  change curriedAssociator m n r f g h = (-1 : R) ^ (n * r) •
    fullCochainCongr (congrArg Int.ofNat (Nat.add_right_comm m r n)) (curriedAssociator m r n f h g)
  rw [hc]
  exact curriedAssociator_graded_symm m n r f g h

theorem fullAssociator_neg_outer (n : ℕ) (q r : ℤ)
    (f : FullCochain R A (Int.negSucc n)) (g : FullCochain R A q) (h : FullCochain R A r) :
    fullAssociator (Int.negSucc n) q r f g h = 0 := by
  unfold fullAssociator
  rw [fullPreLie_neg_outer n q f g, fullPreLie_zero_left,
    fullPreLie_neg_outer n (q + r) f (fullPreLie q r g h), map_zero, sub_self]

theorem fullAssociator_below_second (p : ℤ) (n : ℕ) (r : ℤ)
    (f : FullCochain R A p) (g : FullCochain R A (Int.negSucc (n + 1))) (h : FullCochain R A r) :
    fullAssociator p (Int.negSucc (n + 1)) r f g h = 0 := by
  unfold fullAssociator
  rw [fullPreLie_below_right p n f g, fullPreLie_zero_left,
    fullPreLie_neg_outer (n + 1) r g h, fullPreLie_zero_right, map_zero, sub_self]

theorem fullAssociator_below_third (p q : ℤ) (n : ℕ)
    (f : FullCochain R A p) (g : FullCochain R A q) (h : FullCochain R A (Int.negSucc (n + 1))) :
    fullAssociator p q (Int.negSucc (n + 1)) f g h = 0 := by
  unfold fullAssociator
  rw [fullPreLie_below_right (p + q) n (fullPreLie p q f g) h,
    fullPreLie_below_right q n g h, fullPreLie_zero_right, map_zero, sub_self]

end EnvelopingIsomorphism.Deformation
