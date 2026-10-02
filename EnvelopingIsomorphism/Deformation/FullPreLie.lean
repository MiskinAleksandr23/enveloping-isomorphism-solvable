import EnvelopingIsomorphism.Deformation.FullSymmetry

/-! The insertion product in integer degrees; zero-ary outer cochains have no slots. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

def fullPreLie : (p q : ℤ) → FullCochain R A p →ₗ[R] FullCochain R A q →ₗ[R]
    FullCochain R A (p + q)
  | .ofNat m, .ofNat n => curriedPreLie (n + 1) m
  | .ofNat 0, .negSucc 0 => curriedPreLie 0 0
  | .ofNat (m + 1), .negSucc 0 => (curriedPreLie 0 (m + 1)).compr₂
      (fullCochainCongr (show Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 by
        change (m : ℤ) = ((m : ℤ) + 1) + (-1)
        omega)).toLinearMap
  | .negSucc _, _ => 0
  | _, .negSucc (_ + 1) => 0

@[simp] theorem fullPreLie_nat (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) :
    fullPreLie (m : ℤ) (n : ℤ) f g = curriedPreLie (n + 1) m f g := rfl

@[simp] theorem fullPreLie_constant_outer (q : ℤ) (a : A) (f : FullCochain R A q) :
    fullPreLie (-1) q a f = 0 := rfl

@[simp] theorem fullPreLie_neg_outer (n : ℕ) (q : ℤ)
    (f : FullCochain R A (Int.negSucc n)) (g : FullCochain R A q) :
    fullPreLie (Int.negSucc n) q f g = 0 := rfl

@[simp] theorem fullPreLie_below_left (n : ℕ) (q : ℤ)
    (f : FullCochain R A (Int.negSucc (n + 1))) (g : FullCochain R A q) :
    fullPreLie (Int.negSucc (n + 1)) q f g = 0 := rfl

@[simp] theorem fullPreLie_below_right (p : ℤ) (n : ℕ)
    (f : FullCochain R A p) (g : FullCochain R A (Int.negSucc (n + 1))) :
    fullPreLie p (Int.negSucc (n + 1)) f g = 0 := by
  cases p with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

@[simp] theorem fullPreLie_zero_left (p q : ℤ) (g : FullCochain R A q) :
    fullPreLie p q (0 : FullCochain R A p) g = 0 := by rw [map_zero, LinearMap.zero_apply]

@[simp] theorem fullPreLie_zero_right (p q : ℤ) (f : FullCochain R A p) :
    fullPreLie p q f (0 : FullCochain R A q) = 0 := map_zero _

theorem fullBracket_nat_constant_eq_preLie (m : ℕ) (f : Curried R A (m + 1)) (a : A) :
    fullBracket (m : ℤ) (-1) f a = fullPreLie (m : ℤ) (-1) f a := by
  cases m <;> rfl

theorem fullBracket_constant_nat_eq_preLie (m : ℕ) (a : A) (f : Curried R A (m + 1)) :
    fullBracket (-1) (m : ℤ) a f = -((-1 : R) ^ m) •
      fullCochainCongr (add_comm (m : ℤ) (-1)) (fullPreLie (m : ℤ) (-1) f a) := by
  cases m with
  | zero =>
    change -(f a) = -((-1 : R) ^ 0) • f a
    simp
  | succ m =>
    have hl : Int.ofNat m = Int.negSucc 0 + Int.ofNat (m + 1) := by
      change (m : ℤ) = (-1) + ((m : ℤ) + 1)
      omega
    have hr : Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 := by
      change (m : ℤ) = ((m : ℤ) + 1) + (-1)
      omega
    change fullCochainCongr hl (-((-1 : R) ^ (m + 1)) • curriedPreLie 0 (m + 1) f a) =
      -((-1 : R) ^ (m + 1)) • fullCochainCongr (add_comm _ _)
        (fullCochainCongr hr (curriedPreLie 0 (m + 1) f a))
    rw [fullCochainCongr_trans, map_smul]

/-- The full bracket is exactly the signed commutator of the actual insertion operation. -/
theorem fullBracket_eq_preLie (p q : ℤ) (f : FullCochain R A p) (g : FullCochain R A q) :
    fullBracket p q f g = fullPreLie p q f g - koszulSign R p q •
      fullCochainCongr (add_comm q p) (fullPreLie q p g f) := by
  cases p with
  | ofNat m =>
    cases q with
    | ofNat n =>
      have hc := fullCochainCongr_nat (R := R) (A := A)
        (congrArg Int.ofNat (Nat.add_comm n m)) (curriedPreLie (m + 1) n g f)
      have hk : koszulSign R (Int.ofNat m) (Int.ofNat n) = (-1 : R) ^ (m * n) :=
        koszulSign_nat (R := R) m n
      change curriedBracket m n f g = curriedPreLie (n + 1) m f g -
        koszulSign R (Int.ofNat m) (Int.ofNat n) •
          fullCochainCongr (congrArg Int.ofNat (Nat.add_comm n m)) (curriedPreLie (m + 1) n g f)
      rw [hc, hk]
      rfl
    | negSucc n =>
      cases n with
      | zero =>
        have hz : fullPreLie (Int.negSucc 0) (Int.ofNat m) g f = 0 := rfl
        rw [hz, map_zero, smul_zero, sub_zero]
        exact fullBracket_nat_constant_eq_preLie m f g
      | succ n =>
        rw [fullBracket_below_right, fullPreLie_below_right, fullPreLie_below_left]
        simp only [map_zero, smul_zero, sub_zero]
  | negSucc m =>
    cases m with
    | zero =>
      cases q with
      | ofNat n =>
        have hk : koszulSign R (Int.negSucc 0) (Int.ofNat n) = (-1 : R) ^ n :=
          koszulSign_neg_one_nat (R := R) n
        have hz : fullPreLie (Int.negSucc 0) (Int.ofNat n) f g = 0 := rfl
        rw [hz, zero_sub, ← neg_smul, hk]
        exact fullBracket_constant_nat_eq_preLie n f g
      | negSucc n =>
        cases n with
        | zero =>
          change (0 : PUnit.{v + 1}) = _
          exact Subsingleton.elim _ _
        | succ n =>
          rw [fullBracket_below_right, fullPreLie_below_right, fullPreLie_below_left]
          simp only [map_zero, smul_zero, sub_zero]
    | succ m =>
      rw [fullBracket_below_left, fullPreLie_below_left, fullPreLie_below_right]
      simp only [map_zero, smul_zero, sub_zero]

end EnvelopingIsomorphism.Deformation
