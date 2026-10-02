import EnvelopingIsomorphism.Deformation.FullHochschild

/-! The actual Gerstenhaber bracket in all integer degrees, retaining degree -1. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

def fullCochainCongr {p q : ℤ} (h : p = q) : FullCochain R A p ≃ₗ[R] FullCochain R A q :=
  h ▸ LinearEquiv.refl R (FullCochain R A p)

@[simp] theorem fullCochainCongr_self {p : ℤ} (h : p = p) (f : FullCochain R A p) :
    fullCochainCongr h f = f := by cases h; rfl

theorem fullCochainCongr_heq {p q : ℤ} (h : p = q) (f : FullCochain R A p) :
    HEq (fullCochainCongr h f) f := by cases h; rfl

theorem fullCochainCongr_smul_heq {p q : ℤ} (h : p = q) (c : R)
    (f : FullCochain R A p) : HEq (c • fullCochainCongr h f) (c • f) := by
  rw [← map_smul]
  exact fullCochainCongr_heq h (c • f)

theorem fullCochain_zero_heq {p q : ℤ} (h : p = q) :
    HEq (0 : FullCochain R A p) (0 : FullCochain R A q) := by cases h; rfl

@[simp] theorem fullCochainCongr_trans {p q r : ℤ} (h : p = q) (h' : q = r)
    (f : FullCochain R A p) :
    fullCochainCongr h' (fullCochainCongr h f) = fullCochainCongr (h.trans h') f := by
  subst q
  subst r
  rfl

theorem fullCochainCongr_nat {m n : ℕ} (h : (m : ℤ) = (n : ℤ)) (f : Curried R A (m + 1)) :
    fullCochainCongr h f = curriedCongr (congrArg (· + 1) (Int.ofNat.inj h)) f := by
  have hm := Int.ofNat.inj h
  subst n
  rfl

/-- The Koszul sign with genuine integer degrees, using Mathlib's integer-unit power. -/
def koszulSign (R : Type u) [CommRing R] (p q : ℤ) : R := ((p * q).negOnePow : R)

@[simp] theorem koszulSign_nat (m n : ℕ) :
    koszulSign R (m : ℤ) (n : ℤ) = (-1 : R) ^ (m * n) := by
  unfold koszulSign
  rw [← Int.natCast_mul, Int.cast_negOnePow_natCast]

@[simp] theorem koszulSign_neg_one_nat (n : ℕ) :
    koszulSign R (-1) (n : ℤ) = (-1 : R) ^ n := by
  unfold koszulSign
  rw [neg_one_mul, Int.negOnePow_neg, Int.cast_negOnePow_natCast]

theorem koszulSign_comm (p q : ℤ) : koszulSign R p q = koszulSign R q p := by
  unfold koszulSign
  rw [mul_comm]

@[simp] theorem koszulSign_nat_neg_one (m : ℕ) :
    koszulSign R (m : ℤ) (-1) = (-1 : R) ^ m := by
  rw [koszulSign_comm, koszulSign_neg_one_nat]

/-- Gerstenhaber bracket: positive arities, constant insertions, and zero below degree -1. -/
def fullBracket : (p q : ℤ) → FullCochain R A p →ₗ[R] FullCochain R A q →ₗ[R]
    FullCochain R A (p + q)
  | .ofNat m, .ofNat n => curriedBracketLinear m n
  | .ofNat 0, .negSucc 0 => curriedPreLie 0 0
  | .ofNat (m + 1), .negSucc 0 => (curriedPreLie 0 (m + 1)).compr₂
      (fullCochainCongr (show Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 by
        change (m : ℤ) = ((m : ℤ) + 1) + (-1)
        omega)).toLinearMap
  | .negSucc 0, .ofNat 0 => -(curriedPreLie 0 0).flip
  | .negSucc 0, .ofNat (n + 1) =>
      (-((-1 : R) ^ (n + 1)) • (curriedPreLie 0 (n + 1)).flip).compr₂
        (fullCochainCongr (show Int.ofNat n = Int.negSucc 0 + Int.ofNat (n + 1) by
          change (n : ℤ) = (-1) + ((n : ℤ) + 1)
          omega)).toLinearMap
  | .negSucc 0, .negSucc 0 => 0
  | .negSucc (_ + 1), _ => 0
  | _, .negSucc (_ + 1) => 0

@[simp] theorem fullBracket_nat (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) :
    fullBracket (m : ℤ) (n : ℤ) f g = curriedBracket m n f g := rfl

@[simp] theorem fullBracket_constants (a b : A) :
    fullBracket (R := R) (-1) (-1) a b = 0 := rfl

@[simp] theorem fullBracket_nat_constant (m : ℕ) (f : Curried R A (m + 1)) (a : A) :
    HEq (fullBracket (m : ℤ) (-1) f a) (curriedBracketConstant m f a) := by
  cases m with
  | zero => rfl
  | succ m =>
    exact fullCochainCongr_heq (R := R) (A := A)
      (show Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 by
        change (m : ℤ) = ((m : ℤ) + 1) + (-1)
        omega) (curriedBracketConstant (m + 1) f a)

@[simp] theorem fullBracket_constant_nat (n : ℕ) (a : A) (f : Curried R A (n + 1)) :
    HEq (fullBracket (-1) (n : ℤ) a f) (curriedConstantBracket n a f) := by
  cases n with
  | zero =>
    change HEq (-(f a)) (-((-1 : R) ^ 0) • f a)
    simp
  | succ n =>
    exact fullCochainCongr_heq (R := R) (A := A)
      (show Int.ofNat n = Int.negSucc 0 + Int.ofNat (n + 1) by
        change (n : ℤ) = (-1) + ((n : ℤ) + 1)
        omega) (curriedConstantBracket (n + 1) a f)

@[simp] theorem fullBracket_below_left (n : ℕ) (q : ℤ)
    (f : FullCochain R A (Int.negSucc (n + 1))) (g : FullCochain R A q) :
    fullBracket (Int.negSucc (n + 1)) q f g = 0 := by
  cases q with
  | ofNat m => cases m <;> rfl
  | negSucc m => cases m <;> rfl

@[simp] theorem fullBracket_below_right (p : ℤ) (n : ℕ)
    (f : FullCochain R A p) (g : FullCochain R A (Int.negSucc (n + 1))) :
    fullBracket p (Int.negSucc (n + 1)) f g = 0 := by
  cases p with
  | ofNat m => cases m <;> rfl
  | negSucc m => cases m <;> rfl

theorem fullBracket_nat_constant_skew (m : ℕ) (f : Curried R A (m + 1)) (a : A) :
    HEq (fullBracket (m : ℤ) (-1) f a)
      (-((-1 : R) ^ m) • fullBracket (-1) (m : ℤ) a f) := by
  cases m with
  | zero =>
    apply heq_of_eq
    change f a = -((-1 : R) ^ 0) • -(f a)
    simp
  | succ m =>
    have hl : Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 := by
      change (m : ℤ) = ((m : ℤ) + 1) + (-1)
      omega
    have hr : Int.ofNat m = Int.negSucc 0 + Int.ofNat (m + 1) := by
      change (m : ℤ) = (-1) + ((m : ℤ) + 1)
      omega
    let B := curriedBracketConstant (m + 1) f a
    have hs : -((-1 : R) ^ (m + 1)) • (-((-1 : R) ^ (m + 1)) • B) = B := by
      rw [smul_smul, neg_mul_neg, insertionSign_square, one_smul]
    exact (fullCochainCongr_heq hl B).trans ((heq_of_eq hs.symm).trans
      (fullCochainCongr_smul_heq hr (-((-1 : R) ^ (m + 1)))
        (-((-1 : R) ^ (m + 1)) • B)).symm)

theorem fullBracket_constant_nat_skew (m : ℕ) (a : A) (f : Curried R A (m + 1)) :
    HEq (fullBracket (-1) (m : ℤ) a f)
      (-((-1 : R) ^ m) • fullBracket (m : ℤ) (-1) f a) := by
  cases m with
  | zero =>
    apply heq_of_eq
    change -(f a) = -((-1 : R) ^ 0) • f a
    simp
  | succ m =>
    have hl : Int.ofNat m = Int.negSucc 0 + Int.ofNat (m + 1) := by
      change (m : ℤ) = (-1) + ((m : ℤ) + 1)
      omega
    have hr : Int.ofNat m = Int.ofNat (m + 1) + Int.negSucc 0 := by
      change (m : ℤ) = ((m : ℤ) + 1) + (-1)
      omega
    let B := curriedBracketConstant (m + 1) f a
    exact (fullCochainCongr_heq hl (-((-1 : R) ^ (m + 1)) • B)).trans
      (fullCochainCongr_smul_heq hr (-((-1 : R) ^ (m + 1))) B).symm

/-- Signed antisymmetry in every integer degree, including constant cochains. -/
theorem fullBracket_skew (p q : ℤ) (f : FullCochain R A p) (g : FullCochain R A q) :
    HEq (fullBracket p q f g) (-(koszulSign R p q) • fullBracket q p g f) := by
  cases p with
  | ofNat m =>
    cases q with
    | ofNat n =>
      have hk : koszulSign R (Int.ofNat m) (Int.ofNat n) = (-1 : R) ^ (m * n) :=
        koszulSign_nat (R := R) m n
      rw [hk]
      have hs := curriedBracket_antisymm m n f g
      have ht : HEq
          (-((-1 : R) ^ (m * n)) • curriedCongr
            (congrArg (· + 1) (Nat.add_comm n m)) (curriedBracket n m g f))
          (-((-1 : R) ^ (m * n)) • curriedBracket n m g f) := by
        rw [← map_smul]
        exact curriedCongr_heq _ _
      exact (heq_of_eq hs).trans ht
    | negSucc n =>
      cases n with
      | zero =>
        have hk : koszulSign R (Int.ofNat m) (Int.negSucc 0) = (-1 : R) ^ m :=
          koszulSign_nat_neg_one (R := R) m
        rw [hk]
        exact fullBracket_nat_constant_skew m f g
      | succ n =>
        rw [fullBracket_below_right, fullBracket_below_left, smul_zero]
        exact fullCochain_zero_heq (add_comm _ _)
  | negSucc m =>
    cases m with
    | zero =>
      cases q with
      | ofNat n =>
        have hk : koszulSign R (Int.negSucc 0) (Int.ofNat n) = (-1 : R) ^ n :=
          koszulSign_neg_one_nat (R := R) n
        rw [hk]
        exact fullBracket_constant_nat_skew n f g
      | negSucc n =>
        cases n with
        | zero =>
          change HEq (0 : FullCochain R A (-2))
            (-(koszulSign R (-1) (-1)) • (0 : FullCochain R A (-2)))
          rw [smul_zero]
        | succ n =>
          rw [fullBracket_below_right, fullBracket_below_left, smul_zero]
          exact fullCochain_zero_heq (add_comm _ _)
    | succ m =>
      rw [fullBracket_below_left, fullBracket_below_right, smul_zero]
      exact fullCochain_zero_heq (add_comm _ _)

end EnvelopingIsomorphism.Deformation
