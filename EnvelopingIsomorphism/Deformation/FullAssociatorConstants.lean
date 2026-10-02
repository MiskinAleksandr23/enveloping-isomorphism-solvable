import EnvelopingIsomorphism.Deformation.FullAssociator
import EnvelopingIsomorphism.Deformation.PreLieConstantMixed

/-! Constant-degree cases of the associator symmetry for actual integer-graded cochains. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- A genuine arity-n cochain is exactly a full cochain of degree n-1. -/
def arityToFull : (n : ℕ) → Curried R A n ≃ₗ[R] FullCochain R A ((n : ℤ) - 1)
  | 0 => LinearEquiv.refl R A
  | n + 1 => fullCochainCongr (by omega : (n : ℤ) = ((n + 1 : ℕ) : ℤ) - 1)

theorem arityToFull_heq (n : ℕ) (f : Curried R A n) : HEq (arityToFull n f) f := by
  cases n with
  | zero => rfl
  | succ n =>
      exact fullCochainCongr_heq (R := R) (A := A)
        (by omega : (n : ℤ) = ((n + 1 : ℕ) : ℤ) - 1) f

theorem arityToFull_symm_heq (n : ℕ) (f : FullCochain R A ((n : ℤ) - 1)) :
    HEq ((arityToFull n).symm f) f := by
  have h := arityToFull_heq n ((arityToFull n).symm f)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Normalize a full cochain to an arity, with an explicit degree equality. -/
def fullToArity {p : ℤ} {n : ℕ} (h : p = (n : ℤ) - 1) : FullCochain R A p ≃ₗ[R] Curried R A n :=
  (fullCochainCongr h).trans (arityToFull n).symm

theorem fullToArity_heq {p : ℤ} {n : ℕ} (h : p = (n : ℤ) - 1) (f : FullCochain R A p) :
    HEq (fullToArity h f) f :=
  (arityToFull_symm_heq n (fullCochainCongr h f)).trans (fullCochainCongr_heq h f)

theorem full_arity_smul_heq {p : ℤ} {n : ℕ} (h : p = (n : ℤ) - 1)
    (c : R) (f : FullCochain R A p) (F : Curried R A n) (hf : HEq f F) : HEq (c • f) (c • F) := by
  have heq : fullToArity h f = F := eq_of_heq ((fullToArity_heq h f).trans hf)
  exact (fullToArity_heq h (c • f)).symm.trans
    (heq_of_eq (by rw [map_smul, heq]))

theorem full_arity_sub_heq {p : ℤ} {n : ℕ} (h : p = (n : ℤ) - 1)
    (f g : FullCochain R A p) (F G : Curried R A n) (hf : HEq f F) (hg : HEq g G) :
    HEq (f - g) (F - G) := by
  have hf' : fullToArity h f = F := eq_of_heq ((fullToArity_heq h f).trans hf)
  have hg' : fullToArity h g = G := eq_of_heq ((fullToArity_heq h g).trans hg)
  exact (fullToArity_heq h (f - g)).symm.trans (heq_of_eq (by rw [map_sub, hf', hg']))

theorem full_arity_zero_heq {p : ℤ} {n : ℕ} (h : p = (n : ℤ) - 1) :
    HEq (0 : FullCochain R A p) (0 : Curried R A n) :=
  (fullToArity_heq h 0).symm.trans (heq_of_eq (map_zero (fullToArity h)))

theorem fullPreLie_heq {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (f : FullCochain R A p) (F : FullCochain R A p') (hf : HEq f F)
    (g : FullCochain R A q) (G : FullCochain R A q') (hg : HEq g G) :
    HEq (fullPreLie p q f g) (fullPreLie p' q' F G) := by
  subst p'
  subst q'
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

theorem fullPreLie_nat_constant_heq (m : ℕ) (f : Curried R A (m + 1)) (a : A) :
    HEq (fullPreLie (m : ℤ) (-1) f a) (curriedPreLie 0 m f a) := by
  rw [← fullBracket_nat_constant_eq_preLie]
  exact fullBracket_nat_constant m f a

/-- Normalize a positive outer operation and an arbitrary nonnegative inner arity. -/
theorem fullPreLie_arity_heq {p q : ℤ} (m n : ℕ) (hp : p = m) (hq : q = (n : ℤ) - 1)
    (f : FullCochain R A p) (F : Curried R A (m + 1)) (hf : HEq f F)
    (g : FullCochain R A q) (G : Curried R A n) (hg : HEq g G) :
    HEq (fullPreLie p q f g) (curriedPreLie n m F G) := by
  cases n with
  | zero =>
      exact (fullPreLie_heq hp (by omega : q = -1) f F hf g G hg).trans
        (fullPreLie_nat_constant_heq m F G)
  | succ n =>
      exact (fullPreLie_heq hp (by omega : q = (n : ℤ)) f F hf g G hg).trans HEq.rfl

theorem fullPreLie_unary_outer_heq {q : ℤ} (n : ℕ) (hq : q = (n : ℤ) - 1)
    (X : Unary R A) (g : FullCochain R A q) (G : Curried R A n) (hg : HEq g G) :
    HEq (fullPreLie 0 q X g) (curriedPost n X G) :=
  (fullPreLie_arity_heq 0 n rfl hq X X HEq.rfl g G hg).trans
    ((curriedCongr_heq (Nat.zero_add n) (curriedPreLie n 0 X G)).symm.trans
      (heq_of_eq (curriedInsertHead_outer_unary n X G)))

/-- Normalize the positive-first, constant-last associator, including unary outer maps. -/
theorem fullAssociator_nat_nat_constant_heq (m r : ℕ)
    (f : Curried R A (m + 1)) (g : Curried R A (r + 1)) (a : A) :
    HEq (fullAssociator (R := R) (A := A) (m : ℤ) (r : ℤ) (Int.negSucc 0) f g a)
      (curriedPreLie 0 (m + r) (curriedPreLie (r + 1) m f g) a -
        curriedPreLie r m f (curriedPreLie 0 r g a)) := by
  have hfirst := fullPreLie_arity_heq (m + r) 0
    (by omega : (m : ℤ) + r = ((m + r : ℕ) : ℤ))
    (by omega : (-1 : ℤ) = ((0 : ℕ) : ℤ) - 1)
    (fullPreLie (m : ℤ) r f g) (curriedPreLie (r + 1) m f g) HEq.rfl a a HEq.rfl
  have hsecond := fullPreLie_arity_heq m r rfl (by omega : (r : ℤ) + (-1) = (r : ℤ) - 1)
    f f HEq.rfl (fullPreLie (r : ℤ) (-1) g a) (curriedPreLie 0 r g a)
    (fullPreLie_nat_constant_heq r g a)
  exact full_arity_sub_heq
    (by omega : ((m : ℤ) + r) + (-1) = ((m + r : ℕ) : ℤ) - 1)
    _ _ _ _ hfirst ((fullCochainCongr_heq (add_assoc (m : ℤ) r (-1)).symm _).trans hsecond)

/-- A constant-first associator with a positive outer degree has no nested term. -/
theorem fullAssociator_nat_constant_nat_heq (m r : ℕ)
    (f : Curried R A ((m + 1) + 1)) (a : A) (g : Curried R A (r + 1)) :
    HEq (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (Int.negSucc 0) (r : ℤ) f a g)
      (curriedPreLie (r + 1) m (curriedPreLie 0 (m + 1) f a) g) := by
  unfold fullAssociator
  rw [fullPreLie_neg_outer 0 (r : ℤ) a g, fullPreLie_zero_right, map_zero, sub_zero]
  exact fullPreLie_arity_heq m (r + 1)
    (by omega : ((m + 1 : ℕ) : ℤ) + (-1) = (m : ℤ))
    (by omega : (r : ℤ) = ((r + 1 : ℕ) : ℤ) - 1)
    (fullPreLie ((m + 1 : ℕ) : ℤ) (-1) f a) (curriedPreLie 0 (m + 1) f a)
    (fullPreLie_nat_constant_heq (m + 1) f a) g g HEq.rfl

theorem fullAssociator_nat_constants_heq (m : ℕ)
    (f : Curried R A ((m + 1) + 1)) (a b : A) :
    HEq (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (Int.negSucc 0) (Int.negSucc 0) f a b)
      (curriedPreLie 0 m (curriedPreLie 0 (m + 1) f a) b) := by
  unfold fullAssociator
  rw [fullPreLie_neg_outer 0 (Int.negSucc 0) a b, fullPreLie_zero_right, map_zero, sub_zero]
  exact fullPreLie_arity_heq m 0
    (by omega : ((m + 1 : ℕ) : ℤ) + (-1) = (m : ℤ))
    (by omega : (-1 : ℤ) = ((0 : ℕ) : ℤ) - 1)
    (fullPreLie ((m + 1 : ℕ) : ℤ) (-1) f a) (curriedPreLie 0 (m + 1) f a)
    (fullPreLie_nat_constant_heq (m + 1) f a) b b HEq.rfl

/-- A unary outer cochain has vanishing positive/constant associator. -/
theorem fullAssociator_unary_constant_right_zero (r : ℕ) (X : Unary R A)
    (g : Curried R A (r + 1)) (a : A) :
    fullAssociator (R := R) (A := A) 0 (r : ℤ) (Int.negSucc 0) X g a = 0 := by
  have hpost := fullPreLie_unary_outer_heq (r + 1)
    (by omega : (r : ℤ) = ((r + 1 : ℕ) : ℤ) - 1) X g g HEq.rfl
  have hfirst := fullPreLie_arity_heq r 0
    (by omega : (0 : ℤ) + r = (r : ℤ)) (by omega : (-1 : ℤ) = ((0 : ℕ) : ℤ) - 1)
    (fullPreLie 0 (r : ℤ) X g) (curriedPost (r + 1) X g) hpost a a HEq.rfl
  have hsecond := fullPreLie_unary_outer_heq r
    (by omega : (r : ℤ) + (-1) = (r : ℤ) - 1) X
    (fullPreLie (r : ℤ) (-1) g a) (curriedPreLie 0 r g a)
    (fullPreLie_nat_constant_heq r g a)
  have hnorm : HEq (fullAssociator (R := R) (A := A) 0 (r : ℤ) (Int.negSucc 0) X g a)
      (curriedPreLie 0 r (curriedPost (r + 1) X g) a - curriedPost r X (curriedPreLie 0 r g a)) :=
    full_arity_sub_heq (by omega : ((0 : ℤ) + r) + (-1) = (r : ℤ) - 1)
      _ _ _ _ hfirst ((fullCochainCongr_heq (add_assoc (0 : ℤ) r (-1)).symm _).trans hsecond)
  have hz : curriedPreLie 0 r (curriedPost (r + 1) X g) a -
      curriedPost r X (curriedPreLie 0 r g a) = 0 :=
    sub_eq_zero.mpr (curriedPreLie_constant_post r X g a)
  exact eq_of_heq (hnorm.trans ((heq_of_eq hz).trans
    (full_arity_zero_heq (by omega : ((0 : ℤ) + r) + (-1) = (r : ℤ) - 1)).symm))

/-- Full integer-degree associator symmetry with a constant second argument. -/
theorem fullAssociator_nat_constant_nat_symm (m r : ℕ)
    (f : Curried R A (m + 1)) (a : A) (g : Curried R A (r + 1)) :
    fullAssociator (R := R) (A := A) (m : ℤ) (Int.negSucc 0) (r : ℤ) f a g =
      koszulSign R (Int.negSucc 0) (r : ℤ) •
        fullCochainCongr (by omega : ((m : ℤ) + r) + Int.negSucc 0 = ((m : ℤ) + Int.negSucc 0) + r)
          (fullAssociator (R := R) (A := A) (m : ℤ) (r : ℤ) (Int.negSucc 0) f g a) := by
  cases m with
  | zero =>
      have hl : fullAssociator (R := R) (A := A) 0 (Int.negSucc 0) (r : ℤ) f a g = 0 := by
        unfold fullAssociator
        rw [fullPreLie_neg_outer 0 (r : ℤ) a g, fullPreLie_zero_right, map_zero, sub_zero]
        exact fullPreLie_neg_outer 0 (r : ℤ) (f a) g
      have hl' : fullAssociator (R := R) (A := A) ((0 : ℕ) : ℤ) (Int.negSucc 0) (r : ℤ) f a g = 0 := by
        convert hl using 1 <;> rfl
      have hr' : fullAssociator (R := R) (A := A) ((0 : ℕ) : ℤ) (r : ℤ) (Int.negSucc 0) f g a = 0 := by
        convert fullAssociator_unary_constant_right_zero r f g a using 1 <;> rfl
      rw [hl', hr', map_zero, smul_zero]
  | succ m =>
      have hs : koszulSign R (Int.negSucc 0) (r : ℤ) = (-1 : R) ^ r :=
        koszulSign_neg_one_nat r
      rw [hs]
      let B := curriedConstantAssociator m r f g a
      have hL := fullAssociator_nat_constant_nat_heq m r f a g
      have hR : HEq
          (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (r : ℤ) (Int.negSucc 0) f g a) B :=
        fullAssociator_nat_nat_constant_heq (m + 1) r f g a
      have hRS := full_arity_smul_heq
        (by omega : (((m + 1 : ℕ) : ℤ) + r) + Int.negSucc 0 = (((m + 1) + r : ℕ) : ℤ) - 1)
        ((-1 : R) ^ r) _ B hR
      have htarget := (fullCochainCongr_smul_heq
        (by omega : (((m + 1 : ℕ) : ℤ) + r) + Int.negSucc 0 =
          (((m + 1 : ℕ) : ℤ) + Int.negSucc 0) + r)
        ((-1 : R) ^ r)
        (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (r : ℤ) (Int.negSucc 0) f g a)).trans hRS
      have hcast : HEq
          ((-1 : R) ^ r • curriedCongr (Nat.add_right_comm m 1 r) B) ((-1 : R) ^ r • B) := by
        rw [← map_smul]
        exact curriedCongr_heq _ _
      exact eq_of_heq (hL.trans ((heq_of_eq (curriedPreLie_constant_mixed m r f a g)).trans
        (hcast.trans htarget.symm)))

/-- Full integer-degree associator symmetry for two constant arguments. -/
theorem fullAssociator_nat_constants_symm (m : ℕ) (f : Curried R A (m + 1)) (a b : A) :
    fullAssociator (R := R) (A := A) (m : ℤ) (Int.negSucc 0) (Int.negSucc 0) f a b =
      koszulSign R (Int.negSucc 0) (Int.negSucc 0) •
        fullCochainCongr (by omega : ((m : ℤ) + Int.negSucc 0) + Int.negSucc 0 =
          ((m : ℤ) + Int.negSucc 0) + Int.negSucc 0)
          (fullAssociator (R := R) (A := A) (m : ℤ) (Int.negSucc 0) (Int.negSucc 0) f b a) := by
  cases m with
  | zero =>
      change (_ : PUnit.{v + 1}) = _
      exact Subsingleton.elim _ _
  | succ m =>
      have hs : koszulSign R (Int.negSucc 0) (Int.negSucc 0) = -1 := by
        norm_num [koszulSign]
      rw [hs]
      let B := curriedPreLie 0 m (curriedPreLie 0 (m + 1) f b) a
      have hL := fullAssociator_nat_constants_heq m f a b
      have hR : HEq
          (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (Int.negSucc 0) (Int.negSucc 0) f b a) B :=
        fullAssociator_nat_constants_heq m f b a
      have hRS := full_arity_smul_heq
        (by omega : (((m + 1 : ℕ) : ℤ) + Int.negSucc 0) + Int.negSucc 0 = (m : ℤ) - 1)
        (-1 : R) _ B hR
      have htarget := (fullCochainCongr_smul_heq
        (by omega : (((m + 1 : ℕ) : ℤ) + Int.negSucc 0) + Int.negSucc 0 =
          (((m + 1 : ℕ) : ℤ) + Int.negSucc 0) + Int.negSucc 0)
        (-1 : R)
        (fullAssociator (R := R) (A := A) ((m + 1 : ℕ) : ℤ) (Int.negSucc 0) (Int.negSucc 0) f b a)).trans hRS
      have hraw : curriedPreLie 0 m (curriedPreLie 0 (m + 1) f a) b = (-1 : R) • B := by
        rw [neg_one_smul]
        exact curriedPreLie_two_constants m f a b
      exact eq_of_heq (hL.trans ((heq_of_eq hraw).trans htarget.symm))

/-- The swapped mixed case, with the constant in the third argument. -/
theorem fullAssociator_nat_nat_constant_symm (m r : ℕ)
    (f : Curried R A (m + 1)) (g : Curried R A (r + 1)) (a : A) :
    fullAssociator (R := R) (A := A) (m : ℤ) (r : ℤ) (Int.negSucc 0) f g a =
      koszulSign R (r : ℤ) (Int.negSucc 0) •
        fullCochainCongr (by omega : ((m : ℤ) + Int.negSucc 0) + r = ((m : ℤ) + r) + Int.negSucc 0)
          (fullAssociator (R := R) (A := A) (m : ℤ) (Int.negSucc 0) (r : ℤ) f a g) := by
  rw [koszulSign_comm (r : ℤ) (Int.negSucc 0)]
  have h := congrArg
    (fun z : FullCochain R A (((m : ℤ) + Int.negSucc 0) + r) ↦
      koszulSign R (Int.negSucc 0) (r : ℤ) •
        fullCochainCongr
          (by omega : ((m : ℤ) + Int.negSucc 0) + r = ((m : ℤ) + r) + Int.negSucc 0) z)
    (fullAssociator_nat_constant_nat_symm m r f a g)
  simp only [map_smul, fullCochainCongr_trans, fullCochainCongr_self,
    smul_smul, koszulSign_square, one_smul] at h
  exact h.symm

end EnvelopingIsomorphism.Deformation
