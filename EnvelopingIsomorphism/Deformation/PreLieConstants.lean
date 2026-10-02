import EnvelopingIsomorphism.Deformation.PreLieCancellation

/-! Constant-arity boundary identities for the actual Gerstenhaber insertion product. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Constant insertion is the alternating insertion of the constant in all slots. -/
theorem curriedPreLie_constant_succ (m : ℕ) (f : Curried R A ((m + 1) + 1)) (a b : A) :
    curriedPreLie 0 (m + 1) f a b = f a b - curriedPreLie 0 m (f b) a := by
  change f a b + (-1 : R) ^ 1 • curriedPreLie 0 m (f b) a = _
  simp only [pow_one, neg_one_smul, sub_eq_add_neg]

@[simp] theorem curriedPreLie_constant_unary (f : Curried R A 1) (a : A) :
    curriedPreLie 0 0 f a = f a := rfl

/-- Two constant insertions anticommute. No positive arity is imposed on either constant. -/
theorem curriedPreLie_two_constants (m : ℕ) (f : Curried R A ((m + 1) + 1)) (a b : A) :
    curriedPreLie 0 m (curriedPreLie 0 (m + 1) f a) b =
      -curriedPreLie 0 m (curriedPreLie 0 (m + 1) f b) a := by
  induction m with
  | zero =>
      exact (curriedPreLie_constant_succ 0 f a b).trans
        ((by abel : f a b - f b a = -(f b a - f a b)).trans
          (congrArg Neg.neg (curriedPreLie_constant_succ 0 f b a)).symm)
  | succ m ih =>
      apply LinearMap.ext
      intro x
      change curriedPreLie 0 (m + 1) (curriedPreLie 0 ((m + 1) + 1) f a) b x =
        -(curriedPreLie 0 (m + 1) (curriedPreLie 0 ((m + 1) + 1) f b) a x)
      rw [curriedPreLie_constant_succ m _ b x, curriedPreLie_constant_succ m _ a x]
      rw [curriedPreLie_constant_succ (m + 1) f a b,
        curriedPreLie_constant_succ (m + 1) f a x,
        curriedPreLie_constant_succ (m + 1) f b a,
        curriedPreLie_constant_succ (m + 1) f b x]
      simp only [LinearMap.sub_apply, map_sub]
      change (f a b x - curriedPreLie 0 (m + 1) (f b) a x) -
          (curriedPreLie 0 m (f a x) b -
            curriedPreLie 0 m (curriedPreLie 0 (m + 1) (f x) a) b) =
        -((f b a x - curriedPreLie 0 (m + 1) (f a) b x) -
          (curriedPreLie 0 m (f b x) a -
            curriedPreLie 0 m (curriedPreLie 0 (m + 1) (f x) b) a))
      rw [curriedPreLie_constant_succ m (f b) a x,
        curriedPreLie_constant_succ m (f a) b x]
      rw [ih (f x)]
      abel

/-- Constant insertion commutes with output postcomposition by a unary map. -/
theorem curriedPreLie_constant_post (r : ℕ) (X : Unary R A)
    (g : Curried R A (r + 1)) (a : A) :
    curriedPreLie 0 r (curriedPost (r + 1) X g) a =
      curriedPost r X (curriedPreLie 0 r g a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      apply LinearMap.ext
      intro x
      change curriedPreLie 0 (r + 1) (curriedPost ((r + 1) + 1) X g) a x =
        curriedPost r X (curriedPreLie 0 (r + 1) g a x)
      rw [curriedPreLie_constant_succ r _ a x]
      change curriedPost r X (g a x) -
          curriedPreLie 0 r (curriedPost (r + 1) X (g x)) a =
        curriedPost r X (curriedPreLie 0 (r + 1) g a x)
      rw [ih (g x), curriedPreLie_constant_succ r g a x, map_sub]

/-- Unary outer boundary of the mixed pre-Lie identity: its constant-first
associator is zero because a constant outer operation has no insertion slots. -/
theorem curriedPreLie_constant_unary_outer (r : ℕ) (X : Unary R A)
    (g : Curried R A (r + 1)) (a : A) :
    curriedPreLie 0 r
      (curriedCongr (Nat.zero_add (r + 1)) (curriedPreLie (r + 1) 0 X g)) a =
      curriedCongr (Nat.zero_add r) (curriedPreLie r 0 X (curriedPreLie 0 r g a)) := by
  rw [curriedPreLie_zero, curriedPreLie_zero, curriedInsertHead_outer_unary,
    curriedInsertHead_outer_unary]
  exact curriedPreLie_constant_post r X g a

end EnvelopingIsomorphism.Deformation
