import EnvelopingIsomorphism.Deformation.Hochschild
import EnvelopingIsomorphism.Deformation.Gerstenhaber

/-!
Identify the all-arity Hochschild differential with the Gerstenhaber bracket
with the multiplication.  Associativity is not needed for this identification.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- The final right-multiplication term, without its alternating sign. -/
def curriedRight (μ : Binary R A) :
    (n : ℕ) → Curried R A n →ₗ[R] Curried R A (n + 1)
  | 0 => μ
  | n + 1 => LinearMap.compRight R (curriedRight μ n)

@[simp] theorem curriedRight_zero (μ : Binary R A) (a b : A) :
    curriedRight μ 0 a b = μ a b := rfl

@[simp] theorem curriedRight_succ (μ : Binary R A) (n : ℕ)
    (f : Curried R A (n + 1)) (a : A) :
    curriedRight μ (n + 1) f a = curriedRight μ n (f a) := rfl

theorem curriedRight_eq_head (μ : Binary R A) (n : ℕ) (f : Curried R A n) :
    curriedCongr (Nat.add_comm 1 n) (curriedInsertHead 1 n μ f) = curriedRight μ n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply LinearMap.ext
    intro a
    exact (curriedCongr_succ (Nat.add_comm 1 n)
      (curriedInsertHead 1 (n + 1) μ f) a).trans (ih (f a))

/-- Inserting a product in successive slots alternates in sign. -/
theorem curriedPreLie_mul_succ (μ : Binary R A) (m : ℕ)
    (f : Curried R A (m + 1 + 1)) (a : A) :
    curriedPreLie 2 (m + 1) f μ a =
      f.comp (μ a) - curriedPreLie 2 m (f a) μ := by
  apply LinearMap.ext
  intro b
  change f (μ a b) + ((-1 : R) ^ 3) • curriedPreLie 2 m (f a) μ b =
    f (μ a b) - curriedPreLie 2 m (f a) μ b
  simp [pow_succ, sub_eq_add_neg]

/-- Reduced differential = internal insertion sum + signed final endpoint. -/
theorem curriedReduced_eq_preLie_right (μ : Binary R A) (m : ℕ)
    (f : Curried R A (m + 1)) :
    curriedReduced μ (m + 1) f =
      curriedPreLie 2 m f μ + (-1 : R) ^ (m + 1) • curriedRight μ (m + 1) f := by
  induction m with
  | zero =>
    ext a b
    change f (μ a b) - μ (f a) b = f (μ a b) + ((-1 : R) ^ 1) • μ (f a) b
    simp [sub_eq_add_neg]
  | succ m ih =>
    apply LinearMap.ext
    intro a
    change f.comp (μ a) - curriedReduced μ (m + 1) (f a) =
      curriedPreLie 2 (m + 1) f μ a +
        (-1 : R) ^ (m + 1 + 1) • curriedRight μ (m + 1) (f a)
    rw [curriedPreLie_mul_succ, ih, pow_succ (-1 : R) (m + 1), mul_neg_one, neg_smul]
    abel

/-- The two insertions into multiplication are exactly the two endpoint terms. -/
theorem curriedPreLie_mul_outer (μ : Binary R A) (n : ℕ) (f : Curried R A n) :
    curriedCongr (Nat.add_comm 1 n) (curriedPreLie n 1 μ f) =
      curriedRight μ n f + (-1 : R) ^ (n + 1) • curriedLeft μ n f := by
  rw [curriedPreLie_succ, map_add, map_smul, curriedRight_eq_head, curriedCongr_trans]
  congr 1
  apply congrArg (fun z : Curried R A (n + 1) => (-1 : R) ^ (n + 1) • z)
  apply LinearMap.ext
  intro a
  exact (curriedCongr_succ (Nat.zero_add n)
    (curriedLiftPrefix (curriedPreLie n 0) μ f) a).trans
      (curriedInsertHead_outer_unary n (μ a) f)

/-- In every positive arity, the bracket with multiplication is the signed differential. -/
theorem curriedBracket_multiplication (μ : Binary R A) (m : ℕ)
    (f : Curried R A (m + 1)) :
    curriedCongr (Nat.add_comm 1 (m + 1)) (curriedBracket 1 m μ f) =
      (-1 : R) ^ (m + 1 + 1) • curriedBar μ (m + 1) f := by
  have hs : ((-1 : R) ^ m) * ((-1 : R) ^ (m + 1)) = -1 := by
    rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hp : (-1 : R) ^ (m + 1 + 1) = (-1 : R) ^ m := by
    simp [pow_add]
  unfold curriedBracket
  rw [map_sub, map_smul, curriedPreLie_mul_outer, curriedCongr_trans]
  change curriedRight μ (m + 1) f + (-1 : R) ^ (m + 1 + 1) • curriedLeft μ (m + 1) f -
      (-1 : R) ^ (1 * m) • curriedPreLie 2 m f μ =
    (-1 : R) ^ (m + 1 + 1) •
      (curriedLeft μ (m + 1) f - curriedReduced μ (m + 1) f)
  rw [hp, Nat.one_mul, curriedReduced_eq_preLie_right]
  simp only [smul_sub, smul_add, smul_smul, hs, neg_one_smul]
  abel

/-- The multiplication-bracket identity on the public full cochain representation. -/
theorem signedDifferential_eq_bracket (μ : Binary R A) (m : ℕ)
    (f : Cochain R A (m + 1)) :
    cochainCurriedEquiv R A (m + 1 + 1) (signedDifferential μ (m + 1) f) =
      curriedCongr (Nat.add_comm 1 (m + 1))
        (curriedBracket 1 m μ (cochainCurriedEquiv R A (m + 1) f)) := by
  simp only [signedDifferential, LinearMap.smul_apply, map_smul, barDifferential_apply,
    LinearEquiv.apply_symm_apply]
  exact (curriedBracket_multiplication μ m (cochainCurriedEquiv R A (m + 1) f)).symm

/-- The zero-ary case of `[μ,-]` is the nonzero inner-derivation map. -/
theorem signedDifferential_zero_eq_bracket (μ : Binary R A) (f : Cochain R A 0) :
    cochainOneEquiv R A (signedDifferential μ 0 f) =
      curriedBracketConstant 1 μ (cochainZeroEquiv R A f) := by
  unfold curriedBracketConstant
  rw [curriedPreLie_binary_constant]
  have h := barDifferential_zero μ (cochainZeroEquiv R A f)
  simp only [LinearEquiv.symm_apply_apply] at h
  change cochainOneEquiv R A (((-1 : R) ^ 1) • barDifferential μ 0 f) = _
  rw [pow_one, neg_one_smul, map_neg, h, neg_neg]

end EnvelopingIsomorphism.Deformation
