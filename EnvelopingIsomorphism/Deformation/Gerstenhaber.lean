import EnvelopingIsomorphism.Deformation.Insertion

/-!
The signed Gerstenhaber insertion sum for full cochains.  Positive outer arity
is represented as `m + 1`, so its cohomological degree is m.  Zero-ary inner
operations are retained, with alternating signs at successive slots.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Sum insertion over the outer slots with the Gerstenhaber sign.
`m+1` is the outer arity and n is the inner arity. -/
def curriedPreLie (n : ℕ) : (m : ℕ) →
    Curried R A (m + 1) →ₗ[R] Curried R A n →ₗ[R] Curried R A (m + n)
  | 0 => curriedInsertHead 0 n
  | m + 1 => curriedInsertHead (m + 1) n +
      (-1 : R) ^ (n + 1) •
        (curriedLiftPrefix (curriedPreLie n m)).compr₂
          (curriedCongr (Nat.add_right_comm m n 1)).toLinearMap

@[simp] theorem curriedPreLie_zero (n : ℕ) (f : Unary R A) (g : Curried R A n) :
    curriedPreLie n 0 f g = curriedInsertHead 0 n f g := rfl

theorem curriedPreLie_succ (m n : ℕ) (f : Curried R A (m + 1 + 1))
    (g : Curried R A n) :
    curriedPreLie n (m + 1) f g = curriedInsertHead (m + 1) n f g +
      (-1 : R) ^ (n + 1) • curriedCongr (Nat.add_right_comm m n 1)
        (curriedLiftPrefix (curriedPreLie n m) f g) := rfl

/-- The signed bracket for two positive-arity cochains. -/
def curriedBracket (m n : ℕ) (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) :
    Curried R A (m + (n + 1)) :=
  curriedPreLie (n + 1) m f g - (-1 : R) ^ (m * n) •
    curriedCongr (congrArg (· + 1) (Nat.add_comm n m)) (curriedPreLie (m + 1) n g f)

/-- The positive-arity bracket is bilinear over the coefficient ring. -/
def curriedBracketLinear (m n : ℕ) :
    Curried R A (m + 1) →ₗ[R] Curried R A (n + 1) →ₗ[R] Curried R A (m + (n + 1)) :=
  curriedPreLie (n + 1) m - (-1 : R) ^ (m * n) •
    (curriedPreLie (m + 1) n).flip.compr₂
      (curriedCongr (congrArg (· + 1) (Nat.add_comm n m))).toLinearMap

@[simp] theorem curriedBracketLinear_apply (m n : ℕ)
    (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) :
    curriedBracketLinear m n f g = curriedBracket m n f g := rfl

/-- Bracketing a positive-arity cochain with a constant on the right. -/
def curriedBracketConstant (m : ℕ) (f : Curried R A (m + 1)) (a : A) : Curried R A m :=
  curriedPreLie 0 m f a

/-- The bracket with a zero-ary cochain on the left, with shifted Koszul sign. -/
def curriedConstantBracket (m : ℕ) (a : A) (f : Curried R A (m + 1)) : Curried R A m :=
  -((-1 : R) ^ m) • curriedBracketConstant m f a

/-- The bracket on actual full multilinear cochains of positive arity. -/
def cochainBracketPositive (m n : ℕ) :
    Cochain R A (m + 1) →ₗ[R] Cochain R A (n + 1) →ₗ[R] Cochain R A (m + (n + 1)) :=
  (((curriedBracketLinear m n).comp (cochainCurriedEquiv R A (m + 1)).toLinearMap).compl₂
    (cochainCurriedEquiv R A (n + 1)).toLinearMap).compr₂
      (cochainCurriedEquiv R A (m + (n + 1))).symm.toLinearMap

@[simp] theorem cochainBracketPositive_apply (m n : ℕ)
    (f : Cochain R A (m + 1)) (g : Cochain R A (n + 1)) :
    cochainBracketPositive m n f g = (cochainCurriedEquiv R A (m + (n + 1))).symm
      (curriedBracket m n (cochainCurriedEquiv R A (m + 1) f)
        (cochainCurriedEquiv R A (n + 1) g)) := rfl

theorem curriedPreLie_binary_binary (μ ν : Binary R A) :
    curriedPreLie 2 1 μ ν = insertBinary μ ν := by
  ext a b c
  change μ (ν a b) c + ((-1 : R) ^ 3) • μ a (ν b c) =
    μ (ν a b) c - μ a (ν b c)
  simp [pow_succ, sub_eq_add_neg]

theorem curriedPreLie_binary_unary (μ : Binary R A) (X : Unary R A) :
    curriedPreLie 1 1 μ X = μ.comp X + μ.compl₂ X := by
  ext a b
  change μ (X a) b + ((-1 : R) ^ 2) • μ a (X b) = μ (X a) b + μ a (X b)
  simp

theorem curriedPreLie_binary_constant (μ : Binary R A) (a : A) :
    curriedPreLie 0 1 μ a = differentialZero μ a := by
  ext b
  change μ a b + ((-1 : R) ^ 1) • μ b a = μ a b - μ b a
  simp [sub_eq_add_neg]

theorem curriedBracket_unary_unary (X Y : Unary R A) :
    curriedBracket 0 0 X Y = bracketUnary X Y := by
  ext a
  change X (Y a) - ((-1 : R) ^ 0) • Y (X a) = X (Y a) - Y (X a)
  simp

theorem curriedBracket_unary_binary (X : Unary R A) (μ : Binary R A) :
    curriedBracket 0 1 X μ = unaryAction X μ := by
  ext a b
  change X (μ a b) - ((-1 : R) ^ 0) •
      (μ (X a) b + ((-1 : R) ^ 2) • μ a (X b)) =
    X (μ a b) - μ (X a) b - μ a (X b)
  simp only [pow_zero, neg_one_sq, one_smul]
  abel

theorem curriedBracket_binary_binary (μ ν : Binary R A) :
    curriedBracket 1 1 μ ν = bracketBinary μ ν := by
  change curriedPreLie 2 1 μ ν - ((-1 : R) ^ 1) • curriedPreLie 2 1 ν μ = _
  rw [curriedPreLie_binary_binary, curriedPreLie_binary_binary]
  simp [bracketBinary]

/-- Signed antisymmetry in arbitrary positive arities. -/
theorem curriedBracket_antisymm (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) :
    curriedBracket m n f g = -((-1 : R) ^ (m * n)) •
      curriedCongr (congrArg (· + 1) (Nat.add_comm n m)) (curriedBracket n m g f) := by
  have hs : ((-1 : R) ^ (m * n)) * ((-1 : R) ^ (m * n)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  unfold curriedBracket
  rw [map_sub, map_smul, curriedCongr_trans]
  change curriedPreLie (n + 1) m f g - (-1 : R) ^ (m * n) •
      curriedCongr (congrArg (· + 1) (Nat.add_comm n m)) (curriedPreLie (m + 1) n g f) =
    -((-1 : R) ^ (m * n)) •
      (curriedCongr (congrArg (· + 1) (Nat.add_comm n m)) (curriedPreLie (m + 1) n g f) -
        (-1 : R) ^ (n * m) • curriedPreLie (n + 1) m f g)
  simp only [Nat.mul_comm n m, smul_sub, smul_smul, neg_mul, hs,
    neg_smul, one_smul]
  abel

end EnvelopingIsomorphism.Deformation
