import EnvelopingIsomorphism.Deformation.Cochains
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.Abel

/-!
Gerstenhaber operations in arities zero through three, expressed using the
linear equivalences in `Cochains`.  We use the shifted convention `d = [μ, -]`.
The computations include arity zero (cohomological degree -1).
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Insert a binary operation in the first slot of another binary operation. -/
def insertLeft (μ ν : Binary R A) : Ternary R A := ν.compr₂ μ

/-- Insert a binary operation in the second slot of another binary operation. -/
def insertRight (μ ν : Binary R A) : Ternary R A where
  toFun a := ν.compr₂ (μ a)
  map_add' _ _ := by ext b c; simp
  map_smul' _ _ := by ext b c; simp

@[simp] theorem insertLeft_apply (μ ν : Binary R A) (a b c : A) :
    insertLeft μ ν a b c = μ (ν a b) c := rfl

@[simp] theorem insertRight_apply (μ ν : Binary R A) (a b c : A) :
    insertRight μ ν a b c = μ a (ν b c) := rfl

/-- The insertion sum of two degree-one cochains has a minus sign. -/
def insertBinary (μ ν : Binary R A) : Ternary R A :=
  insertLeft μ ν - insertRight μ ν

/-- Two degree-one cochains have a symmetric Gerstenhaber bracket. -/
def bracketBinary (μ ν : Binary R A) : Ternary R A :=
  insertBinary μ ν + insertBinary ν μ

/-- Gerstenhaber bracket of two degree-zero cochains. -/
def bracketUnary (X Y : Unary R A) : Unary R A := X.comp Y - Y.comp X

/-- Gerstenhaber bracket `[X, μ]` for degrees zero and one. -/
def unaryAction (X : Unary R A) (μ : Binary R A) : Binary R A :=
  μ.compr₂ X - μ.comp X - μ.compl₂ X

/-- `d = [μ,-]` in cohomological degree -1. -/
def differentialZero (μ : Binary R A) (a : A) : Unary R A := μ a - μ.flip a

/-- `d = [μ,-]` in cohomological degree zero. -/
def differentialOne (μ : Binary R A) (X : Unary R A) : Binary R A :=
  μ.comp X + μ.compl₂ X - μ.compr₂ X

/-- `d = [μ,-]` in cohomological degree one. -/
def differentialTwo (μ ν : Binary R A) : Ternary R A := bracketBinary μ ν

@[simp] theorem insertBinary_apply (μ ν : Binary R A) (a b c : A) :
    insertBinary μ ν a b c = μ (ν a b) c - μ a (ν b c) := rfl

@[simp] theorem bracketBinary_apply (μ ν : Binary R A) (a b c : A) :
    bracketBinary μ ν a b c =
      (μ (ν a b) c - μ a (ν b c)) + (ν (μ a b) c - ν a (μ b c)) := rfl

@[simp] theorem bracketUnary_apply (X Y : Unary R A) (a : A) :
    bracketUnary X Y a = X (Y a) - Y (X a) := rfl

@[simp] theorem unaryAction_apply (X : Unary R A) (μ : Binary R A) (a b : A) :
    unaryAction X μ a b = X (μ a b) - μ (X a) b - μ a (X b) := rfl

@[simp] theorem differentialZero_apply (μ : Binary R A) (a b : A) :
    differentialZero μ a b = μ a b - μ b a := rfl

@[simp] theorem differentialOne_apply (μ : Binary R A) (X : Unary R A) (a b : A) :
    differentialOne μ X a b = μ (X a) b + μ a (X b) - X (μ a b) := rfl

@[simp] theorem differentialTwo_apply (μ ν : Binary R A) (a b c : A) :
    differentialTwo μ ν a b c =
      (μ (ν a b) c - μ a (ν b c)) + (ν (μ a b) c - ν a (μ b c)) := rfl

theorem differentialOne_eq_neg_unaryAction (μ : Binary R A) (X : Unary R A) :
    differentialOne μ X = -unaryAction X μ := by
  ext a b
  simp only [differentialOne_apply, LinearMap.neg_apply, unaryAction_apply]
  abel

theorem bracketBinary_comm (μ ν : Binary R A) :
    bracketBinary μ ν = bracketBinary ν μ := add_comm _ _

theorem bracketUnary_self (X : Unary R A) : bracketUnary X X = 0 := sub_self _

theorem bracketBinary_self (μ : Binary R A) :
    bracketBinary μ μ = 2 • insertBinary μ μ := by
  exact (two_nsmul _).symm

/-- Associativity is the vanishing of the Gerstenhaber insertion square. -/
theorem insertBinary_self_eq_zero_iff (μ : Binary R A) :
    insertBinary μ μ = 0 ↔ ∀ a b c, μ (μ a b) c = μ a (μ b c) := by
  constructor
  · intro h a b c
    have := LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun h a) b) c
    exact sub_eq_zero.mp this
  · intro h
    ext a b c
    simp [h]

/-- Expansion of the associator, valid without assuming the base product associative. -/
theorem insertBinary_add_self (μ ν : Binary R A) :
    insertBinary (μ + ν) (μ + ν) =
      insertBinary μ μ + differentialTwo μ ν + insertBinary ν ν := by
  ext a b c
  simp only [insertBinary_apply, differentialTwo_apply, LinearMap.add_apply, map_add]
  abel

/-- The Maurer-Cartan equation for a perturbation is precisely associativity.
This formulation avoids division by 2 and thus works over any commutative ring. -/
theorem maurerCartan_iff_associative (μ ν : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    differentialTwo μ ν + insertBinary ν ν = 0 ↔
      ∀ a b c, (μ + ν) ((μ + ν) a b) c = (μ + ν) a ((μ + ν) b c) := by
  rw [← insertBinary_self_eq_zero_iff, insertBinary_add_self,
    (insertBinary_self_eq_zero_iff μ).mpr hμ, zero_add]

/-- The first square-zero identity includes the cochains of degree -1. -/
theorem differentialOne_differentialZero (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (a : A) :
    differentialOne μ (differentialZero μ a) = 0 := by
  ext b c
  simp only [differentialOne_apply, differentialZero_apply, map_sub, LinearMap.sub_apply,
    LinearMap.zero_apply]
  rw [hμ, hμ, hμ]
  abel

/-- The second square-zero identity uses only associativity and linearity. -/
theorem differentialTwo_differentialOne (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (X : Unary R A) :
    differentialTwo μ (differentialOne μ X) = 0 := by
  ext a b c
  simp only [differentialTwo_apply, differentialOne_apply, map_add, map_sub,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply]
  simp only [hμ]
  abel

/-- The unary action is a representation of the commutator Lie algebra. -/
theorem unaryAction_bracket (X Y : Unary R A) (μ : Binary R A) :
    unaryAction (bracketUnary X Y) μ =
      unaryAction X (unaryAction Y μ) - unaryAction Y (unaryAction X μ) := by
  ext a b
  simp only [unaryAction_apply, bracketUnary_apply, map_sub, LinearMap.sub_apply]
  abel

end EnvelopingIsomorphism.Deformation
