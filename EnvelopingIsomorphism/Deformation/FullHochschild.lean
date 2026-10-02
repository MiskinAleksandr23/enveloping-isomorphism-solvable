import EnvelopingIsomorphism.Deformation.HochschildDGLALaws
import Mathlib.Algebra.Ring.NegOnePow

/-!
The full shifted Hochschild complex indexed by integers.  Degree -1 is A,
degree p ≥ 0 consists of (p+1)-ary cochains, and degrees below -1 are zero.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Full cochain modules with their actual shifted integer degrees. -/
@[reducible] def fullCochainObj : ℤ → ModuleCat.{v} R
  | .ofNat n => curriedObj R A (n + 1)
  | .negSucc 0 => ModuleCat.of R A
  | .negSucc (_ + 1) => ModuleCat.of R PUnit

abbrev FullCochain (p : ℤ) : Type v := fullCochainObj R A p

variable {R A}

theorem curriedDifferential_zero (μ : Binary R A) (X : Unary R A) :
    curriedDifferential μ 0 X = differentialOne μ X := by
  ext a b
  change ((-1 : R) ^ 2) • (μ a (X b) - (X (μ a b) - μ (X a) b)) =
    μ (X a) b + μ a (X b) - X (μ a b)
  simp only [neg_one_sq, one_smul]
  abel

/-- The genuine Gerstenhaber-sign differential, including degree -1. -/
def fullDifferential (μ : Binary R A) : (p : ℤ) →
    FullCochain R A p →ₗ[R] FullCochain R A (p + 1)
  | .ofNat n => curriedDifferential μ n
  | .negSucc 0 => μ - μ.flip
  | .negSucc (_ + 1) => 0

@[simp] theorem fullDifferential_nat (μ : Binary R A) (n : ℕ)
    (f : FullCochain R A (n : ℤ)) :
    fullDifferential μ n f = curriedDifferential μ n f := rfl

@[simp] theorem fullDifferential_neg_one (μ : Binary R A) (a : A) :
    fullDifferential μ (-1) a = differentialZero μ a := rfl

theorem fullDifferential_sq (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (p : ℤ) (f : FullCochain R A p) :
    fullDifferential μ (p + 1) (fullDifferential μ p f) = 0 := by
  cases p with
  | ofNat n => exact curriedDifferential_sq μ hμ n f
  | negSucc n =>
    cases n with
    | zero =>
      change curriedDifferential μ 0 (differentialZero μ f) = 0
      rw [curriedDifferential_zero, differentialOne_differentialZero μ hμ]
    | succ n =>
      change fullDifferential μ (Int.negSucc (n + 1) + 1) 0 = 0
      exact map_zero _

/-- The all-degree shifted Hochschild complex, with no truncation at degree zero. -/
def fullComplex (μ : Binary R A) (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fullCochainObj R A)
    (fun p => ModuleCat.ofHom (fullDifferential μ p)) (by
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact fullDifferential_sq μ hμ p f)

end EnvelopingIsomorphism.Deformation
