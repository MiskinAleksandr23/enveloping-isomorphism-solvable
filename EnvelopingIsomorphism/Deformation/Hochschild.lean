import EnvelopingIsomorphism.Deformation.Curried
import EnvelopingIsomorphism.Deformation.LowArity
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
The full Hochschild differential in every arity.  A recursive construction
separates the left action from internal contractions and the right action.
The square-zero identity is proved by induction, without requiring an entire
cosimplicial-object presentation.
-/

namespace EnvelopingIsomorphism.Deformation

set_option backward.isDefEq.respectTransparency false

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Merge the first two arguments of a curried cochain. -/
def curriedMerge (μ : Binary R A) (n : ℕ) :
    Curried R A (n + 1) →ₗ[R] Curried R A (n + 2) :=
  LinearMap.mk₂ R (fun f a => f.comp (μ a))
    (by intros; rfl)
    (by intros; rfl)
    (by intros; ext b; simp)
    (by intros; ext b; simp)

/-- The reduced bar differential, containing internal products and the right action. -/
def curriedReduced (μ : Binary R A) :
    (n : ℕ) → Curried R A n →ₗ[R] Curried R A (n + 1)
  | 0 => μ
  | n + 1 => curriedMerge μ n - LinearMap.compRight R (curriedReduced μ n)

@[simp] theorem curriedReduced_zero (μ : Binary R A) (f a : A) :
    curriedReduced μ 0 f a = μ f a := rfl

@[simp] theorem curriedReduced_succ (μ : Binary R A) (n : ℕ)
    (f : Curried R A (n + 1)) (a : A) :
    curriedReduced μ (n + 1) f a = f.comp (μ a) - curriedReduced μ n (f a) := rfl

/-- The leading left-action term of the bar differential. -/
def curriedLeft (μ : Binary R A) (n : ℕ) :
    Curried R A n →ₗ[R] Curried R A (n + 1) :=
  ((curriedPost n).comp μ).flip

@[simp] theorem curriedLeft_apply (μ : Binary R A) (n : ℕ)
    (f : Curried R A n) (a : A) :
    curriedLeft μ n f a = curriedPost n (μ a) f := rfl

/-- The full Hochschild differential with ordinary, unshifted bar signs. -/
def curriedBar (μ : Binary R A) (n : ℕ) :
    Curried R A n →ₗ[R] Curried R A (n + 1) :=
  curriedLeft μ n - curriedReduced μ n

theorem curriedBar_succ (μ : Binary R A) (n : ℕ) (f : Curried R A (n + 1)) (a : A) :
    curriedBar μ (n + 1) f a =
      curriedPost (n + 1) (μ a) f - f.comp (μ a) +
        curriedLeft μ n (f a) - curriedBar μ n (f a) := by
  change curriedPost (n + 1) (μ a) f - (f.comp (μ a) - curriedReduced μ n (f a)) =
    curriedPost (n + 1) (μ a) f - f.comp (μ a) + curriedLeft μ n (f a) -
      (curriedLeft μ n (f a) - curriedReduced μ n (f a))
  abel

variable (μ : Binary R A) (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))

include hμ

theorem leftMultiplication_comp (a b : A) :
    (μ a).comp (μ b) = μ (μ a b) := by
  ext c
  exact (hμ a b c).symm

/-- The reduced differential already squares to zero. -/
theorem curriedReduced_sq (n : ℕ) (f : Curried R A n) :
    curriedReduced μ (n + 1) (curriedReduced μ n f) = 0 := by
  induction n with
  | zero =>
    ext a b
    change μ f (μ a b) - μ (μ f a) b = 0
    rw [hμ, sub_self]
  | succ n ih =>
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    have hassoc : f.comp (μ (μ a b)) = (f.comp (μ a)).comp (μ b) := by
      ext c
      change f (μ (μ a b) c) = f (μ a (μ b c))
      rw [hμ]
    have hi : (curriedReduced μ n (f a)).comp (μ b) -
        curriedReduced μ n (curriedReduced μ n (f a) b) = 0 :=
      congrArg (fun g => g b) (ih (f a))
    change
      (f.comp (μ (μ a b)) - curriedReduced μ n (f (μ a b))) -
        ((f.comp (μ a) - curriedReduced μ n (f a)).comp (μ b) -
          curriedReduced μ n (f (μ a b) - curriedReduced μ n (f a) b)) = 0
    rw [hassoc, LinearMap.sub_comp, map_sub]
    calc
      _ = (curriedReduced μ n (f a)).comp (μ b) -
          curriedReduced μ n (curriedReduced μ n (f a) b) := by abel
      _ = 0 := hi

/-- The reduced differential commutes with left multiplication on the output. -/
theorem curriedReduced_post_left (n : ℕ) (a : A) (f : Curried R A n) :
    curriedReduced μ n (curriedPost n (μ a) f) =
      curriedPost (n + 1) (μ a) (curriedReduced μ n f) := by
  induction n with
  | zero =>
    ext b
    exact hμ a f b
  | succ n ih =>
    apply LinearMap.ext
    intro b
    change ((curriedPost n (μ a)).comp f).comp (μ b) -
        curriedReduced μ n (curriedPost n (μ a) (f b)) =
      curriedPost (n + 1) (μ a) (f.comp (μ b) - curriedReduced μ n (f b))
    rw [map_sub, ih]
    rfl

/-- The mixed left/reduced identity which cancels the cross terms in δ². -/
theorem curriedReduced_left (n : ℕ) (f : Curried R A n) :
    curriedReduced μ (n + 1) (curriedLeft μ n f) =
      curriedLeft μ (n + 1) (curriedLeft μ n f) -
        curriedLeft μ (n + 1) (curriedReduced μ n f) := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change curriedPost n (μ (μ a b)) f -
      curriedReduced μ n (curriedPost n (μ a) f) b =
    curriedPost n (μ a) (curriedPost n (μ b) f) -
      curriedPost n (μ a) (curriedReduced μ n f b)
  rw [curriedReduced_post_left μ hμ, ← curriedPost_comp, leftMultiplication_comp μ hμ]
  rfl

/-- The full bar differential squares to zero in every arity, including zero. -/
theorem curriedBar_sq (n : ℕ) (f : Curried R A n) :
    curriedBar μ (n + 1) (curriedBar μ n f) = 0 := by
  simp only [curriedBar, LinearMap.sub_apply, map_sub,
    curriedReduced_left μ hμ, curriedReduced_sq μ hμ]
  abel

omit hμ

/-- The ordinary bar differential on all multilinear Hochschild cochains. -/
def barDifferential (n : ℕ) : Cochain R A n →ₗ[R] Cochain R A (n + 1) :=
  (cochainCurriedEquiv R A (n + 1)).symm.toLinearMap.comp
    ((curriedBar μ n).comp (cochainCurriedEquiv R A n).toLinearMap)

@[simp] theorem barDifferential_apply (n : ℕ) (f : Cochain R A n) :
    barDifferential μ n f = (cochainCurriedEquiv R A (n + 1)).symm
      (curriedBar μ n (cochainCurriedEquiv R A n f)) := rfl

theorem barDifferential_eval (n : ℕ) (f : Cochain R A n) (x : Fin (n + 1) → A) :
    barDifferential μ n f x =
      curriedEval (n + 1) (curriedBar μ n (cochainCurriedEquiv R A n f)) x :=
  cochainCurriedEquiv_symm_apply _ _ _

/-- A tuple recurrence for the full differential, including both endpoint terms.
This also identifies the recursive construction with the usual bar formula. -/
theorem barDifferential_cons_cons (n : ℕ) (f : Cochain R A (n + 1))
    (a b : A) (x : Fin n → A) :
    barDifferential μ (n + 1) f (Fin.cons a (Fin.cons b x)) =
      μ a (f (Fin.cons b x)) - f (Fin.cons (μ a b) x) +
        μ b (f (Fin.cons a x)) -
          barDifferential μ n (f.curryLeft a) (Fin.cons b x) := by
  rw [barDifferential_eval]
  change curriedEval (n + 1)
      (curriedBar μ (n + 1) (cochainCurriedEquiv R A (n + 1) f) a) (Fin.cons b x) = _
  rw [curriedBar_succ, curriedEval_sub, curriedEval_add, curriedEval_sub,
    curriedEval_post, curriedEval_equiv]
  change μ a (f (Fin.cons b x)) -
      curriedEval n (cochainCurriedEquiv R A (n + 1) f (μ a b)) x +
      curriedEval n (curriedPost n (μ b) (cochainCurriedEquiv R A (n + 1) f a)) x -
      curriedEval (n + 1)
        (curriedBar μ n (cochainCurriedEquiv R A n (f.curryLeft a))) (Fin.cons b x) = _
  rw [curriedEval_equiv_cons, curriedEval_post, curriedEval_equiv_cons,
    ← barDifferential_eval]

/-- The Gerstenhaber convention `[μ,-]`, with sign `(-1)^(n-1)` in arity n.
We use the equal sign `(-1)^(n+1)` to avoid negative natural exponents at n=0. -/
def signedDifferential (n : ℕ) : Cochain R A n →ₗ[R] Cochain R A (n + 1) :=
  (-1 : R) ^ (n + 1) • barDifferential μ n

include hμ

theorem barDifferential_sq (n : ℕ) (f : Cochain R A n) :
    barDifferential μ (n + 1) (barDifferential μ n f) = 0 := by
  simp only [barDifferential_apply, LinearEquiv.apply_symm_apply,
    curriedBar_sq μ hμ, map_zero]

theorem signedDifferential_sq (n : ℕ) (f : Cochain R A n) :
    signedDifferential μ (n + 1) (signedDifferential μ n f) = 0 := by
  simp only [signedDifferential, LinearMap.smul_apply, map_smul,
    barDifferential_sq μ hμ, smul_zero]

/-- The genuine full Hochschild cochain complex with ordinary bar signs. -/
def barComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (Cochain R A n))
    (fun n => ModuleCat.ofHom (barDifferential μ n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact barDifferential_sq μ hμ n f)

/-- The same full cochain modules with the Gerstenhaber differential signs.
The index here is arity; its shifted cohomological degree is n−1. -/
def signedComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (Cochain R A n))
    (fun n => ModuleCat.ofHom (signedDifferential μ n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact signedDifferential_sq μ hμ n f)

omit hμ

theorem barDifferential_zero (a : A) :
    cochainOneEquiv R A (barDifferential μ 0 ((cochainZeroEquiv R A).symm a)) =
      -differentialZero μ a := by
  simp only [barDifferential_apply, cochainCurriedEquiv_zero,
    LinearEquiv.apply_symm_apply]
  ext b
  change μ b a - μ a b = -(μ a b - μ b a)
  abel

theorem barDifferential_one (X : Unary R A) :
    cochainTwoEquiv R A (barDifferential μ 1 ((cochainOneEquiv R A).symm X)) =
      differentialOne μ X := by
  simp only [barDifferential_apply, cochainCurriedEquiv_one,
    LinearEquiv.apply_symm_apply]
  ext a b
  change μ a (X b) - (X (μ a b) - μ (X a) b) =
    μ (X a) b + μ a (X b) - X (μ a b)
  abel

theorem barDifferential_two (ν : Binary R A) :
    cochainThreeEquiv R A (barDifferential μ 2 ((cochainTwoEquiv R A).symm ν)) =
      -differentialTwo μ ν := by
  simp only [barDifferential_apply, cochainCurriedEquiv_two,
    LinearEquiv.apply_symm_apply]
  ext a b c
  change μ a (ν b c) - (ν (μ a b) c - (ν a (μ b c) - μ (ν a b) c)) =
    -((μ (ν a b) c - μ a (ν b c)) + (ν (μ a b) c - ν a (μ b c)))
  abel

end EnvelopingIsomorphism.Deformation
