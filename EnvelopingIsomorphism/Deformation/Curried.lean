import EnvelopingIsomorphism.Deformation.Cochains
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
Recursively curried full Hochschild cochains.  This auxiliary representation
lets us construct the differential by induction while retaining an explicit
linear equivalence to the usual multilinear-map representation in every arity.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Bundling keeps the recursively needed module instances available. -/
@[reducible] def curriedObj : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R A
  | n + 1 => ModuleCat.of R (A →ₗ[R] curriedObj n)

abbrev Curried (n : ℕ) : Type v := curriedObj R A n

/-- All curried cochains are canonically full multilinear cochains. -/
def cochainCurriedEquiv : (n : ℕ) → Cochain R A n ≃ₗ[R] Curried R A n
  | 0 => cochainZeroEquiv R A
  | n + 1 =>
    (multilinearCurryLeftEquiv R (fun _ : Fin (n + 1) => A) A).trans
      ((LinearEquiv.refl R A).arrowCongr (cochainCurriedEquiv n))

@[simp] theorem cochainCurriedEquiv_zero :
    cochainCurriedEquiv R A 0 = cochainZeroEquiv R A := rfl

@[simp] theorem cochainCurriedEquiv_one :
    cochainCurriedEquiv R A 1 = cochainOneEquiv R A := by
  ext f a
  change f (Fin.cons a Fin.elim0) = f (fun _ => a)
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

@[simp] theorem cochainCurriedEquiv_two :
    cochainCurriedEquiv R A 2 = cochainTwoEquiv R A := by
  change (multilinearCurryLeftEquiv R (fun _ : Fin 2 => A) A).trans
      ((LinearEquiv.refl R A).arrowCongr (cochainCurriedEquiv R A 1)) = _
  rw [cochainCurriedEquiv_one]
  rfl

@[simp] theorem cochainCurriedEquiv_three :
    cochainCurriedEquiv R A 3 = cochainThreeEquiv R A := by
  change (multilinearCurryLeftEquiv R (fun _ : Fin 3 => A) A).trans
      ((LinearEquiv.refl R A).arrowCongr (cochainCurriedEquiv R A 2)) = _
  rw [cochainCurriedEquiv_two]
  rfl

variable {R A}

/-- Transport curried cochains across an equality of arities. -/
def curriedCongr {n m : ℕ} (h : n = m) : Curried R A n ≃ₗ[R] Curried R A m :=
  h ▸ LinearEquiv.refl R (Curried R A n)

@[simp] theorem curriedCongr_rfl (n : ℕ) (f : Curried R A n) :
    curriedCongr rfl f = f := rfl

@[simp] theorem curriedCongr_trans {n m l : ℕ} (h : n = m) (h' : m = l)
    (f : Curried R A n) :
    curriedCongr h' (curriedCongr h f) = curriedCongr (h.trans h') f := by
  subst m
  subst l
  rfl

@[simp] theorem curriedCongr_succ {n m : ℕ} (h : n = m)
    (f : Curried R A (n + 1)) (a : A) :
    curriedCongr (congrArg (· + 1) h) f a = curriedCongr h (f a) := by
  subst m
  rfl

@[simp] theorem cochainCurriedEquiv_succ_apply (n : ℕ) (f : Cochain R A (n + 1)) (a : A) :
    cochainCurriedEquiv R A (n + 1) f a =
      cochainCurriedEquiv R A n (f.curryLeft a) := rfl

/-- Evaluate a recursively curried cochain on an ordinary finite tuple. -/
def curriedEval : (n : ℕ) → Curried R A n → (Fin n → A) → A
  | 0, f, _ => f
  | n + 1, f, x => curriedEval n (f (x 0)) (Fin.tail x)

@[simp] theorem curriedEval_add (n : ℕ) (f g : Curried R A n) (x : Fin n → A) :
    curriedEval n (f + g) x = curriedEval n f x + curriedEval n g x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f (x 0)) (g (x 0)) (Fin.tail x)

@[simp] theorem curriedEval_sub (n : ℕ) (f g : Curried R A n) (x : Fin n → A) :
    curriedEval n (f - g) x = curriedEval n f x - curriedEval n g x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f (x 0)) (g (x 0)) (Fin.tail x)

@[simp] theorem curriedEval_smul (n : ℕ) (r : R) (f : Curried R A n) (x : Fin n → A) :
    curriedEval n (r • f) x = r • curriedEval n f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f (x 0)) (Fin.tail x)

theorem curriedEval_equiv (n : ℕ) (f : Cochain R A n) (x : Fin n → A) :
    curriedEval n (cochainCurriedEquiv R A n f) x = f x := by
  induction n with
  | zero =>
    change f Fin.elim0 = f x
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    change curriedEval n (cochainCurriedEquiv R A n (f.curryLeft (x 0))) (Fin.tail x) = _
    rw [ih]
    change f (Fin.cons (x 0) (Fin.tail x)) = f x
    rw [Fin.cons_self_tail]

theorem cochainCurriedEquiv_symm_apply (n : ℕ) (f : Curried R A n) (x : Fin n → A) :
    (cochainCurriedEquiv R A n).symm f x = curriedEval n f x := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (curriedEval_equiv n ((cochainCurriedEquiv R A n).symm f) x).symm

theorem curriedEval_equiv_cons (n : ℕ) (f : Cochain R A (n + 1)) (a : A) (x : Fin n → A) :
    curriedEval n (cochainCurriedEquiv R A (n + 1) f a) x = f (Fin.cons a x) := by
  change curriedEval n (cochainCurriedEquiv R A n (f.curryLeft a)) x = _
  rw [curriedEval_equiv]
  rfl

/-- Postcompose the output of a cochain with a linear endomorphism. -/
def curriedPost : (n : ℕ) → Unary R A →ₗ[R] Module.End R (Curried R A n)
  | 0 => LinearMap.id
  | n + 1 =>
    { toFun X := LinearMap.compRight R (curriedPost n X)
      map_add' _ _ := by ext f a; simp
      map_smul' _ _ := by ext f a; simp }

@[simp] theorem curriedPost_zero (X : Unary R A) (a : A) :
    curriedPost 0 X a = X a := rfl

@[simp] theorem curriedPost_succ (n : ℕ) (X : Unary R A)
    (f : Curried R A (n + 1)) (a : A) :
    curriedPost (n + 1) X f a = curriedPost n X (f a) := rfl

theorem curriedPost_comp (n : ℕ) (X Y : Unary R A) (f : Curried R A n) :
    curriedPost n (X.comp Y) f = curriedPost n X (curriedPost n Y f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext a
    exact ih (f a)

@[simp] theorem curriedEval_post (n : ℕ) (X : Unary R A) (f : Curried R A n)
    (x : Fin n → A) :
    curriedEval n (curriedPost n X f) x = X (curriedEval n f x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (f (x 0)) (Fin.tail x)

end EnvelopingIsomorphism.Deformation
