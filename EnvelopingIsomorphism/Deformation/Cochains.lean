import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.BilinearMap

/-!
The full Hochschild cochain spaces, including arity zero.  No condition of
being normalized or differential is imposed.  Arity `n` has shifted degree
`(n : ℤ) - 1`.

The low arities are identified with ordinary curried linear maps, so subsequent
identities can use Mathlib's existing linear algebra without manipulating tuples.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- All multilinear Hochschild cochains, indexed by their arity. -/
abbrev Cochain (n : ℕ) := MultilinearMap R (fun _ : Fin n => A) A

/-- Hochschild cohomological degree after the Gerstenhaber shift. -/
def cochainDegree (n : ℕ) : ℤ := (n : ℤ) - 1

@[simp] theorem cochainDegree_zero : cochainDegree 0 = -1 := rfl
@[simp] theorem cochainDegree_one : cochainDegree 1 = 0 := rfl
@[simp] theorem cochainDegree_two : cochainDegree 2 = 1 := rfl

abbrev Unary := A →ₗ[R] A
abbrev Binary := A →ₗ[R] A →ₗ[R] A
abbrev Ternary := A →ₗ[R] A →ₗ[R] A →ₗ[R] A

/-- A zero-ary cochain is an element of the algebra, not zero. -/
def cochainZeroEquiv : Cochain R A 0 ≃ₗ[R] A where
  toFun f := f Fin.elim0
  invFun a := MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => A) a
  left_inv f := by
    ext x
    change f Fin.elim0 = f x
    exact congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- One-ary cochains are all linear endomorphisms. -/
def cochainOneEquiv : Cochain R A 1 ≃ₗ[R] Unary R A where
  toEquiv := (MultilinearMap.ofSubsingleton R A A (0 : Fin 1)).symm
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl

/-- Currying a two-ary cochain gives an ordinary bilinear map. -/
def cochainTwoEquiv : Cochain R A 2 ≃ₗ[R] Binary R A :=
  (multilinearCurryLeftEquiv R (fun _ : Fin 2 => A) A).trans
    ((LinearEquiv.refl R A).arrowCongr (cochainOneEquiv R A))

/-- Currying a three-ary cochain gives an ordinary trilinear map. -/
def cochainThreeEquiv : Cochain R A 3 ≃ₗ[R] Ternary R A :=
  (multilinearCurryLeftEquiv R (fun _ : Fin 3 => A) A).trans
    ((LinearEquiv.refl R A).arrowCongr (cochainTwoEquiv R A))

@[simp] theorem cochainZeroEquiv_symm_apply (a : A) (x : Fin 0 → A) :
    (cochainZeroEquiv R A).symm a x = a := rfl

@[simp] theorem cochainOneEquiv_symm_apply (f : Unary R A) (x : Fin 1 → A) :
    (cochainOneEquiv R A).symm f x = f (x 0) := rfl

@[simp] theorem cochainTwoEquiv_symm_apply (f : Binary R A) (x : Fin 2 → A) :
    (cochainTwoEquiv R A).symm f x = f (x 0) (x 1) := rfl

@[simp] theorem cochainThreeEquiv_symm_apply (f : Ternary R A) (x : Fin 3 → A) :
    (cochainThreeEquiv R A).symm f x = f (x 0) (x 1) (x 2) := rfl

end EnvelopingIsomorphism.Deformation
