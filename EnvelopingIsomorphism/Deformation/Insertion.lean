import EnvelopingIsomorphism.Deformation.Curried
import EnvelopingIsomorphism.Deformation.LowArity

/-!
Partial insertions of full cochains in arbitrary arity, including a zero-ary
inner cochain.  Prefix/suffix indexing keeps the recursive maps free of casts:
an outer operation has `p` arguments before the slot and `q` after it.

These are actual multilinear operations via `cochainCurriedEquiv`, not an
abstract operad assumed to satisfy insertion identities.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Insert a cochain in the first slot; `q` outer slots remain after it. -/
def curriedInsertHead (q : ℕ) : (r : ℕ) →
    Curried R A (q + 1) →ₗ[R] Curried R A r →ₗ[R] Curried R A (q + r)
  | 0 => LinearMap.id
  | r + 1 =>
    { toFun f := LinearMap.compRight R (curriedInsertHead q r f)
      map_add' _ _ := by ext g a; simp
      map_smul' _ _ := by ext g a; simp }

@[simp] theorem curriedInsertHead_zero (q : ℕ) (f : Curried R A (q + 1)) (a : A) :
    curriedInsertHead q 0 f a = f a := rfl

@[simp] theorem curriedInsertHead_succ (q r : ℕ) (f : Curried R A (q + 1))
    (g : Curried R A (r + 1)) (a : A) :
    curriedInsertHead q (r + 1) f g a = curriedInsertHead q r f (g a) := rfl

/-- Extend a bilinear operation on cochains past one unchanged prefix argument. -/
def curriedLiftPrefix {m r s : ℕ}
    (F : Curried R A m →ₗ[R] Curried R A r →ₗ[R] Curried R A s) :
    Curried R A (m + 1) →ₗ[R] Curried R A r →ₗ[R] Curried R A (s + 1) :=
  LinearMap.mk₂ R (fun f g => (F.flip g).comp f)
    (by
      intro f g x
      apply LinearMap.ext
      intro a
      change F (f a + g a) x = F (f a) x + F (g a) x
      simp)
    (by
      intro c f x
      apply LinearMap.ext
      intro a
      change F (c • f a) x = c • F (f a) x
      simp)
    (by
      intro f g h
      apply LinearMap.ext
      intro a
      exact (F (f a)).map_add g h)
    (by
      intro c f g
      apply LinearMap.ext
      intro a
      exact (F (f a)).map_smul c g)

@[simp] theorem curriedLiftPrefix_apply {m r s : ℕ}
    (F : Curried R A m →ₗ[R] Curried R A r →ₗ[R] Curried R A s)
    (f : Curried R A (m + 1)) (g : Curried R A r) (a : A) :
    curriedLiftPrefix F f g a = F (f a) g := rfl

/-- Partial insertion with `p` arguments before the slot and `q` arguments after it. -/
def curriedInsert (q r : ℕ) : (p : ℕ) →
    Curried R A ((q + 1) + p) →ₗ[R] Curried R A r →ₗ[R] Curried R A ((q + r) + p)
  | 0 => curriedInsertHead q r
  | p + 1 => curriedLiftPrefix (curriedInsert q r p)

@[simp] theorem curriedInsert_zero (q r : ℕ) :
    curriedInsert (R := R) (A := A) q r 0 = curriedInsertHead q r := rfl

@[simp] theorem curriedInsert_succ (p q r : ℕ)
    (f : Curried R A ((q + 1) + (p + 1))) (g : Curried R A r) (a : A) :
    curriedInsert q r (p + 1) f g a = curriedInsert q r p (f a) g := rfl

/-- Partial insertion transported to the full multilinear cochain spaces. -/
def cochainInsert (p q r : ℕ) :
    Cochain R A ((q + 1) + p) →ₗ[R] Cochain R A r →ₗ[R] Cochain R A ((q + r) + p) :=
  (((curriedInsert q r p).comp
      (cochainCurriedEquiv R A ((q + 1) + p)).toLinearMap).compl₂
        (cochainCurriedEquiv R A r).toLinearMap).compr₂
          (cochainCurriedEquiv R A ((q + r) + p)).symm.toLinearMap

@[simp] theorem cochainInsert_apply (p q r : ℕ)
    (f : Cochain R A ((q + 1) + p)) (g : Cochain R A r) :
    cochainInsert p q r f g = (cochainCurriedEquiv R A ((q + r) + p)).symm
      (curriedInsert q r p (cochainCurriedEquiv R A ((q + 1) + p) f)
        (cochainCurriedEquiv R A r g)) := rfl

/-- Arbitrary-arity insertion agrees with the previously checked binary first slot. -/
theorem curriedInsert_binary_left (μ ν : Binary R A) :
    curriedInsert 1 2 0 μ ν = insertLeft μ ν := by ext a b c; rfl

/-- Arbitrary-arity insertion agrees with the previously checked binary second slot. -/
theorem curriedInsert_binary_right (μ ν : Binary R A) :
    curriedInsert 0 2 1 μ ν = insertRight μ ν := by ext a b c; rfl

/-- Inserting a constant is retained; it is essential in degree -1. -/
theorem curriedInsert_constant_left (μ : Binary R A) (a : A) :
    curriedInsert 1 0 0 μ a = μ a := rfl

theorem curriedInsert_constant_right (μ : Binary R A) (a : A) :
    curriedInsert 0 0 1 μ a = μ.flip a := by ext b; rfl

/-- Insertion of a unary map in the first slot is ordinary precomposition. -/
theorem curriedInsertHead_unary (q : ℕ) (f : Curried R A (q + 1)) (X : Unary R A) :
    curriedInsertHead q 1 f X = f.comp X := rfl

/-- Inserting an arbitrary cochain into a unary outer map is output postcomposition. -/
theorem curriedInsertHead_outer_unary (r : ℕ) (X : Unary R A) (g : Curried R A r) :
    curriedCongr (Nat.zero_add r) (curriedInsertHead 0 r X g) = curriedPost r X g := by
  induction r with
  | zero => rfl
  | succ r ih =>
    apply LinearMap.ext
    intro a
    exact (curriedCongr_succ (Nat.zero_add r)
      (curriedInsertHead 0 (r + 1) X g) a).trans (ih (g a))

end EnvelopingIsomorphism.Deformation
