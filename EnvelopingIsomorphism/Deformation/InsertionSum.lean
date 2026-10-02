import EnvelopingIsomorphism.Deformation.Gerstenhaber
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Module

/-!
Finite-slot indexing for partial insertion and the signed Gerstenhaber sum.
This is the bridge from recursive operations to the finite-index cancellation
needed in the graded pre-Lie and Jacobi identities.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Insert an n-ary cochain in slot i of an (m+1)-ary cochain. -/
def curriedInsertAt : (m n : ℕ) → Fin (m + 1) →
    Curried R A (m + 1) →ₗ[R] Curried R A n →ₗ[R] Curried R A (m + n)
  | 0, n, _ => curriedInsertHead 0 n
  | m + 1, n, i => Fin.cases (curriedInsertHead (m + 1) n)
      (fun j => (curriedLiftPrefix (curriedInsertAt m n j)).compr₂
        (curriedCongr (Nat.add_right_comm m n 1)).toLinearMap) i

@[simp] theorem curriedInsertAt_zero (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A n) :
    curriedInsertAt m n 0 f g = curriedInsertHead m n f g := by cases m <;> rfl

/-- Partial insertion respects arity transport and equality of finite slot values. -/
theorem curriedInsertAt_heq {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (i : Fin (m + 1)) (j : Fin (m' + 1)) (hi : i.val = j.val)
    (f : Curried R A (m + 1)) (f' : Curried R A (m' + 1)) (hf : HEq f f')
    (g : Curried R A n) (g' : Curried R A n') (hg : HEq g g') :
    HEq (curriedInsertAt m n i f g) (curriedInsertAt m' n' j f' g') := by
  subst m'
  subst n'
  have hij : i = j := Fin.ext hi
  subst j
  have hff' := eq_of_heq hf
  have hgg' := eq_of_heq hg
  subst f'
  subst g'
  rfl

/-- Removing an unchanged first argument shifts the insertion slot down by one. -/
theorem curriedInsertAt_succ (m n : ℕ) (i : Fin (m + 1))
    (f : Curried R A (m + 1 + 1)) (g : Curried R A n) :
    curriedCongr (Nat.add_right_comm m 1 n) (curriedInsertAt (m + 1) n i.succ f g) =
      curriedLiftPrefix (curriedInsertAt m n i) f g := by
  exact (curriedCongr_trans (Nat.add_right_comm m n 1) (Nat.add_right_comm m 1 n)
    (curriedLiftPrefix (curriedInsertAt m n i) f g)).trans rfl

@[simp] theorem curriedInsertAt_succ_eq (m n : ℕ) (i : Fin (m + 1))
    (f : Curried R A (m + 1 + 1)) (g : Curried R A n) :
    curriedInsertAt (m + 1) n i.succ f g = curriedCongr (Nat.add_right_comm m n 1)
      (curriedLiftPrefix (curriedInsertAt m n i) f g) := rfl

/-- Prefix extension depends linearly on the inserted bilinear operation. -/
def curriedLiftPrefixLinear {m n l : ℕ} :
    (Curried R A m →ₗ[R] Curried R A n →ₗ[R] Curried R A l) →ₗ[R]
      Curried R A (m + 1) →ₗ[R] Curried R A n →ₗ[R] Curried R A (l + 1) where
  toFun := curriedLiftPrefix
  map_add' _ _ := by ext f g a; rfl
  map_smul' _ _ := by ext f g a; rfl

theorem curriedLiftPrefix_sum {ι : Type*} [Fintype ι] {m n l : ℕ}
    (F : ι → Curried R A m →ₗ[R] Curried R A n →ₗ[R] Curried R A l)
    (c : ι → R) (f : Curried R A (m + 1)) (g : Curried R A n) :
    curriedLiftPrefix (∑ i, c i • F i) f g = ∑ i, c i • curriedLiftPrefix (F i) f g := by
  change curriedLiftPrefixLinear (∑ i, c i • F i) f g = _
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

/-- The recursive Gerstenhaber operation is exactly its finite signed insertion sum. -/
theorem curriedPreLie_eq_sum (m n : ℕ) :
    curriedPreLie (R := R) (A := A) n m =
      ∑ i : Fin (m + 1), (-1 : R) ^ (i.val * (n + 1)) • curriedInsertAt m n i := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.zero_mul, pow_zero, one_smul]
    rfl
  | succ m ih =>
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro g
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [curriedPreLie_succ, ih, curriedLiftPrefix_sum, map_sum]
    simp only [map_smul, Finset.smul_sum, smul_smul]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_mul, pow_zero, one_smul, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm (n + 1) (i.val * (n + 1))]

theorem curriedPreLie_eq_sum_apply (m n : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A n) :
    curriedPreLie n m f g =
      ∑ i : Fin (m + 1), (-1 : R) ^ (i.val * (n + 1)) • curriedInsertAt m n i f g := by
  rw [curriedPreLie_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

end EnvelopingIsomorphism.Deformation
