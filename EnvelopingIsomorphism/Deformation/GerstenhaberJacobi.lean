import EnvelopingIsomorphism.Deformation.PreLieCancellation
import Mathlib.Tactic.Module

/-! Graded Jacobi for the Gerstenhaber bracket, derived from the actual insertion identity. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

@[simp] theorem curriedCongr_self {n : ℕ} (h : n = n) (f : Curried R A n) :
    curriedCongr h f = f := by cases h; rfl

theorem curriedPreLie_cast_outer {m m' n : ℕ} (hm : m + 1 = m' + 1)
    (f : Curried R A (m + 1)) (g : Curried R A n) :
    curriedPreLie n m' (curriedCongr hm f) g =
      curriedCongr (by omega : m + n = m' + n) (curriedPreLie n m f g) := by
  have h := Nat.succ.inj hm
  subst m'
  rfl

theorem curriedPreLie_cast_inner {m n n' : ℕ} (hn : n = n')
    (f : Curried R A (m + 1)) (g : Curried R A n) :
    curriedPreLie n' m f (curriedCongr hn g) =
      curriedCongr (congrArg (m + ·) hn) (curriedPreLie n m f g) := by
  subst n'
  rfl

attribute [local irreducible] curriedCongr

def curriedJacobiator (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    Curried R A ((m + n) + (r + 1)) :=
  curriedCongr (Nat.add_assoc m n (r + 1)).symm
    (curriedBracket m (n + r) f (curriedBracket n r g h)) -
      curriedBracket (m + n) r (curriedBracket m n f g) h -
    (-1 : R) ^ (m * n) • curriedCongr (by omega : n + ((m + r) + 1) = (m + n) + (r + 1))
      (curriedBracket n (m + r) g (curriedBracket m r f h))

set_option maxHeartbeats 2000000 in
/-- The Jacobi defect is the sum of three signed pre-Lie symmetry defects. -/
theorem curriedJacobiator_eq_associators (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedJacobiator m n r f g h =
      -(curriedAssociator m n r f g h - (-1 : R) ^ (n * r) •
        curriedCongr (by omega : (m + r) + (n + 1) = (m + n) + (r + 1))
          (curriedAssociator m r n f h g)) +
      (-1 : R) ^ (m * n) • curriedCongr
        (by omega : (n + m) + (r + 1) = (m + n) + (r + 1))
        (curriedAssociator n m r g f h - (-1 : R) ^ (m * r) •
          curriedCongr (by omega : (n + r) + (m + 1) = (n + m) + (r + 1))
            (curriedAssociator n r m g h f)) -
      (((-1 : R) ^ (m * r)) * ((-1 : R) ^ (n * r))) • curriedCongr
        (by omega : (r + m) + (n + 1) = (m + n) + (r + 1))
        (curriedAssociator r m n h f g - (-1 : R) ^ (m * n) •
          curriedCongr (by omega : (r + n) + (m + 1) = (r + m) + (n + 1))
            (curriedAssociator r n m h g f)) := by
  simp +instances only [curriedJacobiator, curriedBracket, curriedAssociator,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [Nat.mul_add, Nat.add_mul, pow_add, Nat.mul_comm n m]
  repeat' first
    | rw [curriedPreLie_cast_outer]
    | rw [curriedPreLie_cast_inner]
    | rw [curriedCongr_trans]
    | rw [curriedCongr_self]
  match_scalars
  all_goals ring_nf
  all_goals simp [Nat.mul_comm (m * n) 2, pow_mul]

/-- The Jacobi defect vanishes by the three proved graded pre-Lie symmetries. -/
theorem curriedJacobiator_zero (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedJacobiator m n r f g h = 0 := by
  rw [curriedJacobiator_eq_associators]
  have h₁ := sub_eq_zero.mpr (curriedAssociator_graded_symm m n r f g h)
  have h₂ := sub_eq_zero.mpr (curriedAssociator_graded_symm n m r g f h)
  have h₃ := sub_eq_zero.mpr (curriedAssociator_graded_symm r m n h f g)
  rw [h₁, h₂, h₃]
  simp only [neg_zero, map_zero, smul_zero, add_zero, sub_zero]

/-- Graded Jacobi for genuine full cochains in all nonnegative shifted degrees. -/
theorem curriedBracket_jacobi (m n r : ℕ) (f : Curried R A (m + 1))
    (g : Curried R A (n + 1)) (h : Curried R A (r + 1)) :
    curriedCongr (Nat.add_assoc m n (r + 1)).symm
      (curriedBracket m (n + r) f (curriedBracket n r g h)) =
        curriedBracket (m + n) r (curriedBracket m n f g) h +
      (-1 : R) ^ (m * n) • curriedCongr
        (by omega : n + ((m + r) + 1) = (m + n) + (r + 1))
        (curriedBracket n (m + r) g (curriedBracket m r f h)) := by
  have hj := curriedJacobiator_zero m n r f g h
  change _ - _ - _ = 0 at hj
  rw [sub_sub] at hj
  exact sub_eq_zero.mp hj

end EnvelopingIsomorphism.Deformation
