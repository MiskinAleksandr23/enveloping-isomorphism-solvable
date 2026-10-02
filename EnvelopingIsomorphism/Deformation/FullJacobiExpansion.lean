import EnvelopingIsomorphism.Deformation.FullAssociator

/-! The algebraic Jacobi expansion in all integer degrees, before imposing pre-Lie symmetry. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

attribute [local irreducible] fullCochainCongr

set_option maxHeartbeats 2000000 in
/-- The full Jacobi defect is a sum of three insertion-associator symmetry defects. -/
theorem fullJacobiator_eq_associators (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) :
    fullJacobiator p q r f g h =
      -(fullAssociator p q r f g h - koszulSign R q r •
        fullCochainCongr (by omega : (p + r) + q = (p + q) + r)
          (fullAssociator p r q f h g)) +
      koszulSign R p q • fullCochainCongr (by omega : (q + p) + r = (p + q) + r)
        (fullAssociator q p r g f h - koszulSign R p r •
          fullCochainCongr (by omega : (q + r) + p = (q + p) + r)
            (fullAssociator q r p g h f)) -
      (koszulSign R p r * koszulSign R q r) •
        fullCochainCongr (by omega : (r + p) + q = (p + q) + r)
        (fullAssociator r p q h f g - koszulSign R p q •
          fullCochainCongr (by omega : (r + q) + p = (r + p) + q)
            (fullAssociator r q p h g f)) := by
  simp +instances only [fullJacobiator, fullBracket_eq_preLie (R := R) (A := A), fullAssociator,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  simp only [koszulSign_add_left, koszulSign_add_right, koszulSign_comm q p]
  repeat' first
    | rw [fullPreLie_cast_left]
    | rw [fullPreLie_cast_right]
    | rw [fullCochainCongr_trans]
    | rw [fullCochainCongr_self]
  match_scalars
  all_goals ring_nf
  all_goals simp only [pow_two, koszulSign_square, one_mul]

end EnvelopingIsomorphism.Deformation
