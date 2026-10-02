import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChildShapeDecomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Exact finite parent/child counting for forest chart dimensions.
Every nonroot node contributes exactly once, as a child of its predecessor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDimensionCount

open ForestChildShapeDecomposition
open scoped Classical BigOperators

variable (T : RootedTree) [Fintype T]

def nonrootChildEquiv : {u : T // u ≠ ⊥} ≃ (v : Parent T) × Child T v.val where
  toFun u := ⟨predecessorParent T u.val u.property, predecessorChild T u.val u.property⟩
  invFun p := ⟨p.2.val, ne_of_gt (lt_of_le_of_lt bot_le p.2.property.lt)⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, ⟨u, hu⟩⟩
    have hp := hu.pred_eq
    dsimp only at hp
    subst v
    rfl

theorem sum_children {A : Type*} [AddCommMonoid A] (w : T → A) :
    (∑ v : Parent T, ∑ u : Child T v.val, w u.val) = ∑ u : {u : T // u ≠ ⊥}, w u.val := by
  calc
    _ = ∑ p : (v : Parent T) × Child T v.val, w p.2.val :=
      (Fintype.sum_sigma (fun p : (v : Parent T) × Child T v.val => w p.2.val)).symm
    _ = _ := by
      symm
      apply Fintype.sum_equiv (nonrootChildEquiv T)
      intro u
      rfl

theorem card_children : (∑ v : Parent T, Fintype.card (Child T v.val)) + 1 = Fintype.card T := by
  have h := sum_children T (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [h, Fintype.card_subtype_compl (fun u : T => u = ⊥)]
  have hc : Fintype.card {u : T // u = ⊥} = 1 := by simp
  rw [hc]
  have hn : 0 < Fintype.card T := Fintype.card_pos
  omega

/-- Weighted tree Euler identity, with no valency or nontriviality premise. -/
theorem weighted_euler {A : Type*} [AddCommGroup A] (w : T → A) :
    (∑ v : Parent T, ((∑ u : Child T v.val, w u.val) - w v.val)) =
      (∑ u : {u : T // IsMax u}, w u.val) - w ⊥ := by
  rw [Finset.sum_sub_distrib, sum_children]
  letI : Fintype {u : T // u = ⊥} := Subtype.fintype (fun u : T => u = ⊥)
  have hp := Fintype.sum_subtype_add_sum_subtype (IsMax : T → Prop) w
  have hr := Fintype.sum_subtype_add_sum_subtype (fun u : T => u = ⊥) w
  have hz : (∑ u : {u : T // u = ⊥}, w u.val) = w ⊥ := by
    have he (u : {u : T // u = ⊥}) : w u.val = w ⊥ := congrArg w u.property
    simp only [he, Finset.sum_const, Finset.card_univ]
    simp
  change (∑ u : {u : T // u = ⊥}, w u.val) +
    (∑ u : {u : T // u ≠ ⊥}, w u.val) = ∑ u, w u at hr
  rw [hz] at hr
  change (∑ u : {u : T // IsMax u}, w u.val) + (∑ v : Parent T, w v.val) = ∑ u, w u at hp
  change w ⊥ + (∑ u : {u : T // u ≠ ⊥}, w u.val) = ∑ u, w u at hr
  calc
    _ = (w ⊥ + ∑ u : {u : T // u ≠ ⊥}, w u.val) -
        (w ⊥ + ∑ v : Parent T, w v.val) := by abel
    _ = ((∑ u : {u : T // IsMax u}, w u.val) + ∑ v : Parent T, w v.val) -
        (w ⊥ + ∑ v : Parent T, w v.val) := by rw [hr, ← hp]
    _ = _ := by abel

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDimensionCount
