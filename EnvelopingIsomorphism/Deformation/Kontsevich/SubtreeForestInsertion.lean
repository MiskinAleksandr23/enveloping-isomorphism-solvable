import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates

/-! Actual insertion units on a native rooted subtree, with its root radius reset to one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion

open AncestorScaleRatios ForestInsertionDifference ForestNormalizationTelescope
open scoped Classical

variable (T : RootedTree) [Fintype T] (c : T)

def Tree : RootedTree := (T.subtree c).coeTree
instance : Fintype (Tree T c) := inferInstanceAs (Fintype (Set.Ici c))

omit [Fintype T] in
@[simp] theorem root_val : (⊥ : Tree T c).val = c := rfl

omit [Fintype T] in
theorem inf_val (v w : Tree T c) : (v ⊓ w).val = v.val ⊓ w.val := rfl

omit [Fintype T] in
theorem child_native {v w : Tree T c} (h : v ⋖ w) : v.val ⋖ w.val := by
  refine ⟨h.lt, ?_⟩
  intro u hvu huw
  exact h.2 (c := (⟨u, v.property.trans hvu.le⟩ : Tree T c)) hvu huw

omit [Fintype T] in
theorem pred_val (v : Tree T c) (hv : v ≠ ⊥) : (Order.pred v).val = Order.pred v.val := by
  exact (child_native T c (Order.pred_covBy_of_not_isMin (not_isMin_iff_ne_bot.mpr hv))).pred_eq.symm

def radius (r : T → ℝ) (v : Tree T c) : ℝ := if v = ⊥ then 1 else r v.val
def increment (z : T → ℂ) (v : Tree T c) : ℂ := z v.val

omit [Fintype T] in
@[simp] theorem radius_root (r : T → ℝ) : radius T c r ⊥ = 1 := by simp [radius]

omit [Fintype T] in
theorem radius_nonroot (r : T → ℝ) (v : Tree T c) (hv : v ≠ ⊥) : radius T c r v = r v.val := by
  simp [radius, hv]

def inclusion : Tree T c ↪ T := ⟨Subtype.val, Subtype.val_injective⟩

/-- The native ancestor differences are literally the same finite set after
including the subtree. Ancestors at or below its root are excluded on both sides. -/
theorem branch_map (v w : Tree T c) :
    (branch (Tree T c) v w).map (inclusion T c) = branch T v.val w.val := by
  ext u
  simp only [Finset.mem_map, mem_branch]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hu
    have hcu : c ≤ u := (le_total_of_directed hu.1 w.property).resolve_right
      (fun huc => hu.2 (huc.trans v.property))
    exact ⟨⟨u, hcu⟩, hu, rfl⟩

/-- Every residual ancestor product agrees, including at zero internal radii. -/
theorem residualScale_eq (r : T → ℝ) (v w : Tree T c) :
    residualScale r v.val w.val = residualScale (radius T c r) v w := by
  change (∏ u ∈ branch T v.val w.val, r u) = ∏ u ∈ branch (Tree T c) v w, radius T c r u
  rw [← branch_map T c v w, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro u hu
  exact (radius_nonroot T c r u (branch_ne_root (Tree T c) hu)).symm

/-- The branch insertion polynomial is unchanged by native subtree restriction. -/
theorem branchUnit_eq (r : T → ℝ) (z : T → ℂ) (v w : Tree T c) :
    branchUnit T r z v.val w.val =
      branchUnit (Tree T c) (radius T c r) (increment T c z) v w := by
  unfold branchUnit
  rw [← branch_map T c v w, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  have hpred := pred_val T c u (branch_ne_root (Tree T c) hu)
  change residualScale r v.val (Order.pred u.val) • z u.val = _
  rw [← hpred, residualScale_eq T c r v (Order.pred u)]
  rfl

/-- No division by the collapsed cluster radius occurs: the full forest's
resolved pair units are exactly the subtree's resolved pair units. -/
theorem unitDifference_eq (r : T → ℝ) (z : T → ℂ) (v w : Tree T c) :
    unitDifference T r z v.val w.val =
      unitDifference (Tree T c) (radius T c r) (increment T c z) v w := by
  unfold unitDifference
  rw [← inf_val T c v w, branchUnit_eq T c r z (v ⊓ w) v, branchUnit_eq T c r z (v ⊓ w) w]

/-- The subtree position is the full tree's residual insertion from c, not its
collapsed absolute leaf position. -/
theorem position_eq_branchUnit (r : T → ℝ) (z : T → ℂ) (v : Tree T c) :
    position (Tree T c) (radius T c r) (increment T c z) v = branchUnit T r z c v.val := by
  rw [position_factor_from_ancestor (Tree T c) _ _ (bot_le : (⊥ : Tree T c) ≤ v),
    position_root, scale_root, radius_root, one_smul, zero_add]
  exact (branchUnit_eq T c r z ⊥ v).symm

theorem full_position_factor (r : T → ℝ) (z : T → ℂ) (v : Tree T c) :
    position T r z v.val = position T r z c + scale r c •
      position (Tree T c) (radius T c r) (increment T c z) v := by
  rw [position_eq_branchUnit, position_factor_from_ancestor T r z v.property]
  rfl

theorem resolvedRatio_eq (r : T → ℝ) (v w : Tree T c) (U V : ℝ) :
    resolvedRatio r v.val w.val U V = resolvedRatio (radius T c r) v w U V := by
  unfold resolvedRatio resolvedDenominator
  rw [← inf_val T c v w, residualScale_eq T c r (v ⊓ w) v, residualScale_eq T c r (v ⊓ w) w]

def parameters (p : ForestDirectionRatioCoordinates.Parameters T) :
    ForestDirectionRatioCoordinates.Parameters (Tree T c) := (radius T c p.1, increment T c p.2)

variable {I : Type*} (lab : I → Tree T c)

theorem pairUnit_eq (p : ForestDirectionRatioCoordinates.Parameters T)
    (e : ForestDirectionRatioCoordinates.Pair I) :
    ForestDirectionRatioCoordinates.pairUnit T (fun j => (lab j).val) p e =
      ForestDirectionRatioCoordinates.pairUnit (Tree T c) lab (parameters T c p) e :=
  unitDifference_eq T c p.1 p.2 _ _

theorem ratioValue_eq (p : ForestDirectionRatioCoordinates.Parameters T)
    (e : ForestDirectionRatioCoordinates.Triple I) :
    ForestDirectionRatioCoordinates.ratioValue T (fun j => (lab j).val) p e =
      ForestDirectionRatioCoordinates.ratioValue (Tree T c) lab (parameters T c p) e := by
  unfold ForestDirectionRatioCoordinates.ratioValue
  rw [pairUnit_eq T c lab, pairUnit_eq T c lab]
  change resolvedRatio p.1 ((lab e.val.1).val ⊓ (lab e.val.2.1).val)
    ((lab e.val.1).val ⊓ (lab e.val.2.2).val) _ _ = _
  rw [← inf_val T c, ← inf_val T c, resolvedRatio_eq T c]
  rfl

omit [Fintype T] in
theorem radius_nonneg (r : T → ℝ) (hr : ∀ v, 0 ≤ r v) (v : Tree T c) : 0 ≤ radius T c r v := by
  unfold radius
  split_ifs
  · exact zero_le_one
  · exact hr v.val

def domain (p : ForestDirectionRatioCoordinates.Domain T (fun j => (lab j).val)) :
    ForestDirectionRatioCoordinates.Domain (Tree T c) lab :=
  ⟨parameters T c p.val, radius_nonneg T c p.val.1 p.property.1,
    fun e => (pairUnit_eq T c lab p.val e).symm ▸ p.property.2 e⟩

/-- The entire full direction/ratio array is preserved on the subtree, even when
the removed ambient root scale is zero. -/
theorem resolvedCoordinates_eq (p : ForestDirectionRatioCoordinates.Domain T (fun j => (lab j).val)) :
    ForestDirectionRatioCoordinates.resolvedCoordinates T (fun j => (lab j).val) p =
      ForestDirectionRatioCoordinates.resolvedCoordinates (Tree T c) lab (domain T c lab p) := by
  apply Prod.ext
  · funext e
    exact congrArg complexPhase (pairUnit_eq T c lab p.val e)
  · funext e
    apply Subtype.ext
    exact ratioValue_eq T c lab p.val e

end EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion
