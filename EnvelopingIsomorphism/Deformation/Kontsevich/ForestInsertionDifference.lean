import EnvelopingIsomorphism.Deformation.Kontsevich.AncestorScaleRatios
import Mathlib.Data.Fintype.EquivFin

/-! Literal tree insertion formulas and common-ancestor factorization of point differences. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference

open AncestorScaleRatios
open scoped BigOperators
open scoped Classical
open Topology

variable (t : RootedTree) [Fintype t]

/-- The branch after `c` on the ancestor path of `v`. -/
def branch (c v : t) : Finset t := by
  classical
  exact ancestors v \ ancestors c

@[simp] theorem mem_branch (c v u : t) : u ∈ branch t c v ↔ u ≤ v ∧ ¬u ≤ c := by
  classical
  simp [branch]

theorem branch_lt {c v u : t} (hcv : c ≤ v) (hu : u ∈ branch t c v) : c < u := by
  obtain ⟨huv, huc⟩ := (mem_branch t c v u).mp hu
  have hcu : c ≤ u := (le_total_of_directed huv hcv).resolve_right huc
  exact lt_iff_le_not_ge.mpr ⟨hcu, huc⟩

theorem branch_le_pred {c v u : t} (hcv : c ≤ v) (hu : u ∈ branch t c v) : c ≤ Order.pred u :=
  Order.le_pred_of_lt (branch_lt t hcv hu)

theorem branch_ne_root {c v u : t} (hu : u ∈ branch t c v) : u ≠ ⊥ := by
  intro h
  have huc := ((mem_branch t c v u).mp hu).2
  exact huc (h ▸ bot_le)

private theorem erased_ancestor_difference (c v : t) :
    (ancestors v).erase ⊥ \ (ancestors c).erase ⊥ = branch t c v := by
  classical
  ext u
  by_cases hu : u = ⊥
  · subst u
    simp [branch]
  · simp [branch, hu]

theorem exists_child_between {c v : t} (hcv : c < v) : ∃ d, c ⋖ d ∧ d ≤ v := by
  letI : WellFoundedLT t := Finite.to_wellFoundedLT
  exact exists_covBy_le_of_lt hcv

/-- There is only one immediate child of `c` on a fixed ancestor branch. -/
theorem branch_parent_eq_iff {c v d u : t} (hcd : c ⋖ d) (hdv : d ≤ v)
    (hu : u ∈ branch t c v) : Order.pred u = c ↔ u = d := by
  constructor
  · intro hpred
    have hcu := branch_lt t (hcd.le.trans hdv) hu
    have huv := ((mem_branch t c v u).mp hu).1
    rcases le_total_of_directed hdv huv with hud | hdu
    · rcases lt_or_eq_of_le hud with hlt | heq
      · have huc := Order.le_pred_of_lt hlt
        rw [hcd.pred_eq] at huc
        exact False.elim (hcu.not_ge huc)
      · exact heq
    · rcases lt_or_eq_of_le hdu with hlt | heq
      · have hdc := Order.le_pred_of_lt hlt
        rw [hpred] at hdc
        exact False.elim (hcd.lt.not_ge hdc)
      · exact heq.symm
  · rintro rfl
    exact hcd.pred_eq

omit [Fintype t] in
theorem distinct_lca_children {v w d e : t} (hd : (v ⊓ w) ⋖ d) (hdv : d ≤ v)
    (_he : (v ⊓ w) ⋖ e) (hew : e ≤ w) : d ≠ e := by
  intro hde
  have hdw : d ≤ w := hde ▸ hew
  exact hd.lt.not_ge (le_inf hdv hdw)

omit [Fintype t] in
theorem inf_lt_left_of_leaf {v w : t} (hv : IsMax v) (hne : v ≠ w) : v ⊓ w < v := by
  refine lt_iff_le_not_ge.mpr ⟨inf_le_left, ?_⟩
  intro hvi
  have hvw := hvi.trans inf_le_right
  exact hne (le_antisymm hvw (hv hvw))

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Actual leaf/node position: each nonroot ancestor contributes its child displacement
at the scale of its parent. -/
def position (ρ : t → R) (a : t → M) (v : t) : M := by
  classical
  exact ∑ u ∈ (ancestors v).erase ⊥, scale ρ (Order.pred u) • a u

/-- The residual branch displacement contains only products of radii after `c`. -/
def branchUnit (ρ : t → R) (a : t → M) (c v : t) : M :=
  ∑ u ∈ branch t c v, residualScale ρ c (Order.pred u) • a u

/-- Explicit common-source unit difference, without division by any scale. -/
def unitDifference (ρ : t → R) (a : t → M) (v w : t) : M :=
  branchUnit t ρ a (v ⊓ w) v - branchUnit t ρ a (v ⊓ w) w

theorem position_eq_common_add_branch (ρ : t → R) (a : t → M) {c v : t} (hcv : c ≤ v) :
    position t ρ a v = position t ρ a c +
      ∑ u ∈ branch t c v, scale ρ (Order.pred u) • a u := by
  classical
  have hs : (ancestors c).erase ⊥ ⊆ (ancestors v).erase ⊥ := by
    intro u hu
    simp only [Finset.mem_erase] at hu ⊢
    exact ⟨hu.1, ancestors_mono hcv hu.2⟩
  have h := Finset.sum_sdiff (f := fun u ↦ scale ρ (Order.pred u) • a u) hs
  rw [erased_ancestor_difference] at h
  simpa only [position, add_comm] using h.symm

/-- Every parent on the residual branch is at or after `c`; hence each scale factors
literally by the common scale, and finite summation preserves that factorization. -/
theorem branch_sum_factor (ρ : t → R) (a : t → M) {c v : t} (hcv : c ≤ v) :
    (∑ u ∈ branch t c v, scale ρ (Order.pred u) • a u) = scale ρ c • branchUnit t ρ a c v := by
  classical
  rw [branchUnit, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [scale_factor ρ (branch_le_pred t hcv hu), mul_smul]

theorem position_factor_from_ancestor (ρ : t → R) (a : t → M) {c v : t} (hcv : c ≤ v) :
    position t ρ a v = position t ρ a c + scale ρ c • branchUnit t ρ a c v := by
  rw [position_eq_common_add_branch t ρ a hcv, branch_sum_factor t ρ a hcv]

/-- The shared ancestor terms cancel and the difference has exactly the LCA scale as a factor. -/
theorem position_sub_position (ρ : t → R) (a : t → M) (v w : t) :
    position t ρ a v - position t ρ a w = scale ρ (v ⊓ w) • unitDifference t ρ a v w := by
  rw [position_factor_from_ancestor t ρ a (inf_le_left : v ⊓ w ≤ v),
    position_factor_from_ancestor t ρ a (inf_le_right : v ⊓ w ≤ w)]
  simp only [unitDifference, smul_sub]
  abel

theorem translated_position_sub (ρ : t → R) (a : t → M) (z : M) (v w : t) :
    (z + position t ρ a v) - (z + position t ρ a w) =
      scale ρ (v ⊓ w) • unitDifference t ρ a v w := by
  simpa only [add_sub_add_left_eq_sub] using position_sub_position t ρ a v w

@[simp] theorem branchUnit_self (ρ : t → R) (a : t → M) (c : t) : branchUnit t ρ a c c = 0 := by
  classical
  simp [branchUnit, branch]

theorem residualScale_eq_zero_of_lt (ρ : t → R) {c z : t} (hcz : c < z) (hz : ρ z = 0) :
    residualScale ρ c z = 0 := by
  unfold residualScale
  apply Finset.prod_eq_zero (i := z)
  · simp only [Finset.mem_sdiff, mem_ancestors]
    exact ⟨le_rfl, hcz.not_ge⟩
  · exact hz

/-- On the full descendant-radius-zero face, each branch unit is exactly its first
child shape. Descendant radii are local radius parameters, not absolute scales. -/
theorem branchUnit_eq_child_at_face (ρ : t → R) (a : t → M) {c v d : t}
    (hcd : c ⋖ d) (hdv : d ≤ v) (hzero : ∀ u, c < u → ρ u = 0) :
    branchUnit t ρ a c v = a d := by
  have hdmem : d ∈ branch t c v := (mem_branch t c v d).mpr ⟨hdv, hcd.lt.not_ge⟩
  calc
    branchUnit t ρ a c v = residualScale ρ c (Order.pred d) • a d := by
      unfold branchUnit
      apply Finset.sum_eq_single d
      · intro u hu hne
        have hle := branch_le_pred t (hcd.le.trans hdv) hu
        have hpne : Order.pred u ≠ c := fun hp ↦ hne ((branch_parent_eq_iff t hcd hdv hu).mp hp)
        have hlt : c < Order.pred u :=
          lt_iff_le_not_ge.mpr ⟨hle, fun hrev ↦ hpne (le_antisymm hrev hle)⟩
        rw [residualScale_eq_zero_of_lt t ρ hlt (hzero _ hlt), zero_smul]
      · intro hnot
        exact False.elim (hnot hdmem)
    _ = a d := by rw [hcd.pred_eq, residualScale_self, one_smul]

theorem unitDifference_eq_shapes_at_face (ρ : t → R) (a : t → M) {v w d e : t}
    (hd : (v ⊓ w) ⋖ d) (hdv : d ≤ v) (he : (v ⊓ w) ⋖ e) (hew : e ≤ w)
    (hzero : ∀ u, v ⊓ w < u → ρ u = 0) : unitDifference t ρ a v w = a d - a e := by
  rw [unitDifference, branchUnit_eq_child_at_face t ρ a hd hdv hzero,
    branchUnit_eq_child_at_face t ρ a he hew hzero]

/-- Pairwise distinct immediate-child shapes force the actual unit difference to be
nonzero at the descendant-radius-zero face. -/
theorem unitDifference_ne_zero_at_face (ρ : t → R) (a : t → M) {v w d e : t}
    (hd : (v ⊓ w) ⋖ d) (hdv : d ≤ v) (he : (v ⊓ w) ⋖ e) (hew : e ≤ w)
    (hzero : ∀ u, v ⊓ w < u → ρ u = 0)
    (hshape : ∀ d e, (v ⊓ w) ⋖ d → (v ⊓ w) ⋖ e → d ≠ e → a d ≠ a e) :
    unitDifference t ρ a v w ≠ 0 := by
  rw [unitDifference_eq_shapes_at_face t ρ a hd hdv he hew hzero]
  exact sub_ne_zero.mpr (hshape d e hd he (distinct_lca_children t hd hdv he hew))

/-- Distinct leaves automatically determine the two distinct immediate-child branches. -/
theorem leaf_unitDifference_ne_zero_at_face (ρ : t → R) (a : t → M) {v w : t}
    (hv : IsMax v) (hw : IsMax w) (hne : v ≠ w)
    (hzero : ∀ u, v ⊓ w < u → ρ u = 0)
    (hshape : ∀ d e, (v ⊓ w) ⋖ d → (v ⊓ w) ⋖ e → d ≠ e → a d ≠ a e) :
    unitDifference t ρ a v w ≠ 0 := by
  obtain ⟨d, hd, hdv⟩ := exists_child_between t (inf_lt_left_of_leaf t hv hne)
  have hiw : v ⊓ w < w := by simpa only [inf_comm] using inf_lt_left_of_leaf t hw hne.symm
  obtain ⟨e, he, hew⟩ := exists_child_between t hiw
  exact unitDifference_ne_zero_at_face t ρ a hd hdv he hew hzero hshape

end Algebra

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop] theorem contDiff_position (v : t) :
    ContDiff ℝ ⊤ (fun x : (t → ℝ) × (t → E) ↦ position t x.1 x.2 v) := by
  classical
  unfold position
  apply ContDiff.sum
  intro u hu
  exact ((contDiff_scale _).comp contDiff_fst).smul (by fun_prop)

@[fun_prop] theorem contDiff_branchUnit (c v : t) :
    ContDiff ℝ ⊤ (fun x : (t → ℝ) × (t → E) ↦ branchUnit t x.1 x.2 c v) := by
  unfold branchUnit
  apply ContDiff.sum
  intro u hu
  exact ((contDiff_residualScale _ _).comp contDiff_fst).smul (by fun_prop)

/-- The unit difference itself is a polynomial insertion expression, smooth even when
several radii vanish; its nonvanishing is a separate geometric shape condition. -/
@[fun_prop] theorem contDiff_unitDifference (v w : t) :
    ContDiff ℝ ⊤ (fun x : (t → ℝ) × (t → E) ↦ unitDifference t x.1 x.2 v w) :=
  (contDiff_branchUnit t _ _).sub (contDiff_branchUnit t _ _)

theorem isOpen_unitDifference_ne_zero (v w : t) :
    IsOpen {x : (t → ℝ) × (t → E) | unitDifference t x.1 x.2 v w ≠ 0} :=
  (isClosed_eq (contDiff_unitDifference t v w).continuous continuous_const).isOpen_compl

end Smooth

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference
