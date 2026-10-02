import Mathlib.Order.SuccPred.Tree
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Ancestor-product scales and smooth common-scale cancellation for comparable tree nodes. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.AncestorScaleRatios

open scoped BigOperators
open Topology

section Products

variable {Node : Type*} [Fintype Node] [PartialOrder Node]

/-- Ancestors include the node itself and the root. -/
def ancestors (v : Node) : Finset Node := by
  classical
  exact Finset.univ.filter (fun u ↦ u ≤ v)

@[simp] theorem mem_ancestors (u v : Node) : u ∈ ancestors v ↔ u ≤ v := by
  classical
  simp [ancestors]

theorem ancestors_mono {v w : Node} (h : v ≤ w) : ancestors v ⊆ ancestors w := by
  intro u hu
  exact (mem_ancestors u w).mpr (le_trans ((mem_ancestors u v).mp hu) h)

/-- The absolute scale is the product of all ancestor radii. -/
def scale {A : Type*} [CommMonoid A] (ρ : Node → A) (v : Node) : A :=
  ∏ u ∈ ancestors v, ρ u

/-- Only the radii after the common ancestor remain in this product. -/
def residualScale {A : Type*} [CommMonoid A] (ρ : Node → A) (v w : Node) : A := by
  classical
  exact ∏ u ∈ ancestors w \ ancestors v, ρ u

@[simp] theorem residualScale_self {A : Type*} [CommMonoid A] (ρ : Node → A) (v : Node) :
    residualScale ρ v v = 1 := by
  classical
  simp [residualScale]

/-- Ancestor inclusion gives exact multiplicative factorization, even at zero radii. -/
theorem scale_factor {A : Type*} [CommMonoid A] (ρ : Node → A) {v w : Node} (h : v ≤ w) :
    scale ρ w = scale ρ v * residualScale ρ v w := by
  classical
  simpa only [scale, residualScale, mul_comm] using
    (Finset.prod_sdiff (f := ρ) (ancestors_mono h)).symm

theorem scale_pos (ρ : Node → ℝ) (hρ : ∀ u, 0 < ρ u) (v : Node) : 0 < scale ρ v :=
  Finset.prod_pos (fun u _ ↦ hρ u)

theorem residualScale_nonneg (ρ : Node → ℝ) (hρ : ∀ u, 0 ≤ ρ u) (v w : Node) :
    0 ≤ residualScale ρ v w := by
  classical
  exact Finset.prod_nonneg (fun u _ ↦ hρ u)

theorem residualScale_pos (ρ : Node → ℝ) (hρ : ∀ u, 0 < ρ u) (v w : Node) :
    0 < residualScale ρ v w := by
  classical
  exact Finset.prod_pos (fun u _ ↦ hρ u)

@[fun_prop] theorem contDiff_scale (v : Node) : ContDiff ℝ ⊤ (fun ρ : Node → ℝ ↦ scale ρ v) := by
  unfold scale
  apply contDiff_prod
  intro u hu
  fun_prop

@[fun_prop] theorem contDiff_residualScale (v w : Node) :
    ContDiff ℝ ⊤ (fun ρ : Node → ℝ ↦ residualScale ρ v w) := by
  classical
  unfold residualScale
  apply contDiff_prod
  intro u hu
  fun_prop

end Products

section CommonSource

variable {Node : Type*} [SemilatticeInf Node] [PredOrder Node] [IsPredArchimedean Node]

/-- The two least common ancestors are comparable because both lie below the same source. -/
theorem common_source_lca_comparable (a b c : Node) :
    a ⊓ b ≤ a ⊓ c ∨ a ⊓ c ≤ a ⊓ b :=
  le_total_of_directed (inf_le_left : a ⊓ c ≤ a) (inf_le_left : a ⊓ b ≤ a)

end CommonSource

section Ratios

variable {Node : Type*} [Fintype Node] [SemilatticeInf Node]

/-- Denominator after factoring out the scale of the common ancestor. -/
def resolvedDenominator (ρ : Node → ℝ) (v w : Node) (U V : ℝ) : ℝ :=
  residualScale ρ (v ⊓ w) v * U + residualScale ρ (v ⊓ w) w * V

/-- This formula uses residual products only; it never divides one radius by another. -/
def resolvedRatio (ρ : Node → ℝ) (v w : Node) (U V : ℝ) : ℝ :=
  residualScale ρ (v ⊓ w) v * U / resolvedDenominator ρ v w U V

theorem resolvedRatio_of_le (ρ : Node → ℝ) {v w : Node} (h : v ≤ w) (U V : ℝ) :
    resolvedRatio ρ v w U V = U / (U + residualScale ρ v w * V) := by
  simp [resolvedRatio, resolvedDenominator, inf_eq_left.mpr h]

theorem resolvedRatio_of_ge (ρ : Node → ℝ) {v w : Node} (h : w ≤ v) (U V : ℝ) :
    resolvedRatio ρ v w U V = residualScale ρ w v * U / (residualScale ρ w v * U + V) := by
  simp [resolvedRatio, resolvedDenominator, inf_eq_right.mpr h]

/-- For comparable nodes one residual product is exactly one, so a positive unit length
survives in the denominator at every nonnegative-radius corner. -/
theorem resolvedDenominator_pos (ρ : Node → ℝ) (hρ : ∀ u, 0 ≤ ρ u)
    {v w : Node} (hvw : v ≤ w ∨ w ≤ v) {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    0 < resolvedDenominator ρ v w U V := by
  rcases hvw with h | h
  · simp only [resolvedDenominator, inf_eq_left.mpr h, residualScale_self, one_mul]
    exact add_pos_of_pos_of_nonneg hU (mul_nonneg (residualScale_nonneg ρ hρ v w) hV.le)
  · simp only [resolvedDenominator, inf_eq_right.mpr h, residualScale_self, one_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (residualScale_nonneg ρ hρ w v) hU.le) hV

/-- On strictly positive radii the resolved formula equals the original scale-norm ratio.
Only the nonzero common scale is cancelled. -/
theorem ratio_eq_resolvedRatio (ρ : Node → ℝ) (hρ : ∀ u, 0 < ρ u)
    (v w : Node) (U V : ℝ) :
    scale ρ v * U / (scale ρ v * U + scale ρ w * V) = resolvedRatio ρ v w U V := by
  rw [scale_factor ρ (inf_le_left : v ⊓ w ≤ v), scale_factor ρ (inf_le_right : v ⊓ w ≤ w)]
  simp only [resolvedRatio, resolvedDenominator, mul_assoc, ← mul_add]
  exact mul_div_mul_left _ _ (ne_of_gt (scale_pos ρ hρ (v ⊓ w)))

theorem resolvedRatio_mem_Icc (ρ : Node → ℝ) (hρ : ∀ u, 0 ≤ ρ u)
    {v w : Node} (hvw : v ≤ w ∨ w ≤ v) {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    resolvedRatio ρ v w U V ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := resolvedDenominator_pos ρ hρ hvw hU hV
  have hnum := mul_nonneg (residualScale_nonneg ρ hρ (v ⊓ w) v) hU.le
  have hother := mul_nonneg (residualScale_nonneg ρ hρ (v ⊓ w) w) hV.le
  refine ⟨div_nonneg hnum hd.le, ?_⟩
  apply (div_le_one hd).mpr
  exact le_add_of_nonneg_right hother

abbrev Parameters (Node : Type*) := (Node → ℝ) × ℝ × ℝ

def ValidParameters (x : Parameters Node) : Prop :=
  (∀ u, 0 ≤ x.1 u) ∧ 0 < x.2.1 ∧ 0 < x.2.2

abbrev NonnegativeParameters (Node : Type*) := {x : Parameters Node // ValidParameters x}

@[fun_prop] theorem contDiff_resolvedDenominator (v w : Node) :
    ContDiff ℝ ⊤ (fun x : Parameters Node ↦ resolvedDenominator x.1 v w x.2.1 x.2.2) := by
  unfold resolvedDenominator
  exact ((contDiff_residualScale _ _).comp contDiff_fst |>.mul contDiff_snd.fst).add
    ((contDiff_residualScale _ _).comp contDiff_fst |>.mul contDiff_snd.snd)

/-- The ambient rational expression is smooth at every admissible corner; the denominator
is nonzero there even when some or all ancestor radii vanish. -/
theorem contDiffAt_resolvedRatio {v w : Node} (hvw : v ≤ w ∨ w ≤ v)
    (x : Parameters Node) (hx : ValidParameters x) :
    ContDiffAt ℝ ⊤ (fun y : Parameters Node ↦ resolvedRatio y.1 v w y.2.1 y.2.2) x := by
  exact (((contDiff_residualScale _ _).comp contDiff_fst).mul contDiff_snd.fst).contDiffAt.div
    (contDiff_resolvedDenominator v w).contDiffAt
    (ne_of_gt (resolvedDenominator_pos x.1 hx.1 hvw hx.2.1 hx.2.2))

theorem contDiffOn_resolvedRatio {v w : Node} (hvw : v ≤ w ∨ w ≤ v) :
    ContDiffOn ℝ ⊤ (fun x : Parameters Node ↦ resolvedRatio x.1 v w x.2.1 x.2.2)
      {x | ValidParameters x} :=
  fun x hx ↦ (contDiffAt_resolvedRatio hvw x hx).contDiffWithinAt

/-- The resolved ratio as an actual value in the compact norm-ratio interval. -/
def ratioExtension (v w : Node) (hvw : v ≤ w ∨ w ≤ v)
    (x : NonnegativeParameters Node) : Set.Icc (0 : ℝ) 1 :=
  ⟨resolvedRatio x.val.1 v w x.val.2.1 x.val.2.2,
    resolvedRatio_mem_Icc x.val.1 x.property.1 hvw x.property.2.1 x.property.2.2⟩

@[fun_prop] theorem continuous_ratioExtension (v w : Node) (hvw : v ≤ w ∨ w ≤ v) :
    Continuous (ratioExtension v w hvw) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (contDiffAt_resolvedRatio hvw x.val x.property).continuousAt.comp
    continuous_subtype_val.continuousAt

theorem ratioExtension_eq_original (v w : Node) (hvw : v ≤ w ∨ w ≤ v)
    (x : NonnegativeParameters Node) (hρ : ∀ u, 0 < x.val.1 u) :
    (ratioExtension v w hvw x : ℝ) =
      scale x.val.1 v * x.val.2.1 /
        (scale x.val.1 v * x.val.2.1 + scale x.val.1 w * x.val.2.2) :=
  (ratio_eq_resolvedRatio x.val.1 hρ v w x.val.2.1 x.val.2.2).symm

end Ratios

section Trees

variable (t : RootedTree) [Fintype t]

/-- The common-source triple ratio on an ordinary finite rooted tree. -/
def tripleRatioExtension (a b c : t) : NonnegativeParameters t → Set.Icc (0 : ℝ) 1 :=
  ratioExtension (a ⊓ b) (a ⊓ c) (common_source_lca_comparable a b c)

@[fun_prop] theorem continuous_tripleRatioExtension (a b c : t) :
    Continuous (tripleRatioExtension t a b c) :=
  continuous_ratioExtension _ _ (common_source_lca_comparable a b c)

theorem contDiffAt_tripleRatio (a b c : t) (x : Parameters t) (hx : ValidParameters x) :
    ContDiffAt ℝ ⊤ (fun y : Parameters t ↦
      resolvedRatio y.1 (a ⊓ b) (a ⊓ c) y.2.1 y.2.2) x :=
  contDiffAt_resolvedRatio (common_source_lca_comparable a b c) x hx

theorem tripleRatioExtension_eq_original (a b c : t) (x : NonnegativeParameters t)
    (hρ : ∀ u, 0 < x.val.1 u) :
    (tripleRatioExtension t a b c x : ℝ) =
      scale x.val.1 (a ⊓ b) * x.val.2.1 /
        (scale x.val.1 (a ⊓ b) * x.val.2.1 + scale x.val.1 (a ⊓ c) * x.val.2.2) :=
  ratioExtension_eq_original _ _ _ x hρ

end Trees

end EnvelopingIsomorphism.Deformation.Kontsevich.AncestorScaleRatios
