import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestFreeShapes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Explicit holomorphic identification of the independent complex forest coordinates
from the actual normalized leaf array. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestChartInverse

open ForestChildShapeDecomposition ComplexForestFreeShapes ComplexForestNormalizedCharts
open ComplexForestInsertion ForestInsertionDifference ForestNormalizationTelescope AncestorScaleRatios
open InteriorFiberAngleSplit Topology
open scoped Classical

variable (t : RootedTree) [Fintype t] (M : Marks t)

def representativeStep (v : t) (rec : (w : t) → v < w → {u : t // IsMax u}) : {u : t // IsMax u} :=
  if hv : IsMax v then ⟨v, hv⟩ else rec (M.anchor ⟨v, hv⟩).val (M.anchor ⟨v, hv⟩).property.lt

def representative : t → {u : t // IsMax u} :=
  (Finite.to_wellFoundedGT (α := t)).wf.fix (representativeStep t M)

theorem representative_eq (v : t) : representative t M v =
    representativeStep t M v (fun w _ ↦ representative t M w) := WellFounded.fix_eq _ _ _

def inserted (x : Coordinates t M) (v : t) : ℂ :=
  complexCartesian t (ComplexForestNormalizedCharts.includeParameters t (parameters t M x)) v

theorem inserted_child (x : Coordinates t M) (v : Parent t) (u : Child t v.val) :
    inserted t M x u.val = scale (weights t x.1) v.val * childShape t M x.2 v u + inserted t M x v.val := by
  change position t (weights t x.1) (shapeArray t M x.2) u.val = _
  rw [position_step t _ _ u.val (ne_bot_of_gt u.property.lt), u.property.pred_eq,
    shapeArray_child t M x.2 v u, smul_eq_mul]
  rfl

/-- Following the actual zero-mark children reaches a leaf at the node's center. -/
theorem representative_position (x : Coordinates t M) (v : t) :
    inserted t M x (representative t M v).val = inserted t M x v := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    rw [representative_eq]
    by_cases hv : IsMax v
    · simp [representativeStep, hv]
    · simp only [representativeStep, dif_neg hv]
      rw [ih _ (M.anchor ⟨v, hv⟩).property.lt,
        inserted_child t M x ⟨v, hv⟩ (M.anchor ⟨v, hv⟩), childShape_anchor, mul_zero, zero_add]

variable {N : ℕ} (labels : Point N ≃ {u : t // IsMax u})

def lab (j : Point N) : t := (labels j).val

omit [Fintype t] in
theorem lab_injective : Function.Injective (lab t labels) :=
  fun _ _ h ↦ labels.injective (Subtype.ext h)

def nodeCenter (η : Shape N) (v : t) : ℂ :=
  normalizedPoint η (labels.symm (representative t M v))

def gap (η : Shape N) (v : Parent t) : ℂ :=
  nodeCenter t M labels η (M.reference v).val - nodeCenter t M labels η v.val

@[fun_prop] theorem analyticAt_nodeCenter (v : t) (η : Shape N) :
    AnalyticAt ℂ (fun ζ ↦ nodeCenter t M labels ζ v) η :=
  PlanarNormalizedCoordinates.analyticAt_normalizedPoint _ η

@[fun_prop] theorem analyticAt_gap (v : Parent t) (η : Shape N) :
    AnalyticAt ℂ (fun ζ ↦ gap t M labels ζ v) η :=
  (analyticAt_nodeCenter t M labels _ η).sub (analyticAt_nodeCenter t M labels _ η)

abbrev chart := ComplexForestFreeShapes.chart t M (lab t labels)
abbrev chartDomain := ComplexForestFreeShapes.chartDomain t M (lab t labels)

def referenceDifference (x : Coordinates t M) : ℂ :=
  inserted t M x (lab t labels 1) - inserted t M x (lab t labels 0)

theorem referenceDifference_ne_zero {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) :
    referenceDifference t M labels x ≠ 0 :=
  ComplexForestNormalizedCharts.reference_ne_zero t (lab t labels) (lab_injective t labels) hx

theorem nodeCenter_chart {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) (v : t) :
    nodeCenter t M labels (chart t M labels x) v =
      (inserted t M x v - inserted t M x (lab t labels 0)) / referenceDifference t M labels x := by
  change normalizedPoint (normalizedShape t (lab t labels) (parameters t M x))
    (labels.symm (representative t M v)) = _
  rw [ComplexForestNormalizedCharts.normalizedPoint_normalizedShape t (lab t labels)
    (lab_injective t labels) hx]
  have hrep : lab t labels (labels.symm (representative t M v)) = (representative t M v).val := by
    simp [lab]
  change (inserted t M x (lab t labels (labels.symm (representative t M v))) - _) / _ = _
  rw [hrep, representative_position]
  rfl

theorem gap_chart {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) (v : Parent t) :
    gap t M labels (chart t M labels x) v = scale (weights t x.1) v.val / referenceDifference t M labels x := by
  rw [gap, nodeCenter_chart t M labels hx, nodeCenter_chart t M labels hx, ← sub_div,
    inserted_child t M x v (M.reference v), childShape_reference, mul_one]
  congr 1
  ring

theorem gap_chart_ne_zero {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) (v : Parent t) :
    gap t M labels (chart t M labels x) v ≠ 0 := by
  rw [gap_chart t M labels hx]
  exact div_ne_zero (scale_ne_zero_of_internal_weights t (weights t x.1)
    (weights_internal_ne_zero t (parameters t M x) hx.2) v.val v.property)
    (referenceDifference_ne_zero t M labels hx)

def normalParent (v : Normal t) : Parent t := ⟨v.val, ((mem_normalNodes t v.val).mp v.property).2⟩

def normalPredecessor (v : Normal t) : Parent t :=
  predecessorParent t v.val ((mem_normalNodes t v.val).mp v.property).1

/-- Every weight is a ratio of actual marked complex gaps; every free shape is
an actual child-center difference divided by its parent's gap. -/
def inverse (η : Shape N) : Coordinates t M :=
  (fun v ↦ gap t M labels η (normalParent t v) / gap t M labels η (normalPredecessor t v),
   fun p ↦ (nodeCenter t M labels η p.2.val.val - nodeCenter t M labels η p.1.val) / gap t M labels η p.1)

theorem inverse_chart {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) :
    inverse t M labels (chart t M labels x) = x := by
  apply Prod.ext
  · funext v
    change gap t M labels (chart t M labels x) (normalParent t v) /
      gap t M labels (chart t M labels x) (normalPredecessor t v) = x.1 v
    rw [gap_chart t M labels hx, gap_chart t M labels hx,
      div_div_div_cancel_right₀ (referenceDifference_ne_zero t M labels hx)]
    change scale (weights t x.1) v.val / scale (weights t x.1) (Order.pred v.val) = _
    rw [scale_step t _ _ ((mem_normalNodes t v.val).mp v.property).1, weights_normal]
    exact mul_div_cancel_right₀ _ (scale_ne_zero_of_internal_weights t (weights t x.1)
      (weights_internal_ne_zero t (parameters t M x) hx.2) _ (normalPredecessor t v).property)
  · funext p
    change (nodeCenter t M labels (chart t M labels x) p.2.val.val -
      nodeCenter t M labels (chart t M labels x) p.1.val) / gap t M labels (chart t M labels x) p.1 = x.2 p
    rw [nodeCenter_chart t M labels hx, nodeCenter_chart t M labels hx, ← sub_div,
      gap_chart t M labels hx, div_div_div_cancel_right₀ (referenceDifference_ne_zero t M labels hx),
      inserted_child t M x p.1 p.2.val]
    have hsub : scale (weights t x.1) p.1.val * childShape t M x.2 p.1 p.2.val +
        inserted t M x p.1.val - inserted t M x (lab t labels 0) -
        (inserted t M x p.1.val - inserted t M x (lab t labels 0)) =
        scale (weights t x.1) p.1.val * childShape t M x.2 p.1 p.2.val := by ring
    rw [hsub, mul_div_cancel_left₀ _ (scale_ne_zero_of_internal_weights t (weights t x.1)
      (weights_internal_ne_zero t (parameters t M x) hx.2) _ p.1.property)]
    simp only [childShape, dif_neg p.2.property.1, dif_neg p.2.property.2]

theorem analyticAt_inverse {η : Shape N} (hη : ∀ v, gap t M labels η v ≠ 0) :
    AnalyticAt ℂ (inverse t M labels) η := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro v
    exact (analyticAt_gap t M labels _ η).div (analyticAt_gap t M labels _ η) (hη _)
  · apply AnalyticAt.pi
    intro p
    exact ((analyticAt_nodeCenter t M labels _ η).sub (analyticAt_nodeCenter t M labels _ η)).div
      (analyticAt_gap t M labels _ η) (hη _)

/-- The explicitly constructed holomorphic inverse supplies a left inverse for
the actual complex derivative on the punctured chart. -/
theorem fderiv_inverse_comp {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) :
    (fderiv ℂ (inverse t M labels) (chart t M labels x)).comp
      (fderiv ℂ (chart t M labels) x) = ContinuousLinearMap.id ℂ (Coordinates t M) := by
  have hi := (analyticAt_inverse t M labels (gap_chart_ne_zero t M labels hx)).differentiableAt.hasFDerivAt
  have hc := ((ComplexForestFreeShapes.analyticOnNhd_chart t M (lab t labels) (lab_injective t labels))
    x hx).differentiableAt.hasFDerivAt
  have heq : inverse t M labels ∘ chart t M labels =ᶠ[nhds x] id := by
    filter_upwards [(ComplexForestFreeShapes.isOpen_chartDomain t M (lab t labels)).mem_nhds hx] with y hy
    exact inverse_chart t M labels hy
  have hd := (hi.comp x hc).fderiv
  rw [heq.fderiv_eq, fderiv_id] at hd
  exact hd.symm

theorem fderiv_chart_injective {x : Coordinates t M} (hx : x ∈ chartDomain t M labels) :
    Function.Injective (fderiv ℂ (chart t M labels) x) := by
  have hi : Function.LeftInverse (fderiv ℂ (inverse t M labels) (chart t M labels x))
      (fderiv ℂ (chart t M labels) x) := fun v ↦
    congrArg (fun L : Coordinates t M →L[ℂ] Coordinates t M ↦ L v) (fderiv_inverse_comp t M labels hx)
  exact hi.injective

theorem fderiv_chart_bijective (hroot : ¬ IsMax (⊥ : t)) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M labels) : Function.Bijective (fderiv ℂ (chart t M labels) x) := by
  have hdim : Module.finrank ℂ (Coordinates t M) = Module.finrank ℂ (Shape N) := by
    rw [ComplexForestFreeShapes.complex_dimension t M hroot, ← Fintype.card_congr labels,
      Fintype.card_fin]
    simp [Shape]
  have hi := fderiv_chart_injective t M labels hx
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

/-- The actual chart derivative, packaged as a continuous complex linear equivalence. -/
def differential (hroot : ¬ IsMax (⊥ : t)) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M labels) : Coordinates t M ≃L[ℂ] Shape N :=
  ContinuousLinearEquiv.ofBijective (fderiv ℂ (chart t M labels) x)
    (LinearMap.ker_eq_bot.mpr (fderiv_chart_bijective t M labels hroot hx).1)
    (LinearMap.range_eq_top.mpr (fderiv_chart_bijective t M labels hroot hx).2)

@[simp] theorem differential_coe (hroot : ¬ IsMax (⊥ : t)) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M labels) :
    (differential t M labels hroot hx : Coordinates t M →L[ℂ] Shape N) = fderiv ℂ (chart t M labels) x :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem hasStrictFDerivAt_chart (hroot : ¬ IsMax (⊥ : t)) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M labels) :
    HasStrictFDerivAt (chart t M labels) (differential t M labels hroot hx : Coordinates t M →L[ℂ] Shape N) x := by
  rw [differential_coe]
  exact (((ComplexForestFreeShapes.analyticOnNhd_chart t M (lab t labels) (lab_injective t labels))
    x hx).contDiffAt (n := 1)).hasStrictFDerivAt (by norm_num)

theorem isOpen_image_chart (hroot : ¬ IsMax (⊥ : t)) {U : Set (Coordinates t M)}
    (hU : IsOpen U) (hsub : U ⊆ chartDomain t M labels) : IsOpen (chart t M labels '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  have himage : chart t M labels '' U ∈ Filter.map (chart t M labels) (nhds x) :=
    Filter.image_mem_map (hU.mem_nhds hx)
  rw [(hasStrictFDerivAt_chart t M labels hroot (hsub hx)).map_nhds_eq_of_equiv] at himage
  exact himage

/-- Actual open chart with the explicit rational inverse, on the whole punctured
forest domain. Its open image follows from the proved invertible derivative. -/
def openPartialHomeomorph (hroot : ¬ IsMax (⊥ : t)) :
    OpenPartialHomeomorph (Coordinates t M) (Shape N) where
  toFun := chart t M labels
  invFun := inverse t M labels
  source := chartDomain t M labels
  target := chart t M labels '' chartDomain t M labels
  map_source' x hx := ⟨x, hx, rfl⟩
  map_target' y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [inverse_chart t M labels hx]
    exact hx
  left_inv' x hx := inverse_chart t M labels hx
  right_inv' y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [inverse_chart t M labels hx]
  open_source := ComplexForestFreeShapes.isOpen_chartDomain _ _ _
  open_target := isOpen_image_chart t M labels hroot (ComplexForestFreeShapes.isOpen_chartDomain _ _ _) Set.Subset.rfl
  continuousOn_toFun := (ComplexForestFreeShapes.analyticOnNhd_chart _ _ _ (lab_injective t labels)).continuousOn
  continuousOn_invFun := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (analyticAt_inverse t M labels (gap_chart_ne_zero t M labels hx)).continuousAt.continuousWithinAt

theorem isOpenMap_chart_restrict (hroot : ¬ IsMax (⊥ : t)) :
    IsOpenMap ((chartDomain t M labels).restrict (chart t M labels)) :=
  (openPartialHomeomorph t M labels hroot).isOpenEmbedding_restrict.isOpenMap

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestChartInverse
