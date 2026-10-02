import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestChartInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFrames
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDimension
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts

/-! Actual upper-subtree complex coordinates on the extracted planar fiber tree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexForestCharts

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterFrames ForestChildShapeDecomposition
open ComplexForestFreeShapes InteriorFiberAngleSplit
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

/-- This is the actual native subtree above the upper root child. -/
def upperTree : RootedTree := ((tree a x).subtree (upperNode a x hx)).coeTree

instance : Fintype (upperTree a x hx) := inferInstanceAs (Fintype (Set.Ici (upperNode a x hx)))

def leaf (j : Point N) : upperTree a x hx := ⟨canonicalLeaf a x (Sum.inl (Sum.inl j)), upper_le_leaf a x hx j⟩

theorem leaf_injective : Function.Injective (leaf a x hx) := by
  intro j k h
  have he := canonicalLeaf_injective a x (congrArg Subtype.val h)
  exact Sum.inl.inj (Sum.inl.inj he)

theorem isMax_iff (v : upperTree a x hx) : IsMax v ↔ IsMax v.val := by
  constructor
  · intro h w hvw
    exact h (b := (⟨w, v.property.trans hvw⟩ : upperTree a x hx)) hvw
  · intro h w hvw
    exact h hvw

theorem leaf_isMax (j : Point N) : IsMax (leaf a x hx j) :=
  (isMax_iff a x hx _).mpr (canonicalLeaf_isMax a x _)

def parent (v : Parent (upperTree a x hx)) : Parent (tree a x) :=
  ⟨v.val.val, fun h ↦ v.property ((isMax_iff a x hx v.val).mpr h)⟩

def liftChild (v : Parent (upperTree a x hx)) (u : Child (tree a x) (parent a x hx v).val) :
    Child (upperTree a x hx) v.val :=
  ⟨⟨u.val, v.val.property.trans u.property.le⟩, u.property.of_image (OrderEmbedding.subtype _)⟩

/-- The marks are the actual extracted complex frame marks at each upper parent. -/
def marks : Marks (upperTree a x hx) where
  anchor v := liftChild a x hx v ⟨(markedPair a x (parent a x hx v).val (parent a x hx v).property).1,
    (markedPair_spec a x _ _).1⟩
  reference v := liftChild a x hx v ⟨(markedPair a x (parent a x hx v).val (parent a x hx v).property).2,
    (markedPair_spec a x _ _).2.1⟩
  distinct _ h := (markedPair_spec a x _ _).2.2 (congrArg (fun u ↦ u.val.val) h)

theorem leaf_surjective : Function.Surjective (fun j ↦ (⟨leaf a x hx j, leaf_isMax a x hx j⟩ :
    {v : upperTree a x hx // IsMax v})) := by
  intro v
  let w : {u : tree a x // IsMax u} := ⟨v.val.val, (isMax_iff a x hx v.val).mp v.property⟩
  obtain ⟨j, hj⟩ := (ExtractedForestDimension.leafEquiv a x).surjective w
  have he : canonicalLeaf a x j = v.val.val := congrArg Subtype.val hj
  have hu : j ∈ PlanarClusterRoot.upperLabels := by
    have hv := v.val.property
    change upperNode a x hx ≤ v.val.val at hv
    rw [← he, le_canonicalLeaf_iff] at hv
    exact hv
  rcases j with (j | j) | j
  · refine ⟨j, ?_⟩
    apply Subtype.ext
    exact Subtype.ext he
  · exact Fin.elim0 j
  · simp at hu

def leafEquiv : Point N ≃ {v : upperTree a x hx // IsMax v} :=
  Equiv.ofBijective (fun j ↦ ⟨leaf a x hx j, leaf_isMax a x hx j⟩)
    ⟨fun _ _ h ↦ leaf_injective a x hx (congrArg Subtype.val h), leaf_surjective a x hx⟩

theorem root_nonleaf : ¬ IsMax (⊥ : upperTree a x hx) := by
  have hn := upper_nonleaf a x hx (if a = 0 then 1 else 0) (by split_ifs with h <;> simp_all)
  exact fun h ↦ hn ((isMax_iff a x hx _).mp h)

abbrev Coordinates := ComplexForestFreeShapes.Coordinates (upperTree a x hx) (marks a x hx)

/-- The actual number of independent complex coordinates is q−2=N. -/
theorem complex_dimension : Module.finrank ℂ (Coordinates a x hx) = N := by
  rw [ComplexForestFreeShapes.complex_dimension _ _ (root_nonleaf a x hx),
    ← Fintype.card_congr (leafEquiv a x hx), Fintype.card_fin]
  omega

def chart : Coordinates a x hx → Shape N :=
  ComplexForestFreeShapes.chart (upperTree a x hx) (marks a x hx) (leaf a x hx)

def chartDomain : Set (Coordinates a x hx) :=
  ComplexForestFreeShapes.chartDomain (upperTree a x hx) (marks a x hx) (leaf a x hx)

theorem chart_mem_configuration {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    chart a x hx z ∈ shapeConfiguration N :=
  ComplexForestFreeShapes.chart_mem_configuration _ _ _ (leaf_injective a x hx) hz

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (chart a x hx) (chartDomain a x hx) :=
  ComplexForestFreeShapes.analyticOnNhd_chart _ _ _ (leaf_injective a x hx)

def nativeChild (v : Parent (upperTree a x hx)) (u : Child (upperTree a x hx) v.val) : ℂ :=
  canonicalIncrement a x u.val.val

theorem child_covBy_native {v u : upperTree a x hx} (h : v ⋖ u) : v.val ⋖ u.val := by
  refine ⟨h.lt, ?_⟩
  intro w hvw hwu
  exact h.2 (c := (⟨w, v.property.trans hvw.le⟩ : upperTree a x hx)) hvw hwu

theorem nativeChild_injective (v : Parent (upperTree a x hx)) :
    Function.Injective (nativeChild a x hx v) := by
  intro u w h
  by_contra hne
  have hn : u.val.val ≠ w.val.val := fun he ↦ hne (Subtype.ext (Subtype.ext he))
  exact canonicalIncrement_siblings_distinct a x v.val.val u.val.val w.val.val
    (child_covBy_native a x hx u.property) (child_covBy_native a x hx w.property) hn h

def childDenominator (v : Parent (upperTree a x hx)) : ℂ :=
  nativeChild a x hx v ((marks a x hx).reference v) -
    nativeChild a x hx v ((marks a x hx).anchor v)

theorem childDenominator_ne_zero (v : Parent (upperTree a x hx)) : childDenominator a x hx v ≠ 0 :=
  sub_ne_zero.mpr ((nativeChild_injective a x hx v).ne ((marks a x hx).distinct v).symm)

/-- The actual extracted leading child shapes, divided by their actual marked difference. -/
def centerFree : Free (upperTree a x hx) (marks a x hx) → ℂ := fun p ↦
  (nativeChild a x hx p.1 p.2.val - nativeChild a x hx p.1 ((marks a x hx).anchor p.1)) /
    childDenominator a x hx p.1

theorem childShape_center (v : Parent (upperTree a x hx)) (u : Child (upperTree a x hx) v.val) :
    childShape (upperTree a x hx) (marks a x hx) (centerFree a x hx) v u =
      (nativeChild a x hx v u - nativeChild a x hx v ((marks a x hx).anchor v)) /
        childDenominator a x hx v := by
  unfold childShape
  split_ifs with ha hb
  · subst u; simp
  · subst u
    exact (div_self (childDenominator_ne_zero a x hx v)).symm
  · rfl

theorem center_childShape_injective (v : Parent (upperTree a x hx)) :
    Function.Injective (childShape (upperTree a x hx) (marks a x hx) (centerFree a x hx) v) := by
  intro u w h
  rw [childShape_center, childShape_center] at h
  exact nativeChild_injective a x hx v
    (sub_left_inj.mp ((div_left_inj' (childDenominator_ne_zero a x hx v)).mp h))

/-- Separation at the actual extracted corner is proved, not supplied as chart data. -/
theorem center_shapes_separated : ComplexForestInsertion.ChildShapesSeparated (upperTree a x hx)
    (shapeArray (upperTree a x hx) (marks a x hx) (centerFree a x hx)) := by
  intro v d e hd he hde h
  let p : Parent (upperTree a x hx) := ⟨v, not_isMax_of_lt hd.lt⟩
  have hchild (u : upperTree a x hx) (hu : v ⋖ u) :
      shapeArray (upperTree a x hx) (marks a x hx) (centerFree a x hx) u =
        childShape (upperTree a x hx) (marks a x hx) (centerFree a x hx) p ⟨u, hu⟩ :=
    shapeArray_child _ _ _ p ⟨u, hu⟩
  rw [hchild d hd, hchild e he] at h
  exact hde (congrArg Subtype.val (center_childShape_injective a x hx p h))

/-- One actual bounded complex neighborhood controls all edge/reference units. -/
theorem bounded_corner_neighborhood : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0, centerFree a x hx) ε ⊆
    parameters (upperTree a x hx) (marks a x hx) ⁻¹'
      ComplexForestNormalizedCharts.unitLocus (upperTree a x hx) (leaf a x hx) :=
  ComplexForestFreeShapes.bounded_unit_neighborhood _ _ _ (leaf_injective a x hx)
    (leaf_isMax a x hx) _ (center_shapes_separated a x hx)

abbrev Normal := ComplexForestNormalizedCharts.Normal (upperTree a x hx)

def exponent (j k b c : Point N) (v : Normal a x hx) : ℤ :=
  ComplexForestInsertion.ancestorExponent (upperTree a x hx)
    (leaf a x hx j ⊓ leaf a x hx k) (leaf a x hx b ⊓ leaf a x hx c) v.val

def unit (j k b c : Point N) (z : Coordinates a x hx) : ℂ :=
  ComplexForestInsertion.unitRatio (upperTree a x hx)
    (leaf a x hx j) (leaf a x hx k) (leaf a x hx b) (leaf a x hx c)
    (ComplexForestNormalizedCharts.includeParameters (upperTree a x hx)
      (parameters (upperTree a x hx) (marks a x hx) z))

/-- All edge and reference choices share the same actual bounded normal-form chart. -/
theorem bounded_normalForm : ∃ ε : ℝ, 0 < ε ∧
    ∀ j k b c : Point N, j ≠ k → b ≠ c →
      AnalyticOnNhd ℂ (unit a x hx j k b c) (Metric.ball (0, centerFree a x hx) ε) ∧
      (∀ z : Coordinates a x hx, z ∈ Metric.ball (0, centerFree a x hx) ε → unit a x hx j k b c z ≠ 0) ∧
      ∀ z : Coordinates a x hx, z ∈ Metric.ball (0, centerFree a x hx) ε → (∀ v : Normal a x hx, z.1 v ≠ 0) →
        z ∈ chartDomain a x hx ∧
        shapeDifference j k (chart a x hx z) / shapeDifference b c (chart a x hx z) =
          (∏ v : Normal a x hx, z.1 v ^ exponent a x hx j k b c v) * unit a x hx j k b c z := by
  obtain ⟨ε, hε, hball⟩ := bounded_corner_neighborhood a x hx
  refine ⟨ε, hε, fun j k b c hjk hbc ↦ ⟨?_, ?_, ?_⟩⟩
  · exact (ComplexForestFreeShapes.analyticOnNhd_unit _ _ _ j k b c hjk hbc).mono hball
  · intro z hz
    exact ComplexForestNormalizedCharts.unit_ne_zero _ _ (hball hz) j k b c hjk hbc
  · intro z hz hnormal
    have hdomain : z ∈ chartDomain a x hx := ⟨hball hz, hnormal⟩
    exact ⟨hdomain, ComplexForestFreeShapes.chart_pairRatio_monomial _ _ _
      (leaf_injective a x hx) hdomain j k b c hjk hbc⟩

/-- Actual open angular sectors for all independent normal phases. -/
def angularSector (u : Normal a x hx → Circle) :
    OpenPartialHomeomorph (Normal a x hx → ℝ) (Normal a x hx → Circle) :=
  OpenPartialHomeomorph.pi (fun v ↦ ForestOrthantCharts.angleChart (u v))

theorem angularSector_source (u : Normal a x hx → Circle) :
    (angularSector a x hx u).source = Set.univ.pi (fun _ ↦ Set.Ioo (-Real.pi) Real.pi) := by
  change Set.univ.pi (fun v ↦ (ForestOrthantCharts.angleChart (u v)).source) = _
  simp_rw [ForestOrthantCharts.angleChart_source]

theorem center_mem_angularSector (u : Normal a x hx → Circle) : u ∈ (angularSector a x hx u).target := by
  change ∀ v ∈ (Set.univ : Set (Normal a x hx)), u v ∈ (ForestOrthantCharts.angleChart (u v)).target
  intro v hv
  exact ForestOrthantCharts.center_mem_angleChart_target _

/-- Compactness of the actual phase torus gives a finite sector cover.
Only sector domains are used; no Cartesian smoothness of angular cutoffs is asserted. -/
theorem finite_angular_sectors : ∃ centers : Finset (Normal a x hx → Circle),
    ∀ u : Normal a x hx → Circle, ∃ c ∈ centers, u ∈ (angularSector a x hx c).target := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun c : Normal a x hx → Circle ↦ (angularSector a x hx c).target)
    (fun c ↦ (angularSector a x hx c).open_target) (by
      intro u hu
      exact Set.mem_iUnion.mpr ⟨u, center_mem_angularSector a x hx u⟩)
  refine ⟨s, fun u ↦ ?_⟩
  simpa only [Set.mem_iUnion, exists_prop] using hs (Set.mem_univ u)

theorem isOpen_chartDomain : IsOpen (chartDomain a x hx) :=
  ComplexForestFreeShapes.isOpen_chartDomain _ _ _

def inverse : Shape N → Coordinates a x hx :=
  ComplexForestChartInverse.inverse (upperTree a x hx) (marks a x hx) (leafEquiv a x hx)

theorem inverse_chart {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    inverse a x hx (chart a x hx z) = z :=
  ComplexForestChartInverse.inverse_chart _ _ (leafEquiv a x hx) hz

theorem fderiv_inverse_comp {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    (fderiv ℂ (inverse a x hx) (chart a x hx z)).comp (fderiv ℂ (chart a x hx) z) =
      ContinuousLinearMap.id ℂ (Coordinates a x hx) :=
  ComplexForestChartInverse.fderiv_inverse_comp _ _ (leafEquiv a x hx) hz

theorem fderiv_chart_bijective {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    Function.Bijective (fderiv ℂ (chart a x hx) z) :=
  ComplexForestChartInverse.fderiv_chart_bijective _ _ (leafEquiv a x hx) (root_nonleaf a x hx) hz

def differential {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    Coordinates a x hx ≃L[ℂ] Shape N :=
  ComplexForestChartInverse.differential _ _ (leafEquiv a x hx) (root_nonleaf a x hx) hz

theorem hasStrictFDerivAt_chart {z : Coordinates a x hx} (hz : z ∈ chartDomain a x hx) :
    HasStrictFDerivAt (chart a x hx) (differential a x hx hz : Coordinates a x hx →L[ℂ] Shape N) z :=
  ComplexForestChartInverse.hasStrictFDerivAt_chart _ _ (leafEquiv a x hx) (root_nonleaf a x hx) hz

def openPartialHomeomorph : OpenPartialHomeomorph (Coordinates a x hx) (Shape N) :=
  ComplexForestChartInverse.openPartialHomeomorph _ _ (leafEquiv a x hx) (root_nonleaf a x hx)

@[simp] theorem openPartialHomeomorph_source : (openPartialHomeomorph a x hx).source = chartDomain a x hx := rfl
@[simp] theorem openPartialHomeomorph_target : (openPartialHomeomorph a x hx).target =
    chart a x hx '' chartDomain a x hx := rfl
@[simp] theorem openPartialHomeomorph_apply (z : Coordinates a x hx) :
    openPartialHomeomorph a x hx z = chart a x hx z := rfl
@[simp] theorem openPartialHomeomorph_symm_apply (η : Shape N) :
    (openPartialHomeomorph a x hx).symm η = inverse a x hx η := rfl

theorem isOpenMap_chart_restrict : IsOpenMap ((chartDomain a x hx).restrict (chart a x hx)) :=
  ComplexForestChartInverse.isOpenMap_chart_restrict _ _ (leafEquiv a x hx) (root_nonleaf a x hx)

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexForestCharts
