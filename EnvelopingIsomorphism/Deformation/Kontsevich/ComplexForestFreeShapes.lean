import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestNormalizedCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDimensionCount
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeDimension

/-! Independent complex forest coordinates: each child shape has the literal
marks 0 and 1. The number of normal weights plus free child entries is q - 2. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestFreeShapes

open ForestChildShapeDecomposition ComplexForestNormalizedCharts ComplexForestInsertion
open InteriorFiberAngleSplit Topology
open scoped BigOperators Classical

variable (t : RootedTree) [Fintype t]

structure Marks where
  anchor : (v : Parent t) → Child t v.val
  reference : (v : Parent t) → Child t v.val
  distinct : ∀ v, anchor v ≠ reference v

variable (M : Marks t)

abbrev Free := (v : Parent t) × {u : Child t v.val // u ≠ M.anchor v ∧ u ≠ M.reference v}
abbrev Coordinates := (Normal t → ℂ) × (Free t M → ℂ)

def childShape (η : Free t M → ℂ) (v : Parent t) (u : Child t v.val) : ℂ :=
  if ha : u = M.anchor v then 0 else if hb : u = M.reference v then 1
  else η ⟨v, ⟨u, ha, hb⟩⟩

def shapeArray (η : Free t M → ℂ) : t → ℂ := restoreArray t (childShape t M η)

def parameters (x : Coordinates t M) : Parameters t := (x.1, shapeArray t M x.2)

omit [Fintype t] in
@[simp] theorem childShape_anchor (η : Free t M → ℂ) (v : Parent t) :
    childShape t M η v (M.anchor v) = 0 := by simp [childShape]

omit [Fintype t] in
@[simp] theorem childShape_reference (η : Free t M → ℂ) (v : Parent t) :
    childShape t M η v (M.reference v) = 1 := by simp [childShape, (M.distinct v).symm]

omit [Fintype t] in
theorem shapeArray_child (η : Free t M → ℂ) (v : Parent t) (u : Child t v.val) :
    shapeArray t M η u.val = childShape t M η v u :=
  congrFun (congrFun (decompose_restore t (childShape t M η)) v) u

@[fun_prop] theorem analyticAt_childShape (v : Parent t) (u : Child t v.val) (η : Free t M → ℂ) :
    AnalyticAt ℂ (fun ζ ↦ childShape t M ζ v u) η := by
  unfold childShape
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj _ : (Free t M → ℂ) →L[ℂ] ℂ).analyticAt η

@[fun_prop] theorem analyticAt_shapeArray (η : Free t M → ℂ) : AnalyticAt ℂ (shapeArray t M) η := by
  apply AnalyticAt.pi
  intro u
  unfold shapeArray restoreArray
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_childShape t M _ _ η

@[fun_prop] theorem analyticAt_parameters (x : Coordinates t M) : AnalyticAt ℂ (parameters t M) x :=
  analyticAt_fst.prod ((analyticAt_shapeArray t M x.2).comp analyticAt_snd)

theorem card_free : Fintype.card (Free t M) + 2 * Fintype.card (Parent t) + 1 = Fintype.card t := by
  have h := ForestDimensionCount.card_children t
  have hc : ∀ v : Parent t, Fintype.card (Child t v.val) =
      Fintype.card {u : Child t v.val // u ≠ M.anchor v ∧ u ≠ M.reference v} + 2 :=
    fun v ↦ by simpa only [← Nat.card_eq_fintype_card] using
      (ForestShapeDimension.freePair_card _ _ _ (M.distinct v)).symm
  simp only [hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [show Fintype.card (Free t M) = ∑ v : Parent t,
      Fintype.card {u : Child t v.val // u ≠ M.anchor v ∧ u ≠ M.reference v} from Fintype.card_sigma]
  omega

theorem card_normal (hroot : ¬ IsMax (⊥ : t)) : Fintype.card (Normal t) + 1 = Fintype.card (Parent t) := by
  have hp : Fintype.card (Parent t) = (internalNodes t).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v ↦ (mem_internalNodes t v).symm))
  rw [hp]
  rw [show Fintype.card (Normal t) = (normalNodes t).card from Fintype.card_coe _]
  exact Finset.card_erase_add_one ((mem_internalNodes t ⊥).mpr hroot)

theorem card_normal_add_free (hroot : ¬ IsMax (⊥ : t)) :
    Fintype.card (Normal t) + Fintype.card (Free t M) + 2 = Fintype.card {v : t // IsMax v} := by
  have hf := card_free t M
  have hn := card_normal t hroot
  have hp := Fintype.card_subtype_compl (IsMax : t → Prop)
  have hle : Fintype.card {v : t // IsMax v} ≤ Fintype.card t :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  change Fintype.card (Parent t) = Fintype.card t - Fintype.card {v : t // IsMax v} at hp
  omega

/-- The dimension follows from the tree Euler count and the two actual marks at
each parent. It is not a separate dimensional assumption on the chart. -/
theorem complex_dimension (hroot : ¬ IsMax (⊥ : t)) :
    Module.finrank ℂ (Coordinates t M) = Fintype.card {v : t // IsMax v} - 2 := by
  have h := card_normal_add_free t M hroot
  simp only [Coordinates, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

variable {N : ℕ} (lab : Point N → t)

def chart (x : Coordinates t M) : Shape N := normalizedShape t lab (parameters t M x)

def chartDomain : Set (Coordinates t M) := parameters t M ⁻¹' puncturedLocus t lab

theorem isOpen_chartDomain : IsOpen (chartDomain t M lab) :=
  (isOpen_puncturedLocus t lab).preimage (continuous_iff_continuousAt.mpr
    (fun x ↦ (analyticAt_parameters t M x).continuousAt))

theorem chart_mem_configuration (hinj : Function.Injective lab) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M lab) : chart t M lab x ∈ shapeConfiguration N :=
  normalizedShape_mem_configuration t lab hinj hx

theorem analyticOnNhd_chart (hinj : Function.Injective lab) :
    AnalyticOnNhd ℂ (chart t M lab) (chartDomain t M lab) := by
  intro x hx
  exact ((analyticOnNhd_normalizedShape t lab hinj) _ hx).comp (analyticAt_parameters t M x)

/-- Literal pair ratios in the independent normal and free-shape coordinates. -/
theorem chart_pairRatio_monomial (hinj : Function.Injective lab) {x : Coordinates t M}
    (hx : x ∈ chartDomain t M lab) (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    shapeDifference j k (chart t M lab x) / shapeDifference a b (chart t M lab x) =
      (∏ u : Normal t, x.1 u ^ ancestorExponent t (lab j ⊓ lab k) (lab a ⊓ lab b) u.val) *
        unitRatio t (lab j) (lab k) (lab a) (lab b)
          (ComplexForestNormalizedCharts.includeParameters t (parameters t M x)) :=
  normalized_pairRatio_monomial t lab hinj hx j k a b hjk hab

/-- The unit neighborhood survives the actual affine free-shape reconstruction. -/
theorem bounded_unit_neighborhood (hinj : Function.Injective lab) (hleaf : ∀ j, IsMax (lab j))
    (η : Free t M → ℂ) (hη : ChildShapesSeparated t (shapeArray t M η)) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0, η) ε ⊆
      parameters t M ⁻¹' unitLocus t lab := by
  have ho : IsOpen (parameters t M ⁻¹' unitLocus t lab) :=
    (isOpen_unitLocus t lab).preimage (continuous_iff_continuousAt.mpr
      (fun x ↦ (analyticAt_parameters t M x).continuousAt))
  exact Metric.isOpen_iff.mp ho (0, η) (corner_mem_unitLocus t lab hinj hleaf _ hη)

theorem analyticOnNhd_unit (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    AnalyticOnNhd ℂ (fun x : Coordinates t M ↦
      unitRatio t (lab j) (lab k) (lab a) (lab b)
        (ComplexForestNormalizedCharts.includeParameters t (parameters t M x)))
      (parameters t M ⁻¹' unitLocus t lab) := by
  intro x hx
  exact ((ComplexForestNormalizedCharts.analyticOnNhd_unit t lab j k a b hjk hab) _ hx).comp
    (analyticAt_parameters t M x)

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestFreeShapes
