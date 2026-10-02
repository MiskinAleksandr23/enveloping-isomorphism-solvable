import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexClusterScaleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularRadialDeterminant
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact rotation extraction for an interior planar cluster with two marked points.
The frame is angular-first, followed by the native interleaved 1,I shape basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFiberAngleSplit

open Set MeasureTheory ContinuousAlternatingMap
open scoped Topology BigOperators

abbrev Shape (N : ℕ) := Fin N → ℂ
abbrev Point (N : ℕ) := Fin (N + 2)
abbrev Parameters (N : ℕ) := ℝ × Shape N
abbrev Dim (N : ℕ) := AngularRadial.realDimension N

def normalizedPoint {N : ℕ} (η : Shape N) : Point N → ℂ := Matrix.vecCons 0 (Matrix.vecCons 1 η)

@[simp] theorem normalizedPoint_anchor {N : ℕ} (η : Shape N) : normalizedPoint η 0 = 0 := rfl
@[simp] theorem normalizedPoint_reference {N : ℕ} (η : Shape N) : normalizedPoint η 1 = 1 := rfl
@[simp] theorem normalizedPoint_free {N : ℕ} (η : Shape N) (j : Fin N) :
    normalizedPoint η j.succ.succ = η j := rfl

def pointLinear {N : ℕ} : Point N → Shape N →L[ℝ] ℂ :=
  Matrix.vecCons 0 (Matrix.vecCons 0 (fun j ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N ↦ ℂ) j)))

theorem hasFDerivAt_normalizedPoint {N : ℕ} (j : Point N) (η : Shape N) :
    HasFDerivAt (fun ζ ↦ normalizedPoint ζ j) (pointLinear j) η := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · exact hasFDerivAt_const (0 : ℂ) η
  · exact hasFDerivAt_const (1 : ℂ) η
  · exact (pointLinear l.succ.succ).hasFDerivAt

theorem contDiff_normalizedPoint {N : ℕ} (j : Point N) :
    ContDiff ℝ ⊤ (fun η : Shape N ↦ normalizedPoint η j) := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · exact contDiff_const
  · exact contDiff_const
  · exact (pointLinear l.succ.succ).contDiff

def toClusterUnitShape {N : ℕ} (η : Shape N) :
    ComplexClusterScaleCoordinates.UnitShape (0 : Point N) 1 Finset.univ :=
  fun j ↦ normalizedPoint η j.val

theorem normalizedPoint_eq_clusterUnitShape {N : ℕ} (η : Shape N) (j : Point N) :
    normalizedPoint η j = ComplexClusterScaleCoordinates.unitShape (toClusterUnitShape η) j := by
  unfold ComplexClusterScaleCoordinates.unitShape
  split_ifs with h0 h1 hj
  · subst j
    rfl
  · subst j
    rfl
  · rfl
  · exact False.elim (hj (Finset.mem_univ j))

def rotatedPoint {N : ℕ} (x : Parameters N) (j : Point N) : ℂ := circleParameter x.1 * normalizedPoint x.2 j

theorem rotatedPoint_eq_clusterInsertion {N : ℕ} (x : Parameters N) (j : Point N) :
    rotatedPoint x j = ComplexClusterScaleCoordinates.insertion
      (0, toClusterUnitShape x.2, circleParameter x.1) j := by
  rw [ComplexClusterScaleCoordinates.insertion, zero_add, ← normalizedPoint_eq_clusterUnitShape]
  rfl

def shapeDifference {N : ℕ} (s t : Point N) (η : Shape N) : ℂ := normalizedPoint η t - normalizedPoint η s
def shapeDerivative {N : ℕ} (s t : Point N) : Shape N →L[ℝ] ℂ := pointLinear t - pointLinear s

theorem hasFDerivAt_shapeDifference {N : ℕ} (s t : Point N) (η : Shape N) :
    HasFDerivAt (shapeDifference s t) (shapeDerivative s t) η :=
  (hasFDerivAt_normalizedPoint t η).sub (hasFDerivAt_normalizedPoint s η)

@[simp] theorem fderiv_shapeDifference {N : ℕ} (s t : Point N) (η : Shape N) :
    fderiv ℝ (shapeDifference s t) η = shapeDerivative s t := (hasFDerivAt_shapeDifference s t η).fderiv

def rotatedDifference {N : ℕ} (s t : Point N) (x : Parameters N) : ℂ := rotatedPoint x t - rotatedPoint x s

theorem rotatedDifference_factor {N : ℕ} (s t : Point N) (x : Parameters N) :
    rotatedDifference s t x = circleParameter x.1 * shapeDifference s t x.2 := by
  simp only [rotatedDifference, rotatedPoint, shapeDifference, mul_sub]

def rotatedDerivative {N : ℕ} (s t : Point N) (x : Parameters N) : Parameters N →L[ℝ] ℂ :=
  shapeDifference s t x.2 • ((circleParameterTangent x.1).comp (ContinuousLinearMap.fst ℝ ℝ (Shape N))) +
    circleParameter x.1 • ((shapeDerivative s t).comp (ContinuousLinearMap.snd ℝ ℝ (Shape N)))

theorem hasFDerivAt_rotatedDifference {N : ℕ} (s t : Point N) (x : Parameters N) :
    HasFDerivAt (rotatedDifference s t) (rotatedDerivative s t x) x := by
  have h := ((hasFDerivAt_circleParameter x.1).comp x (ContinuousLinearMap.fst ℝ ℝ (Shape N)).hasFDerivAt).mul
    ((hasFDerivAt_shapeDifference s t x.2).comp x (ContinuousLinearMap.snd ℝ ℝ (Shape N)).hasFDerivAt)
  have heq : rotatedDifference s t = (circleParameter ∘ Prod.fst) * (shapeDifference s t ∘ Prod.snd) :=
    funext (rotatedDifference_factor s t)
  rw [heq]
  convert h using 1 <;> try rfl
  exact add_comm _ _

theorem rotatedDerivative_apply {N : ℕ} (s t : Point N) (x v : Parameters N) :
    rotatedDerivative s t x v = shapeDifference s t x.2 * (circleParameter x.1 * Complex.I * (v.1 : ℂ)) +
      circleParameter x.1 * shapeDerivative s t v.2 := rfl

@[simp] theorem fderiv_rotatedDifference {N : ℕ} (s t : Point N) (x : Parameters N) :
    fderiv ℝ (rotatedDifference s t) x = rotatedDerivative s t x :=
  (hasFDerivAt_rotatedDifference s t x).fderiv

def shapeEdgeForm {N : ℕ} (s t : Point N) (η : Shape N) : Shape N [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (shapeDifference s t η)).compContinuousLinearMap (fderiv ℝ (shapeDifference s t) η)

def rotatedEdgeForm {N : ℕ} (s t : Point N) (x : Parameters N) : Parameters N [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (rotatedDifference s t x)).compContinuousLinearMap (fderiv ℝ (rotatedDifference s t) x)

def dtheta (N : ℕ) : Parameters N [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (ContinuousLinearMap.fst ℝ ℝ (Shape N))

/-- Actual darg product splitting at every nonzero edge difference. -/
theorem rotatedEdgeForm_split {N : ℕ} (s t : Point N) (x : Parameters N)
    (hδ : shapeDifference s t x.2 ≠ 0) :
    rotatedEdgeForm s t x = dtheta N +
      (shapeEdgeForm s t x.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ ℝ (Shape N)) := by
  ext v
  simp only [rotatedEdgeForm, shapeEdgeForm, fderiv_rotatedDifference, fderiv_shapeDifference,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.add_apply, angularForm_apply]
  change (rotatedDerivative s t x (v 0) / rotatedDifference s t x).im =
    (v 0).1 + (shapeDerivative s t (v 0).2 / shapeDifference s t x.2).im
  rw [rotatedDifference_factor]
  have hratio : rotatedDerivative s t x (v 0) / (circleParameter x.1 * shapeDifference s t x.2) =
      Complex.I * ((v 0).1 : ℂ) + shapeDerivative s t (v 0).2 / shapeDifference s t x.2 := by
    rw [rotatedDerivative_apply]
    field_simp [circleParameter_ne_zero x.1, hδ]
  rw [hratio]
  simp

/-- The reference edge is literally the positive-angle form dθ. -/
theorem referenceEdgeForm {N : ℕ} (x : Parameters N) : rotatedEdgeForm (0 : Point N) 1 x = dtheta N := by
  rw [rotatedEdgeForm_split _ _ x (by simp [shapeDifference])]
  have hz : shapeEdgeForm (0 : Point N) 1 x.2 = 0 := by
    ext v
    simp [shapeEdgeForm, shapeDerivative, pointLinear]
  rw [hz]
  ext v
  change dtheta N v + 0 = dtheta N v
  exact add_zero _

/-- Horizontal tangent evaluation is rotation invariant even at totalized collisions. -/
theorem rotatedEdgeForm_horizontal {N : ℕ} (s t : Point N) (x : Parameters N) (v : Shape N) :
    rotatedEdgeForm s t x (fun _ : Fin 1 ↦ (0, v)) = shapeEdgeForm s t x.2 (fun _ : Fin 1 ↦ v) := by
  simp only [rotatedEdgeForm, shapeEdgeForm, fderiv_rotatedDifference, fderiv_shapeDifference,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  change (rotatedDerivative s t x (0, v) / rotatedDifference s t x).im =
    (shapeDerivative s t v / shapeDifference s t x.2).im
  have hd : rotatedDerivative s t x (0, v) = circleParameter x.1 * shapeDerivative s t v := by
    simp [rotatedDerivative_apply]
  rw [hd, rotatedDifference_factor, mul_div_mul_left _ _ (circleParameter_ne_zero x.1)]

def shapeConfiguration (N : ℕ) : Set (Shape N) := {η | Function.Injective (normalizedPoint η)}
def fiberConfiguration (N : ℕ) : Set (Parameters N) := {x | Function.Injective (rotatedPoint x)}

theorem mem_shapeConfiguration_iff {N : ℕ} (η : Shape N) :
    η ∈ shapeConfiguration N ↔ (∀ j, η j ≠ 0) ∧ (∀ j, η j ≠ 1) ∧ Function.Injective η := by
  change Function.Injective (Fin.cons (0 : ℂ) (Fin.cons (1 : ℂ) η)) ↔ _
  simp only [Fin.cons_injective_iff, Fin.range_cons, mem_insert_iff, not_or, zero_ne_one,
    not_false_eq_true, true_and, Set.mem_range, not_exists]

theorem isOpen_shapeConfiguration (N : ℕ) : IsOpen (shapeConfiguration N) := by
  have hs : shapeConfiguration N = ⋂ s : Point N, ⋂ t : Point N,
      {η : Shape N | s = t ∨ normalizedPoint η s ≠ normalizedPoint η t} := by
    ext η
    simp only [shapeConfiguration, mem_setOf_eq, mem_iInter]
    constructor
    · intro h s t
      by_cases hst : s = t
      · exact Or.inl hst
      · exact Or.inr (fun heq ↦ hst (h heq))
    · intro h s t heq
      exact (h s t).resolve_right (fun hn ↦ hn heq)
  rw [hs]
  apply isOpen_iInter_of_finite
  intro s
  apply isOpen_iInter_of_finite
  intro t
  by_cases hst : s = t
  · simp [hst]
  · simp only [hst, false_or]
    exact isOpen_ne_fun (contDiff_normalizedPoint s).continuous (contDiff_normalizedPoint t).continuous

theorem shapeDifference_ne_zero {N : ℕ} {η : Shape N} (hη : η ∈ shapeConfiguration N)
    {s t : Point N} (hst : s ≠ t) : shapeDifference s t η ≠ 0 := by
  exact sub_ne_zero.mpr (fun h ↦ hst (hη h).symm)

theorem fiberConfiguration_eq (N : ℕ) : fiberConfiguration N = univ ×ˢ shapeConfiguration N := by
  ext x
  change Function.Injective (rotatedPoint x) ↔ True ∧ Function.Injective (normalizedPoint x.2)
  simp only [true_and]
  constructor
  · intro h s t heq
    exact h (congrArg (fun z : ℂ ↦ circleParameter x.1 * z) heq)
  · intro h s t heq
    apply h
    exact mul_left_cancel₀ (circleParameter_ne_zero x.1) heq

theorem rotatedEdgeForm_split_on_configuration {N : ℕ} (x : Parameters N)
    (hx : x.2 ∈ shapeConfiguration N) (s t : Point N) (hst : s ≠ t) :
    rotatedEdgeForm s t x = dtheta N +
      (shapeEdgeForm s t x.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ ℝ (Shape N)) :=
  rotatedEdgeForm_split s t x (shapeDifference_ne_zero hx hst)

abbrev Edges (N : ℕ) := Fin (Dim N) → Point N × Point N

def fiberFrame (N : ℕ) : Fin (Dim N + 1) → Parameters N :=
  Matrix.vecCons (1, 0) (fun j ↦ (0, AngularRadial.realBasis N j))

def formLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm ω

@[simp] theorem formLinear_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ω : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) : formLinear ω v = ω (fun _ : Fin 1 ↦ v) := rfl

def orderedEdgeForms {N : ℕ} (e : Edges N) (x : Parameters N) :
    Fin (Dim N + 1) → Parameters N [⋀^Fin 1]→L[ℝ] ℝ :=
  Matrix.vecCons (rotatedEdgeForm (0 : Point N) 1 x) (fun j ↦ rotatedEdgeForm (e j).1 (e j).2 x)

/-- The actual ordered top alternating product begins with the chosen edge 0→1. -/
def fiberTopForm {N : ℕ} (e : Edges N) (x : Parameters N) :
    Parameters N [⋀^Fin (Dim N + 1)]→L[ℝ] ℝ :=
  (coordinateVolume (Dim N + 1)).compContinuousLinearMap
    (ContinuousLinearMap.pi (fun j ↦ formLinear (orderedEdgeForms e x j)))

def shapeTopForm {N : ℕ} (e : Edges N) (η : Shape N) : Shape N [⋀^Fin (Dim N)]→L[ℝ] ℝ :=
  (coordinateVolume (Dim N)).compContinuousLinearMap
    (ContinuousLinearMap.pi (fun j ↦ formLinear (shapeEdgeForm (e j).1 (e j).2 η)))

def fiberDensity {N : ℕ} (e : Edges N) (x : Parameters N) : ℝ := fiberTopForm e x (fiberFrame N)
def shapeDensity {N : ℕ} (e : Edges N) (η : Shape N) : ℝ := shapeTopForm e η (AngularRadial.realBasis N)

def fiberMatrix {N : ℕ} (e : Edges N) (x : Parameters N) : Matrix (Fin (Dim N + 1)) (Fin (Dim N + 1)) ℝ :=
  fun r c ↦ orderedEdgeForms e x c (fun _ : Fin 1 ↦ fiberFrame N r)

theorem fiberDensity_eq_det {N : ℕ} (e : Edges N) (x : Parameters N) : fiberDensity e x = Matrix.det (fiberMatrix e x) := rfl

theorem shapeDensity_eq_det {N : ℕ} (e : Edges N) (η : Shape N) :
    shapeDensity e η = Matrix.det (fun r c : Fin (Dim N) ↦
      shapeEdgeForm (e c).1 (e c).2 η (fun _ : Fin 1 ↦ AngularRadial.realBasis N r)) := rfl

@[simp] theorem fiberMatrix_zero_zero {N : ℕ} (e : Edges N) (x : Parameters N) : fiberMatrix e x 0 0 = 1 := by
  change rotatedEdgeForm (0 : Point N) 1 x (fun _ : Fin 1 ↦ (1, 0)) = 1
  rw [referenceEdgeForm]
  rfl

@[simp] theorem fiberMatrix_succ_zero {N : ℕ} (e : Edges N) (x : Parameters N) (j : Fin (Dim N)) :
    fiberMatrix e x j.succ 0 = 0 := by
  change rotatedEdgeForm (0 : Point N) 1 x (fun _ : Fin 1 ↦ (0, AngularRadial.realBasis N j)) = 0
  rw [referenceEdgeForm]
  rfl

/-- Exact top determinant factorization in the θ-first/interleaved-1,I frame.
Expansion along the chosen edge has sign +1. Horizontal invariance makes the
identity valid even at totalized collision values, before restricting the domain. -/
theorem fiberDensity_eq_shapeDensity {N : ℕ} (e : Edges N) (x : Parameters N) :
    fiberDensity e x = shapeDensity e x.2 := by
  rw [fiberDensity_eq_det, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [fiberMatrix_zero_zero, fiberMatrix_succ_zero, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [shapeDensity_eq_det]
  congr 1
  funext r c
  change rotatedEdgeForm (e c).1 (e c).2 x
    (fun _ : Fin 1 ↦ (0, AngularRadial.realBasis N r)) = _
  exact rotatedEdgeForm_horizontal (e c).1 (e c).2 x (AngularRadial.realBasis N r)

def integrationRegion (N : ℕ) : Set (Parameters N) :=
  Icc (0 : ℝ) (2 * Real.pi) ×ˢ shapeConfiguration N

theorem integrationRegion_eq_actual_configuration (N : ℕ) :
    integrationRegion N = {x : Parameters N | x.1 ∈ Icc (0 : ℝ) (2 * Real.pi) ∧
      Function.Injective (rotatedPoint x)} := by
  have h := fiberConfiguration_eq N
  ext x
  have hx : Function.Injective (rotatedPoint x) ↔ x.2 ∈ shapeConfiguration N := by
    change x ∈ fiberConfiguration N ↔ _
    rw [h]
    simp
  simp only [integrationRegion, mem_prod, mem_setOf_eq, hx]

theorem measurableSet_integrationRegion (N : ℕ) : MeasurableSet (integrationRegion N) :=
  measurableSet_Icc.prod (isOpen_shapeConfiguration N).measurableSet

/-- True product integration over the actual planar configuration complement.
The coefficient equality holds globally; the L¹ equivalence below identifies
precisely when both sides are genuine absolutely integrable densities. -/
theorem integral_fiberDensity_eq {N : ℕ} (e : Edges N) :
    (∫ x in integrationRegion N, fiberDensity e x) =
      (2 * Real.pi) * ∫ η in shapeConfiguration N, shapeDensity e η := by
  simp_rw [fiberDensity_eq_shapeDensity]
  rw [integrationRegion, Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Shape N)))
    (fun _ : ℝ ↦ (1 : ℝ)) (shapeDensity e) (Icc (0 : ℝ) (2 * Real.pi)) (shapeConfiguration N)
  simpa only [one_mul, setIntegral_const, Real.volume_real_Icc, sub_zero,
    max_eq_left (show (0 : ℝ) ≤ 2 * Real.pi by positivity), smul_eq_mul, mul_one] using h

theorem integral_norm_fiberDensity_eq {N : ℕ} (e : Edges N) :
    (∫ x in integrationRegion N, ‖fiberDensity e x‖) =
      (2 * Real.pi) * ∫ η in shapeConfiguration N, ‖shapeDensity e η‖ := by
  simp_rw [fiberDensity_eq_shapeDensity]
  rw [integrationRegion, Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Shape N)))
    (fun _ : ℝ ↦ (1 : ℝ)) (fun η ↦ ‖shapeDensity e η‖) (Icc (0 : ℝ) (2 * Real.pi)) (shapeConfiguration N)
  simpa only [one_mul, setIntegral_const, Real.volume_real_Icc, sub_zero,
    max_eq_left (show (0 : ℝ) ≤ 2 * Real.pi by positivity), smul_eq_mul, mul_one] using h

/-- Genuine absolute-integrability equivalence, using the positive finite angular measure. -/
theorem integrableOn_fiberDensity_iff {N : ℕ} (e : Edges N) :
    IntegrableOn (fiberDensity e) (integrationRegion N) ↔
      IntegrableOn (shapeDensity e) (shapeConfiguration N) := by
  simp_rw [show fiberDensity e = fun x ↦ shapeDensity e x.2 from funext (fiberDensity_eq_shapeDensity e)]
  rw [integrationRegion, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))
  haveI : IsFiniteMeasure μ := ⟨by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hμ : μ ≠ 0 := by
    intro h
    have hh := congrArg (fun ν : Measure ℝ ↦ ν univ) h
    simp only [μ, Measure.restrict_apply_univ] at hh
    change volume (Icc (0 : ℝ) (2 * Real.pi)) = 0 at hh
    rw [Real.volume_Icc, sub_zero] at hh
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (show (0 : ℝ) < 2 * Real.pi by positivity))) hh
  exact Integrable.comp_snd_iff hμ

/-- Rotation extraction with actual L¹ supplied on the normalized shape configuration. -/
theorem rotation_extraction {N : ℕ} (e : Edges N)
    (hL1 : IntegrableOn (shapeDensity e) (shapeConfiguration N)) :
    IntegrableOn (fiberDensity e) (integrationRegion N) ∧
      (∫ x in integrationRegion N, fiberDensity e x) =
        (2 * Real.pi) * ∫ η in shapeConfiguration N, shapeDensity e η :=
  ⟨(integrableOn_fiberDensity_iff e).mpr hL1, integral_fiberDensity_eq e⟩

theorem integral_fiberDensity_zero_iff {N : ℕ} (e : Edges N) :
    (∫ x in integrationRegion N, fiberDensity e x) = 0 ↔
      (∫ η in shapeConfiguration N, shapeDensity e η) = 0 := by
  rw [integral_fiberDensity_eq, mul_eq_zero]
  simp [Real.pi_ne_zero]

@[simp] theorem shapeDensity_zero_dim (e : Edges 0) (η : Shape 0) : shapeDensity e η = 1 := by
  rw [shapeDensity_eq_det]
  haveI : IsEmpty (Fin (Dim 0)) := by change IsEmpty (Fin 0); infer_instance
  exact Matrix.det_isEmpty

@[simp] theorem shapeConfiguration_zero_dim : shapeConfiguration 0 = univ := by
  ext η
  simp [mem_shapeConfiguration_iff, Function.Injective]

/-- The two-point fiber is the circle itself, with integral +2π rather than a vanishing claim. -/
theorem integral_two_point_fiber (e : Edges 0) :
    (∫ x in integrationRegion 0, fiberDensity e x) = 2 * Real.pi := by
  rw [integral_fiberDensity_eq]
  simp [Measure.real_def, volume_pi]

/-- These are actual translation/positive-scale-normalized planar positions,
with the residual circle direction retained. -/
theorem rotatedPoint_normalization {N : ℕ} (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    Function.Injective (rotatedPoint x) ∧ rotatedPoint x 0 = 0 ∧ ‖rotatedPoint x 1‖ = 1 := by
  have hi : x ∈ fiberConfiguration N := by
    rw [fiberConfiguration_eq]
    exact ⟨trivial, hx⟩
  refine ⟨hi, ?_, ?_⟩
  · simp [rotatedPoint]
  · simp [rotatedPoint, circleParameter_eq]

def relabeledPoint {N : ℕ} {Label : Type*} (σ : Point N ≃ Label) (x : Parameters N) (j : Label) : ℂ :=
  rotatedPoint x (σ.symm j)

def relabeledDifference {N : ℕ} {Label : Type*} (σ : Point N ≃ Label) (s t : Label) (x : Parameters N) : ℂ :=
  relabeledPoint σ x t - relabeledPoint σ x s

def relabeledEdgeForm {N : ℕ} {Label : Type*} (σ : Point N ≃ Label) (s t : Label) (x : Parameters N) :
    Parameters N [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (relabeledDifference σ s t x)).compContinuousLinearMap
    (fderiv ℝ (relabeledDifference σ s t) x)

theorem relabeledEdgeForm_eq {N : ℕ} {Label : Type*} (σ : Point N ≃ Label)
    (s t : Label) (x : Parameters N) :
    relabeledEdgeForm σ s t x = rotatedEdgeForm (σ.symm s) (σ.symm t) x := rfl

/-- Any chosen marked nonloop edge a→b is obtained by labeling 0 by a and 1 by b. -/
theorem relabeled_referenceEdgeForm {N : ℕ} {Label : Type*} (σ : Point N ≃ Label)
    (a b : Label) (ha : σ 0 = a) (hb : σ 1 = b) (x : Parameters N) :
    relabeledEdgeForm σ a b x = dtheta N := by
  rw [← ha, ← hb, relabeledEdgeForm_eq, σ.symm_apply_apply, σ.symm_apply_apply, referenceEdgeForm]

theorem relabeledEdgeForm_split {N : ℕ} {Label : Type*} (σ : Point N ≃ Label)
    (s t : Label) (hst : s ≠ t) (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    relabeledEdgeForm σ s t x = dtheta N +
      (shapeEdgeForm (σ.symm s) (σ.symm t) x.2).compContinuousLinearMap
        (ContinuousLinearMap.snd ℝ ℝ (Shape N)) := by
  rw [relabeledEdgeForm_eq]
  exact rotatedEdgeForm_split_on_configuration x hx _ _ (σ.symm.injective.ne hst)

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFiberAngleSplit
