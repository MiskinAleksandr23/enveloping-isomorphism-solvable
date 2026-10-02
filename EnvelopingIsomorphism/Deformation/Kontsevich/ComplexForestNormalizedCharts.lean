import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarNormalizedCoordinates
import Mathlib.Topology.MetricSpace.Bounded

/-! Root-free complex forest insertion and its literal normalized configuration map.
The normal exponents and holomorphic units are computed from insertion polynomials.
No normal-form assertion is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestNormalizedCharts

open AncestorScaleRatios ForestInsertionDifference ComplexForestInsertion
open InteriorFiberAngleSplit Set Topology
open scoped BigOperators Classical

variable (t : RootedTree) [Fintype t]

def normalNodes : Finset t := (internalNodes t).erase ⊥
abbrev Normal := {v : t // v ∈ normalNodes t}
abbrev Parameters := (Normal t → ℂ) × (t → ℂ)

@[simp] theorem mem_normalNodes (v : t) : v ∈ normalNodes t ↔ v ≠ ⊥ ∧ ¬ IsMax v := by
  simp [normalNodes]

/-- The root complex scale is fixed to one; unused leaf scales are zero. -/
def weights (z : Normal t → ℂ) (v : t) : ℂ :=
  if hv : v ∈ normalNodes t then z ⟨v, hv⟩ else if v = ⊥ then 1 else 0

def includeParameters (x : Parameters t) : ComplexParameters t := (weights t x.1, x.2)

@[simp] theorem weights_normal (z : Normal t → ℂ) (v : Normal t) : weights t z v = z v := by
  simp [weights, v.property]

@[simp] theorem weights_root (z : Normal t → ℂ) : weights t z ⊥ = 1 := by simp [weights]

@[fun_prop] theorem analyticAt_include (x : Parameters t) : AnalyticAt ℂ (includeParameters t) x := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro v
    by_cases hv : v ∈ normalNodes t
    · simp only [weights, dif_pos hv]
      exact ((ContinuousLinearMap.proj (⟨v, hv⟩ : Normal t) : (Normal t → ℂ) →L[ℂ] ℂ).analyticAt x.1).comp
        ((ContinuousLinearMap.fst ℂ (Normal t → ℂ) (t → ℂ)).analyticAt x)
    · simp only [weights, dif_neg hv]
      exact analyticAt_const
  · exact (ContinuousLinearMap.snd ℂ (Normal t → ℂ) (t → ℂ)).analyticAt x

theorem weights_internal_ne_zero (x : Parameters t) (hx : ∀ v, x.1 v ≠ 0) :
    ∀ v ∈ internalNodes t, (includeParameters t x).1 v ≠ 0 := by
  intro v hv
  by_cases hroot : v = ⊥
  · subst v; simp [includeParameters]
  · have hnormal : v ∈ normalNodes t := Finset.mem_erase.mpr ⟨hroot, hv⟩
    simpa [includeParameters, weights, hnormal] using hx ⟨v, hnormal⟩

/-- Root rotation and root scale have exponent zero for every edge/reference ratio. -/
theorem pairRatio_monomial (x : Parameters t) (v w a b : t)
    (hvw : v ≠ w) (hab : a ≠ b) (hx : ∀ v, x.1 v ≠ 0) :
    ComplexForestInsertion.pairRatio t v w a b (includeParameters t x) =
      (∏ u : Normal t, x.1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u.val) *
        unitRatio t v w a b (includeParameters t x) := by
  rw [ComplexForestInsertion.pairRatio_monomial t _ v w a b hvw hab (weights_internal_ne_zero t x hx)]
  congr 1
  have hp : (∏ u ∈ normalNodes t, (includeParameters t x).1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u) =
      ∏ u ∈ internalNodes t, (includeParameters t x).1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u := by
    apply Finset.prod_subset (Finset.erase_subset _ _)
    intro u hu hnot
    have heq : u = ⊥ := by
      by_contra hne
      exact hnot (Finset.mem_erase.mpr ⟨hne, hu⟩)
    simp [heq]
  rw [← hp, ← Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro u hu
  simp [includeParameters]

theorem pairUnit_ne_zero_at_corner (η : t → ℂ) (hη : ChildShapesSeparated t η)
    {v w : t} (hv : IsMax v) (hw : IsMax w) (hne : v ≠ w) :
    pairUnit t (includeParameters t (0, η)) v w ≠ 0 := by
  apply leaf_unitDifference_ne_zero_at_face t (weights t 0) η hw hv hne.symm
  · intro u hu
    have hroot : u ≠ ⊥ := by
      intro h
      exact hu.not_ge (h ▸ bot_le)
    simp [weights, hroot]
  · exact hη _

/-- Changing only the root weight multiplies every insertion by the same scalar. -/
theorem scale_root_factor (w : t → ℂ) (v : t) :
    scale w v = w ⊥ * scale (Function.update w ⊥ 1) v := by
  letI : WellFoundedLT t := Finite.to_wellFoundedLT
  induction v using WellFoundedLT.induction with
  | ind v ih =>
    by_cases hv : v = ⊥
    · subst v; simp
    · rw [ForestNormalizationTelescope.scale_step t w v hv,
        ForestNormalizationTelescope.scale_step t (Function.update w ⊥ 1) v hv,
        Function.update_of_ne hv, ih (Order.pred v) (Order.pred_lt_iff_ne_bot.mpr hv)]
      ring

theorem complexCartesian_root_factor (w η : t → ℂ) (v : t) :
    complexCartesian t (w, η) v = w ⊥ * complexCartesian t (Function.update w ⊥ 1, η) v := by
  unfold complexCartesian position
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scale_root_factor t w (Order.pred k)]
  ring

/-- The reduced chart is the actual insertion with the common complex root scale removed. -/
theorem reducedCartesian_root_factor (w η : t → ℂ) (v : t) :
    complexCartesian t (w, η) v = w ⊥ *
      complexCartesian t (includeParameters t (fun u : Normal t ↦ w u.val, η)) v := by
  rw [complexCartesian_root_factor]
  congr 1
  apply complexCartesian_eq_of_internal_weights
  · intro u hu
    by_cases hroot : u = ⊥
    · subst u; simp [includeParameters]
    · have hn : u ∈ normalNodes t := (mem_normalNodes t u).mpr ⟨hroot, hu⟩
      simp [includeParameters, weights, hn, Function.update_of_ne hroot]
  · intro u hu; rfl

/-- The actual original real-radius positions differ by precisely the discarded
common complex root scale. No nonroot radius is divided out. -/
theorem phase_positions_root_factor (ρ : t → ℝ) (u η : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (v : t) :
    position t ρ η v = ((ρ ⊥ : ℂ) * u ⊥) *
      complexCartesian t (includeParameters t
        (fun k : Normal t ↦ complexWeight t ρ u k.val, normalizedIncrement t u η)) v := by
  rw [← position_complexWeight t ρ u η hu]
  simpa only [complexCartesian, complexWeight_root] using
    reducedCartesian_root_factor t (complexWeight t ρ u) (normalizedIncrement t u η) v

/-- All literal original pair ratios are invariant under removal of the root rotation. -/
theorem phase_pairRatio (ρ : t → ℝ) (u η : t → ℂ) (hu : ∀ v, u v ≠ 0)
    (hρ : ρ ⊥ ≠ 0) (v w a b : t) :
    (position t ρ η w - position t ρ η v) / (position t ρ η b - position t ρ η a) =
      ComplexForestInsertion.pairRatio t v w a b (includeParameters t
        (fun k : Normal t ↦ complexWeight t ρ u k.val, normalizedIncrement t u η)) := by
  rw [phase_positions_root_factor t ρ u η hu w, phase_positions_root_factor t ρ u η hu v,
    phase_positions_root_factor t ρ u η hu b, phase_positions_root_factor t ρ u η hu a,
    ← mul_sub, ← mul_sub, mul_div_mul_left _ _
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ) (hu ⊥))]
  rfl

variable {N : ℕ} (lab : Point N → t)

/-- All actual leaf units stay nonzero on one common open neighborhood. -/
def unitLocus : Set (Parameters t) :=
  {x | ∀ j k : Point N, j ≠ k → pairUnit t (includeParameters t x) (lab j) (lab k) ≠ 0}

theorem isOpen_unitLocus : IsOpen (unitLocus t lab) := by
  have heq : unitLocus t lab = ⋂ j : Point N, ⋂ k : Point N,
      {x : Parameters t | j ≠ k → pairUnit t (includeParameters t x) (lab j) (lab k) ≠ 0} := by
    ext x; simp [unitLocus]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro k
  by_cases hjk : j = k
  · simp [hjk]
  · have heq : {x : Parameters t | j ≠ k → pairUnit t (includeParameters t x) (lab j) (lab k) ≠ 0} =
        {x : Parameters t | pairUnit t (includeParameters t x) (lab j) (lab k) ≠ 0} := by
      ext x; simp [hjk]
    rw [heq]
    exact isOpen_ne_fun (continuous_iff_continuousAt.mpr (fun x ↦
      ((analyticAt_pairUnit t (lab j) (lab k) _).comp (analyticAt_include t x)).continuousAt)) continuous_const

theorem corner_mem_unitLocus (hinj : Function.Injective lab) (hleaf : ∀ j, IsMax (lab j))
    (η : t → ℂ) (hη : ChildShapesSeparated t η) : (0, η) ∈ unitLocus t lab := by
  intro j k hjk
  exact pairUnit_ne_zero_at_corner t η hη (hleaf j) (hleaf k) (hinj.ne hjk)

/-- A bounded neighborhood supporting every edge and every choice of reference pair. -/
theorem bounded_unit_neighborhood (hinj : Function.Injective lab) (hleaf : ∀ j, IsMax (lab j))
    (η : t → ℂ) (hη : ChildShapesSeparated t η) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0, η) ε ⊆ unitLocus t lab :=
  Metric.isOpen_iff.mp (isOpen_unitLocus t lab) _ (corner_mem_unitLocus t lab hinj hleaf η hη)

def puncturedLocus : Set (Parameters t) := unitLocus t lab ∩ {x | ∀ v, x.1 v ≠ 0}

theorem isOpen_puncturedLocus : IsOpen (puncturedLocus t lab) := by
  apply (isOpen_unitLocus t lab).inter
  have heq : {x : Parameters t | ∀ v, x.1 v ≠ 0} =
      ⋂ v : Normal t, {x : Parameters t | x.1 v ≠ 0} := by ext x; simp
  rw [heq]
  apply isOpen_iInter_of_finite
  intro v
  exact isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const

/-- The actual normalized affine quotient of the inserted leaf positions. -/
def normalizedShape (x : Parameters t) : Shape N := fun j ↦
  ComplexForestInsertion.pairRatio t (lab 0) (lab j.succ.succ) (lab 0) (lab 1) (includeParameters t x)

theorem reference_ne_zero (hinj : Function.Injective lab) {x : Parameters t}
    (hx : x ∈ puncturedLocus t lab) : pairDifference t (includeParameters t x) (lab 0) (lab 1) ≠ 0 :=
  pairDifference_ne_zero t _ _ _ (hinj.ne Fin.zero_ne_one)
    (weights_internal_ne_zero t x hx.2) (hx.1 0 1 Fin.zero_ne_one)

theorem normalizedPoint_normalizedShape (hinj : Function.Injective lab) {x : Parameters t}
    (hx : x ∈ puncturedLocus t lab) (j : Point N) :
    normalizedPoint (normalizedShape t lab x) j =
      pairDifference t (includeParameters t x) (lab 0) (lab j) /
        pairDifference t (includeParameters t x) (lab 0) (lab 1) := by
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j
  · simp [pairDifference]
  · simpa using (div_self (reference_ne_zero t lab hinj hx)).symm
  · rfl

theorem normalizedShape_mem_configuration (hinj : Function.Injective lab) {x : Parameters t}
    (hx : x ∈ puncturedLocus t lab) : normalizedShape t lab x ∈ shapeConfiguration N := by
  intro j k heq
  rw [normalizedPoint_normalizedShape t lab hinj hx,
    normalizedPoint_normalizedShape t lab hinj hx] at heq
  have hd := (div_left_inj' (reference_ne_zero t lab hinj hx)).mp heq
  by_contra hjk
  have hdiff := pairDifference_ne_zero t (includeParameters t x) (lab j) (lab k) (hinj.ne hjk)
    (weights_internal_ne_zero t x hx.2) (hx.1 j k hjk)
  apply hdiff
  simp only [pairDifference] at hd ⊢
  exact sub_eq_zero.mpr (sub_left_inj.mp hd).symm

/-- A genuine map into X_N, derived from the insertion's collision complement. -/
def configurationMap (hinj : Function.Injective lab) (x : puncturedLocus t lab) :
    PlanarNormalizedCoordinates.Configuration N :=
  ⟨normalizedShape t lab x.val, normalizedShape_mem_configuration t lab hinj x.property⟩

theorem analyticOnNhd_normalizedShape (hinj : Function.Injective lab) :
    AnalyticOnNhd ℂ (normalizedShape t lab) (puncturedLocus t lab) := by
  intro x hx
  apply AnalyticAt.pi
  intro j
  exact (analyticAt_pairRatio t _ _ _ _ (includeParameters t x) (hinj.ne Fin.zero_ne_one)
    (weights_internal_ne_zero t x hx.2) (hx.1 0 1 Fin.zero_ne_one)).comp (analyticAt_include t x)

/-- Every original normalized pair/reference quotient is the literal insertion quotient.
The two LCAs are allowed to be incomparable. -/
theorem normalized_pairRatio (hinj : Function.Injective lab) {x : Parameters t}
    (hx : x ∈ puncturedLocus t lab) (j k a b : Point N) :
    shapeDifference j k (normalizedShape t lab x) /
        shapeDifference a b (normalizedShape t lab x) =
      ComplexForestInsertion.pairRatio t (lab j) (lab k) (lab a) (lab b) (includeParameters t x) := by
  simp only [shapeDifference, normalizedPoint_normalizedShape t lab hinj hx,
    ← sub_div]
  have hk : pairDifference t (includeParameters t x) (lab 0) (lab k) -
      pairDifference t (includeParameters t x) (lab 0) (lab j) =
      pairDifference t (includeParameters t x) (lab j) (lab k) := by
    unfold pairDifference; abel
  have hb : pairDifference t (includeParameters t x) (lab 0) (lab b) -
      pairDifference t (includeParameters t x) (lab 0) (lab a) =
      pairDifference t (includeParameters t x) (lab a) (lab b) := by
    unfold pairDifference; abel
  rw [hk, hb, div_div_div_cancel_right₀ (reference_ne_zero t lab hinj hx)]
  rfl

theorem normalized_pairRatio_monomial (hinj : Function.Injective lab) {x : Parameters t}
    (hx : x ∈ puncturedLocus t lab) (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    shapeDifference j k (normalizedShape t lab x) /
        shapeDifference a b (normalizedShape t lab x) =
      (∏ u : Normal t, x.1 u ^ ancestorExponent t (lab j ⊓ lab k) (lab a ⊓ lab b) u.val) *
        unitRatio t (lab j) (lab k) (lab a) (lab b) (includeParameters t x) := by
  rw [normalized_pairRatio t lab hinj hx]
  exact pairRatio_monomial t x _ _ _ _ (hinj.ne hjk) (hinj.ne hab) hx.2

/-- The explicit units are jointly holomorphic in normal and shape variables
throughout the same common neighborhood, including every zero normal coordinate. -/
theorem analyticOnNhd_unit (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    AnalyticOnNhd ℂ (fun x : Parameters t ↦ unitRatio t (lab j) (lab k) (lab a) (lab b)
      (includeParameters t x)) (unitLocus t lab) := by
  intro x hx
  exact ((analyticOnNhd_unitRatio t (lab j) (lab k) (lab a) (lab b)) _
    ⟨hx j k hjk, hx a b hab⟩).comp (analyticAt_include t x)

theorem unit_ne_zero {x : Parameters t} (hx : x ∈ unitLocus t lab)
    (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    unitRatio t (lab j) (lab k) (lab a) (lab b) (includeParameters t x) ≠ 0 :=
  div_ne_zero (hx j k hjk) (hx a b hab)

theorem analyticOnNhd_inv_unit (j k a b : Point N) (hjk : j ≠ k) (hab : a ≠ b) :
    AnalyticOnNhd ℂ (fun x : Parameters t ↦ (unitRatio t (lab j) (lab k) (lab a) (lab b)
      (includeParameters t x))⁻¹) (unitLocus t lab) := by
  intro x hx
  exact ((analyticOnNhd_unit t lab j k a b hjk hab) x hx).inv
    (unit_ne_zero t lab hx j k a b hjk hab)

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestNormalizedCharts
