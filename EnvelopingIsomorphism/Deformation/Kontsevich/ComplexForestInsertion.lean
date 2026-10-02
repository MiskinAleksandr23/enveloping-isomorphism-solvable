import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii
import Mathlib.Analysis.Analytic.Constructions

/-! Actual complex forest insertion coordinates and holomorphic monomial pair ratios.
Phase ratios telescope without dividing by any real radius. Leaf weights and the
root increment do not affect positions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestInsertion

open AncestorScaleRatios ForestInsertionDifference ForestNormalizationTelescope
open scoped BigOperators Classical Topology

variable (t : RootedTree) [Fintype t]

def complexWeight (ρ : t → ℝ) (u : t → ℂ) (v : t) : ℂ :=
  if v = ⊥ then (ρ v : ℂ) * u v else (ρ v : ℂ) * u v / u (Order.pred v)

def normalizedIncrement (u a : t → ℂ) (v : t) : ℂ :=
  if v = ⊥ then a v else a v / u (Order.pred v)

omit [Fintype t] in
@[simp] theorem complexWeight_root (ρ : t → ℝ) (u : t → ℂ) :
    complexWeight t ρ u ⊥ = (ρ ⊥ : ℂ) * u ⊥ := by simp [complexWeight]

omit [Fintype t] in
theorem complexWeight_nonroot (ρ : t → ℝ) (u : t → ℂ) {v : t} (hv : v ≠ ⊥) :
    complexWeight t ρ u v = (ρ v : ℂ) * u v / u (Order.pred v) := by simp [complexWeight, hv]

/-- The actual complex ancestor scale is the real scale times the terminal phase.
Only phases are cancelled; every real radius may vanish or be negative. -/
theorem scale_complexWeight (ρ : t → ℝ) (u : t → ℂ) (hu : ∀ v, u v ≠ 0) (v : t) :
    scale (complexWeight t ρ u) v = ((scale ρ v : ℝ) : ℂ) * u v := by
  letI : WellFoundedLT t := Finite.to_wellFoundedLT
  induction v using WellFoundedLT.induction with
  | ind v ih =>
    by_cases hv : v = ⊥
    · subst v
      simp
    · rw [scale_step t _ v hv, complexWeight_nonroot t ρ u hv,
        ih (Order.pred v) (Order.pred_lt_iff_ne_bot.mpr hv), scale_step t ρ v hv, Complex.ofReal_mul]
      field_simp [hu (Order.pred v)]

/-- Literal complex insertion equals the original real-radius insertion. -/
theorem position_complexWeight (ρ : t → ℝ) (u a : t → ℂ) (hu : ∀ v, u v ≠ 0) (v : t) :
    position t (complexWeight t ρ u) (normalizedIncrement t u a) v = position t ρ a v := by
  unfold position
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := (Finset.mem_erase.mp hk).1
  rw [scale_complexWeight t ρ u hu, normalizedIncrement, if_neg hk0, smul_eq_mul, Complex.real_smul]
  field_simp [hu (Order.pred k)]

theorem position_complexWeight_rootIncrement (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (c : ℂ) (v : t) :
    position t (complexWeight t ρ u) (Function.update (normalizedIncrement t u a) ⊥ c) v =
      position t ρ a v := by
  rw [position_congr_nonroot t (complexWeight t ρ u) _ (normalizedIncrement t u a)
    (fun k hk ↦ Function.update_of_ne hk _ _) v]
  exact position_complexWeight t ρ u a hu v

abbrev ComplexParameters := (t → ℂ) × (t → ℂ)

def complexCartesian (x : ComplexParameters t) (v : t) : ℂ := position t x.1 x.2 v

def pairDifference (x : ComplexParameters t) (v w : t) : ℂ := complexCartesian t x w - complexCartesian t x v

def pairUnit (x : ComplexParameters t) (v w : t) : ℂ := unitDifference t x.1 x.2 w v

theorem pairDifference_factor (x : ComplexParameters t) (v w : t) :
    pairDifference t x v w = scale x.1 (v ⊓ w) * pairUnit t x v w := by
  simpa only [pairDifference, complexCartesian, pairUnit, inf_comm, smul_eq_mul] using
    position_sub_position t x.1 x.2 w v

theorem complexCartesian_eq_of_internal_weights (x y : ComplexParameters t)
    (hw : ∀ v, ¬ IsMax v → x.1 v = y.1 v) (hη : ∀ v, v ≠ ⊥ → x.2 v = y.2 v) (v : t) :
    complexCartesian t x v = complexCartesian t y v := by
  rw [complexCartesian, complexCartesian, ForestLeafRadii.position_eq t x.1 y.1 hw]
  exact position_congr_nonroot t y.1 x.2 y.2 hη v

@[fun_prop] theorem analyticAt_scale (v : t) (x : t → ℂ) : AnalyticAt ℂ (fun w : t → ℂ ↦ scale w v) x := by
  unfold scale
  apply Finset.analyticAt_fun_prod
  intro k hk
  exact (ContinuousLinearMap.proj k : (t → ℂ) →L[ℂ] ℂ).analyticAt x

@[fun_prop] theorem analyticAt_residualScale (v w : t) (x : t → ℂ) :
    AnalyticAt ℂ (fun z : t → ℂ ↦ residualScale z v w) x := by
  unfold residualScale
  apply Finset.analyticAt_fun_prod
  intro k hk
  exact (ContinuousLinearMap.proj k : (t → ℂ) →L[ℂ] ℂ).analyticAt x

@[fun_prop] theorem analyticAt_complexCartesian (v : t) (x : ComplexParameters t) :
    AnalyticAt ℂ (fun y : ComplexParameters t ↦ complexCartesian t y v) x := by
  unfold complexCartesian position
  simp only [smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact ((analyticAt_scale t (Order.pred k) x.1).comp
    ((ContinuousLinearMap.fst ℂ (t → ℂ) (t → ℂ)).analyticAt x)).mul
      (((ContinuousLinearMap.proj k : (t → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp
        ((ContinuousLinearMap.snd ℂ (t → ℂ) (t → ℂ)).analyticAt x))

@[fun_prop] theorem analyticAt_branchUnit (c v : t) (x : ComplexParameters t) :
    AnalyticAt ℂ (fun y : ComplexParameters t ↦ branchUnit t y.1 y.2 c v) x := by
  unfold branchUnit
  simp only [smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact ((analyticAt_residualScale t c (Order.pred k) x.1).comp
    ((ContinuousLinearMap.fst ℂ (t → ℂ) (t → ℂ)).analyticAt x)).mul
      (((ContinuousLinearMap.proj k : (t → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp
        ((ContinuousLinearMap.snd ℂ (t → ℂ) (t → ℂ)).analyticAt x))

@[fun_prop] theorem analyticAt_pairUnit (v w : t) (x : ComplexParameters t) :
    AnalyticAt ℂ (fun y : ComplexParameters t ↦ pairUnit t y v w) x :=
  (analyticAt_branchUnit t _ _ x).sub (analyticAt_branchUnit t _ _ x)

@[fun_prop] theorem analyticAt_pairDifference (v w : t) (x : ComplexParameters t) :
    AnalyticAt ℂ (fun y : ComplexParameters t ↦ pairDifference t y v w) x :=
  (analyticAt_complexCartesian t w x).sub (analyticAt_complexCartesian t v x)

/-- Only nonleaf weights enter any genuine insertion scale. The root is retained. -/
def internalNodes : Finset t := Finset.univ.filter (fun v ↦ ¬ IsMax v)

@[simp] theorem mem_internalNodes (v : t) : v ∈ internalNodes t ↔ ¬ IsMax v := by simp [internalNodes]

def ancestorIndicator (v u : t) : ℤ := if u ≤ v then 1 else 0

/-- Integer differences of ancestor indicators; no comparability of v and w is required. -/
def ancestorExponent (v w u : t) : ℤ := ancestorIndicator t v u - ancestorIndicator t w u

omit [Fintype t] in
theorem ancestorExponent_negative {v w u : t} (huv : ¬ u ≤ v) (huw : u ≤ w) :
    ancestorExponent t v w u = -1 := by simp [ancestorExponent, ancestorIndicator, huv, huw]

omit [Fintype t] in
theorem ancestorExponent_positive {v w u : t} (huv : u ≤ v) (huw : ¬ u ≤ w) :
    ancestorExponent t v w u = 1 := by simp [ancestorExponent, ancestorIndicator, huv, huw]

omit [Fintype t] in
@[simp] theorem ancestorExponent_root (v w : t) : ancestorExponent t v w ⊥ = 0 := by
  simp [ancestorExponent, ancestorIndicator]

omit [Fintype t] in
theorem inf_nonleaf {v w : t} (hne : v ≠ w) : ¬ IsMax (v ⊓ w) := by
  intro hmax
  have hv : v ⊓ w = v := le_antisymm inf_le_left (hmax inf_le_left)
  have hw : v ⊓ w = w := le_antisymm inf_le_right (hmax inf_le_right)
  exact hne (hv.symm.trans hw)

theorem scale_eq_full_monomial (w : t → ℂ) (v : t) :
    scale w v = ∏ u : t, w u ^ ancestorIndicator t v u := by
  unfold scale ancestors
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro u hu
  by_cases h : u ≤ v <;> simp [ancestorIndicator, h]

omit [Fintype t] in
theorem ancestorIndicator_eq_zero_of_leaf {v u : t} (hv : ¬ IsMax v) (hu : IsMax u) :
    ancestorIndicator t v u = 0 := by
  have hnot : ¬ u ≤ v := by
    intro h
    have heq := le_antisymm h (hu h)
    exact hv (heq ▸ hu)
  simp [ancestorIndicator, hnot]

theorem scale_eq_internal_monomial (w : t → ℂ) (v : t) (hv : ¬ IsMax v) :
    scale w v = ∏ u ∈ internalNodes t, w u ^ ancestorIndicator t v u := by
  rw [scale_eq_full_monomial]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro u hu hnot
  have hmax : IsMax u := by
    by_contra h
    exact hnot ((mem_internalNodes t u).mpr h)
  rw [ancestorIndicator_eq_zero_of_leaf t hv hmax, zpow_zero]

/-- The quotient of arbitrary ancestor scales is an integer monomial in the
actual internal complex weights, including incomparable ancestor branches. -/
theorem scale_ratio_eq_internal_monomial (w : t → ℂ)
    (hw : ∀ u ∈ internalNodes t, w u ≠ 0) (v z : t) (hv : ¬ IsMax v) (hz : ¬ IsMax z) :
    scale w v / scale w z = ∏ u ∈ internalNodes t, w u ^ ancestorExponent t v z u := by
  rw [scale_eq_internal_monomial t w v hv, scale_eq_internal_monomial t w z hz,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  exact (zpow_sub₀ (hw u hu) _ _).symm

def unitRatio (v w a b : t) (x : ComplexParameters t) : ℂ := pairUnit t x v w / pairUnit t x a b

def pairRatio (v w a b : t) (x : ComplexParameters t) : ℂ :=
  pairDifference t x v w / pairDifference t x a b

/-- Literal edge/reference difference quotient, with both units and all integer
normal exponents computed from the actual insertion and the two LCAs. -/
theorem pairRatio_monomial (x : ComplexParameters t) (v w a b : t)
    (hvw : v ≠ w) (hab : a ≠ b) (hw : ∀ u ∈ internalNodes t, x.1 u ≠ 0) :
    pairRatio t v w a b x =
      (∏ u ∈ internalNodes t, x.1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u) * unitRatio t v w a b x := by
  rw [pairRatio, pairDifference_factor, pairDifference_factor, mul_div_mul_comm,
    scale_ratio_eq_internal_monomial t x.1 hw _ _ (inf_nonleaf t hvw) (inf_nonleaf t hab)]
  rfl

def unitDomain (v w a b : t) : Set (ComplexParameters t) :=
  {x | pairUnit t x v w ≠ 0 ∧ pairUnit t x a b ≠ 0}

theorem isOpen_unitDomain (v w a b : t) : IsOpen (unitDomain t v w a b) := by
  have hp : Continuous (fun x : ComplexParameters t ↦ pairUnit t x v w) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (analyticAt_pairUnit t v w x).continuousAt)
  have hq : Continuous (fun x : ComplexParameters t ↦ pairUnit t x a b) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (analyticAt_pairUnit t a b x).continuousAt)
  exact (isOpen_ne_fun hp continuous_const).inter (isOpen_ne_fun hq continuous_const)

theorem analyticOnNhd_unitRatio (v w a b : t) :
    AnalyticOnNhd ℂ (unitRatio t v w a b) (unitDomain t v w a b) := by
  intro x hx
  exact (analyticAt_pairUnit t v w x).div (analyticAt_pairUnit t a b x) hx.2

theorem unitRatio_ne_zero (v w a b : t) (x : ComplexParameters t) (hx : x ∈ unitDomain t v w a b) :
    unitRatio t v w a b x ≠ 0 := div_ne_zero hx.1 hx.2

theorem pairUnit_eq_of_internal_weights (x y : ComplexParameters t)
    (hw : ∀ v, ¬ IsMax v → x.1 v = y.1 v) (hη : x.2 = y.2) (v w : t) :
    pairUnit t x v w = pairUnit t y v w := by
  unfold pairUnit
  rw [ForestLeafRadii.unitDifference_eq t x.1 y.1 hw, hη]

def ChildShapesSeparated (η : t → ℂ) : Prop :=
  ∀ c d e : t, c ⋖ d → c ⋖ e → d ≠ e → η d ≠ η e

/-- Distinct leaf branches produce an actual nonzero polynomial unit at the
collapsed internal-weight face. Unused leaf weights may have arbitrary values. -/
theorem pairUnit_ne_zero_at_corner (x : ComplexParameters t)
    (hzero : ∀ u ∈ internalNodes t, x.1 u = 0) (hshape : ChildShapesSeparated t x.2)
    (v w : t) (hv : IsMax v) (hw : IsMax w) (hne : v ≠ w) : pairUnit t x v w ≠ 0 := by
  have heq : pairUnit t x v w = pairUnit t (0, x.2) v w :=
    pairUnit_eq_of_internal_weights t x (0, x.2) (fun u hu ↦ hzero u ((mem_internalNodes t u).mpr hu)) rfl v w
  rw [heq, pairUnit]
  apply leaf_unitDifference_ne_zero_at_face t (0 : t → ℂ) x.2 hw hv hne.symm
  · intro u hu
    rfl
  · intro d e hd he hde
    exact hshape _ d e hd he hde

/-- The actual holomorphic unit ratio has a genuine open nonvanishing neighborhood
at a separated forest corner; its construction is not a normal-form assumption. -/
theorem unitDomain_mem_nhds_at_corner (x : ComplexParameters t)
    (hzero : ∀ u ∈ internalNodes t, x.1 u = 0) (hshape : ChildShapesSeparated t x.2)
    (v w a b : t) (hv : IsMax v) (hw : IsMax w) (ha : IsMax a) (hb : IsMax b)
    (hvw : v ≠ w) (hab : a ≠ b) : unitDomain t v w a b ∈ nhds x :=
  (isOpen_unitDomain t v w a b).mem_nhds
    ⟨pairUnit_ne_zero_at_corner t x hzero hshape v w hv hw hvw,
      pairUnit_ne_zero_at_corner t x hzero hshape a b ha hb hab⟩

/-- Genuine independent complex normal coordinates: unused leaf weights are absent. -/
abbrev Internal := {v : t // v ∈ internalNodes t}
abbrev InternalParameters := (Internal t → ℂ) × (t → ℂ)

def extendWeights (w : Internal t → ℂ) (v : t) : ℂ :=
  if hv : v ∈ internalNodes t then w ⟨v, hv⟩ else 1

def includeParameters (x : InternalParameters t) : ComplexParameters t := (extendWeights t x.1, x.2)

@[simp] theorem extendWeights_internal (w : Internal t → ℂ) (v : Internal t) :
    extendWeights t w v.val = w v := by simp [extendWeights, v.property]

@[fun_prop] theorem analyticAt_includeParameters (x : InternalParameters t) :
    AnalyticAt ℂ (includeParameters t) x := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro v
    by_cases hv : v ∈ internalNodes t
    · simp only [extendWeights, dif_pos hv]
      exact ((ContinuousLinearMap.proj (⟨v, hv⟩ : Internal t) : (Internal t → ℂ) →L[ℂ] ℂ).analyticAt x.1).comp
        ((ContinuousLinearMap.fst ℂ (Internal t → ℂ) (t → ℂ)).analyticAt x)
    · simp only [extendWeights, dif_neg hv]
      exact analyticAt_const
  · exact (ContinuousLinearMap.snd ℂ (Internal t → ℂ) (t → ℂ)).analyticAt x

def internalCartesian (x : InternalParameters t) (v : t) : ℂ := complexCartesian t (includeParameters t x) v
def internalUnitRatio (v w a b : t) (x : InternalParameters t) : ℂ := unitRatio t v w a b (includeParameters t x)
def internalPairRatio (v w a b : t) (x : InternalParameters t) : ℂ := pairRatio t v w a b (includeParameters t x)

@[fun_prop] theorem analyticAt_internalCartesian (v : t) (x : InternalParameters t) :
    AnalyticAt ℂ (fun y ↦ internalCartesian t y v) x :=
  (analyticAt_complexCartesian t v (includeParameters t x)).comp (analyticAt_includeParameters t x)

theorem analyticOnNhd_internalUnitRatio (v w a b : t) :
    AnalyticOnNhd ℂ (internalUnitRatio t v w a b)
      (includeParameters t ⁻¹' unitDomain t v w a b) := by
  intro x hx
  exact ((analyticOnNhd_unitRatio t v w a b) _ hx).comp (analyticAt_includeParameters t x)

theorem internalUnitRatio_ne_zero (v w a b : t) (x : InternalParameters t)
    (hx : includeParameters t x ∈ unitDomain t v w a b) : internalUnitRatio t v w a b x ≠ 0 :=
  unitRatio_ne_zero t v w a b _ hx

theorem internalPairRatio_monomial (x : InternalParameters t) (v w a b : t)
    (hvw : v ≠ w) (hab : a ≠ b) (hw : ∀ u, x.1 u ≠ 0) :
    internalPairRatio t v w a b x =
      (∏ u : Internal t, x.1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u.val) * internalUnitRatio t v w a b x := by
  have hweights : ∀ u ∈ internalNodes t, (includeParameters t x).1 u ≠ 0 := by
    intro u hu
    simpa only [includeParameters, extendWeights, dif_pos hu] using hw ⟨u, hu⟩
  rw [internalPairRatio, pairRatio_monomial t (includeParameters t x) v w a b hvw hab hweights]
  congr 1
  rw [← Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro u hu
  simp only [includeParameters, extendWeights_internal]

/-- The complex phase-ratio coordinates also give the literal old positions after
discarding all unused leaf weights. -/
theorem internalCartesian_phase_coordinates (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (v : t) :
    internalCartesian t ((fun q : Internal t ↦ complexWeight t ρ u q.val), normalizedIncrement t u a) v =
      position t ρ a v := by
  have h := complexCartesian_eq_of_internal_weights t
    (complexWeight t ρ u, normalizedIncrement t u a)
    (includeParameters t ((fun q : Internal t ↦ complexWeight t ρ u q.val), normalizedIncrement t u a))
    (fun w hw ↦ by simp [includeParameters, extendWeights, (mem_internalNodes t w).mpr hw])
    (fun _ _ ↦ rfl) v
  exact h.symm.trans (position_complexWeight t ρ u a hu v)

def internalUnitDomain (v w a b : t) : Set (InternalParameters t) :=
  includeParameters t ⁻¹' unitDomain t v w a b

theorem isOpen_internalUnitDomain (v w a b : t) : IsOpen (internalUnitDomain t v w a b) :=
  (isOpen_unitDomain t v w a b).preimage
    (continuous_iff_continuousAt.mpr (fun x ↦ (analyticAt_includeParameters t x).continuousAt))

theorem corner_mem_internalUnitDomain (η : t → ℂ) (hshape : ChildShapesSeparated t η)
    (v w a b : t) (hv : IsMax v) (hw : IsMax w) (ha : IsMax a) (hb : IsMax b)
    (hvw : v ≠ w) (hab : a ≠ b) : (0, η) ∈ internalUnitDomain t v w a b := by
  have hzero : ∀ u ∈ internalNodes t, (includeParameters t (0, η)).1 u = 0 := by
    intro u hu
    simp [includeParameters, extendWeights, hu]
  exact ⟨pairUnit_ne_zero_at_corner t (includeParameters t (0, η)) hzero hshape v w hv hw hvw,
    pairUnit_ne_zero_at_corner t (includeParameters t (0, η)) hzero hshape a b ha hb hab⟩

/-- A genuine local holomorphic monomial normal form near a separated pure-complex
forest corner. The unit and exponent map are the explicit functions above. -/
theorem internal_normalForm_near_corner (η : t → ℂ) (hshape : ChildShapesSeparated t η)
    (v w a b : t) (hv : IsMax v) (hw : IsMax w) (ha : IsMax a) (hb : IsMax b)
    (hvw : v ≠ w) (hab : a ≠ b) :
    ∃ U : Set (InternalParameters t), IsOpen U ∧ (0, η) ∈ U ∧
      AnalyticOnNhd ℂ (internalUnitRatio t v w a b) U ∧
      (∀ x ∈ U, internalUnitRatio t v w a b x ≠ 0) ∧
      ∀ x ∈ U, (∀ u : Internal t, x.1 u ≠ 0) →
        internalPairRatio t v w a b x =
          (∏ u : Internal t, x.1 u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u.val) *
            internalUnitRatio t v w a b x := by
  refine ⟨internalUnitDomain t v w a b, isOpen_internalUnitDomain t v w a b,
    corner_mem_internalUnitDomain t η hshape v w a b hv hw ha hb hvw hab,
    analyticOnNhd_internalUnitRatio t v w a b, ?_, ?_⟩
  · exact fun x hx ↦ internalUnitRatio_ne_zero t v w a b x hx
  · exact fun x hx hweights ↦ internalPairRatio_monomial t x v w a b hvw hab hweights

def fixedShapeUnit (η : t → ℂ) (v w a b : t) (z : Internal t → ℂ) : ℂ :=
  internalUnitRatio t v w a b (z, η)

def fixedShapePairRatio (η : t → ℂ) (v w a b : t) (z : Internal t → ℂ) : ℂ :=
  internalPairRatio t v w a b (z, η)

/-- With shape coordinates fixed, the same unit is genuinely holomorphic in only
the independent complex normal weights, ready for the monomial-current interface. -/
theorem fixedShape_normalForm_near_zero (η : t → ℂ) (hshape : ChildShapesSeparated t η)
    (v w a b : t) (hv : IsMax v) (hw : IsMax w) (ha : IsMax a) (hb : IsMax b)
    (hvw : v ≠ w) (hab : a ≠ b) :
    ∃ U : Set (Internal t → ℂ), IsOpen U ∧ (0 : Internal t → ℂ) ∈ U ∧
      AnalyticOnNhd ℂ (fixedShapeUnit t η v w a b) U ∧
      (∀ z ∈ U, fixedShapeUnit t η v w a b z ≠ 0) ∧
      ∀ z ∈ U, (∀ u : Internal t, z u ≠ 0) →
        fixedShapePairRatio t η v w a b z =
          (∏ u : Internal t, z u ^ ancestorExponent t (v ⊓ w) (a ⊓ b) u.val) *
            fixedShapeUnit t η v w a b z := by
  obtain ⟨V, hV, h0, hhol, hne, hfac⟩ := internal_normalForm_near_corner t η hshape v w a b hv hw ha hb hvw hab
  let f : (Internal t → ℂ) → InternalParameters t := fun z ↦ (z, η)
  have hf (z : Internal t → ℂ) : AnalyticAt ℂ f z := analyticAt_id.prod analyticAt_const
  refine ⟨f ⁻¹' V, hV.preimage (continuous_iff_continuousAt.mpr (fun z ↦ (hf z).continuousAt)), h0, ?_, ?_, ?_⟩
  · exact fun z hz ↦ (hhol (f z) hz).comp (hf z)
  · exact fun z hz ↦ hne (f z) hz
  · exact fun z hz hweights ↦ hfac (f z) hz hweights

theorem scale_ne_zero_of_internal_weights (w : t → ℂ)
    (hw : ∀ u ∈ internalNodes t, w u ≠ 0) (v : t) (hv : ¬ IsMax v) : scale w v ≠ 0 := by
  rw [scale_eq_internal_monomial t w v hv]
  exact Finset.prod_ne_zero_iff.mpr (fun u hu ↦ zpow_ne_zero _ (hw u hu))

/-- On the punctured normal chart the literal reference difference is nonzero,
so the ratio theorem concerns the actual geometric quotient, not total division by zero. -/
theorem pairDifference_ne_zero (x : ComplexParameters t) (v w : t) (hvw : v ≠ w)
    (hw : ∀ u ∈ internalNodes t, x.1 u ≠ 0) (hu : pairUnit t x v w ≠ 0) :
    pairDifference t x v w ≠ 0 := by
  rw [pairDifference_factor]
  exact mul_ne_zero (scale_ne_zero_of_internal_weights t x.1 hw _ (inf_nonleaf t hvw)) hu

theorem analyticAt_pairRatio (v w a b : t) (x : ComplexParameters t) (hab : a ≠ b)
    (hw : ∀ u ∈ internalNodes t, x.1 u ≠ 0) (hu : pairUnit t x a b ≠ 0) :
    AnalyticAt ℂ (pairRatio t v w a b) x :=
  (analyticAt_pairDifference t v w x).div (analyticAt_pairDifference t a b x)
    (pairDifference_ne_zero t x a b hab hw hu)

/-- The explicit holomorphic unit has an actual holomorphic reciprocal. -/
theorem analyticOnNhd_inv_unitRatio (v w a b : t) :
    AnalyticOnNhd ℂ (fun x ↦ (unitRatio t v w a b x)⁻¹) (unitDomain t v w a b) := by
  intro x hx
  exact ((analyticOnNhd_unitRatio t v w a b) x hx).inv (unitRatio_ne_zero t v w a b x hx)

omit [Fintype t] in
theorem normalizedIncrement_child (u a : t → ℂ) {c v : t} (hcv : c ⋖ v) :
    normalizedIncrement t u a v = a v / u c := by
  have hv : v ≠ ⊥ := by
    intro hv
    exact (hcv.lt.not_ge (hv ▸ bot_le))
  rw [normalizedIncrement, if_neg hv, hcv.pred_eq]

omit [Fintype t] in
theorem childShapesSeparated_normalizedIncrement (u a : t → ℂ) (hu : ∀ v, u v ≠ 0)
    (ha : ChildShapesSeparated t a) : ChildShapesSeparated t (normalizedIncrement t u a) := by
  intro c d e hcd hce hde h
  rw [normalizedIncrement_child t u a hcd, normalizedIncrement_child t u a hce] at h
  apply ha c d e hcd hce hde
  have hh := congrArg (fun z : ℂ ↦ z * u c) h
  simpa only [div_mul_cancel₀ _ (hu c)] using hh

/-- Actual separated real-frame child increments, after phase normalization,
produce the required nonzero holomorphic unit neighborhood at a collapsed corner. -/
theorem phase_corner_unitDomain_mem_nhds (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (hρ : ∀ z ∈ internalNodes t, ρ z = 0) (hshape : ChildShapesSeparated t a)
    (v w c d : t) (hv : IsMax v) (hw : IsMax w) (hc : IsMax c) (hd : IsMax d)
    (hvw : v ≠ w) (hcd : c ≠ d) :
    unitDomain t v w c d ∈ nhds (complexWeight t ρ u, normalizedIncrement t u a) := by
  apply unitDomain_mem_nhds_at_corner t _ _
    (childShapesSeparated_normalizedIncrement t u a hu hshape) v w c d hv hw hc hd hvw hcd
  intro z hz
  simp only [complexWeight, hρ z hz, Complex.ofReal_zero, zero_mul, zero_div, ite_self]

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestInsertion
