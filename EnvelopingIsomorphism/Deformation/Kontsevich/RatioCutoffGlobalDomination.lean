import EnvelopingIsomorphism.Deformation.Kontsevich.CutoffErrorPullback
import EnvelopingIsomorphism.Deformation.Kontsevich.FiniteChartPartition

/-! Actual ratio-cutoff error convergence from a finite monomial chart cover.
Only local geometry and unit data enter the chart hypotheses. The varying
coefficients, alternating determinant, absolute Jacobian, measurable partition,
and dominated convergence are all derived for the original cutoff error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffGlobalDomination

open Set MeasureTheory Filter ContinuousAlternatingMap
open InteriorFiberAngleSplit NormalCrossingStokes RatioCutoffStokes
open scoped Topology BigOperators

variable {N : ℕ}

/-- Geometric and scalar monomial data for an actual chart of the original
configuration space. There is no bound or convergence hypothesis on a form. -/
structure ErrorChart (e : RatioCutoffStokes.Edges N) where
  monomial : BoundedLogMonomialCombination.LocalData (Fin (N + 1))
    (RatioCutoff.RadialIndex (N + 1)) (Degree N)
  map : Space N → Space N
  map_C1 : ∀ x ∈ monomial.region, ContDiffAt ℝ 1 map x
  map_injective : InjOn map monomial.region
  image_open : IsOpen (map '' monomial.region)
  image_configuration : map '' monomial.region ⊆ shapeConfiguration (N + 1)
  identitySet : Set (Space N)
  identity_open : IsOpen identitySet
  region_identity : monomial.region ⊆ identitySet
  base_identity : ∀ j, ∀ y ∈ identitySet,
    edgeFunctions e j (map y) = BoundedLogMonomialCombination.baseFunctions monomial j y
  extra_identity : ∀ k, ∀ y ∈ identitySet,
    RatioCutoff.radialFunction k (map y) = BoundedLogMonomialCombination.extraFunctions monomial k y

variable (e : RatioCutoffStokes.Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)

/-- The actual scalar top coefficient in the fixed Cartesian frame. -/
def errorDensity (ε : ℝ) (η : Space N) : ℝ := cutoffTerm e ε η (frame N)

/-- Its literal real-coordinate expression. -/
def realError (ε : ℝ) (x : BoxStokes.Coord (NormalCrossingStokes.Dim N)) : ℝ := errorDensity e ε (cartesian N x)

variable (a : ErrorChart e)

theorem map_configuration {x : Space N} (hx : x ∈ a.monomial.region) :
    a.map x ∈ shapeConfiguration (N + 1) := a.image_configuration ⟨x, hx, rfl⟩

include he in
/-- Exact native pulled-back determinant, including the original dχ and β. -/
theorem pullback_eq_density (ε : ℝ) {x : Space N} (hx : x ∈ a.monomial.region) :
    ((cutoffTerm e ε (a.map x)).compContinuousLinearMap (fderiv ℝ a.map x)) (frame N) =
      BoundedLogMonomialCombination.density a.monomial
        (RatioCutoff.signedCoefficient ε (a.map x)) (frame N) x :=
  cutoffTerm_pullback_eq_density e he a.monomial
    ((a.map_C1 x hx).differentiableAt (by norm_num)) (map_configuration e a hx) ε
    a.identity_open (a.region_identity hx) a.base_identity a.extra_identity (frame N)

/-- Genuine coefficient measurability follows from the actual ratio cutoff,
using continuity on configurations and the actual local chart. -/
theorem continuousOn_coefficient (ε : ℝ) (k : RatioCutoff.RadialIndex (N + 1)) :
    ContinuousOn (fun x ↦ RatioCutoff.signedCoefficient ε (a.map x) k) a.monomial.region := by
  intro x hx
  exact ((RatioCutoff.continuousAt_signedCoefficient ε k (map_configuration e a hx)).comp
    (a.map_C1 x hx).continuousAt).continuousWithinAt

/-- The actual cutoff coefficient tends to zero at every point of the chart. -/
theorem tendsto_coefficient {x : Space N} (hx : x ∈ a.monomial.region)
    (k : RatioCutoff.RadialIndex (N + 1)) :
    Tendsto (fun ε ↦ RatioCutoff.signedCoefficient ε (a.map x) k) (𝓝[>] 0) (𝓝 0) :=
  RatioCutoff.tendsto_signedCoefficient (map_configuration e a hx) k

include he in
/-- Uniform local majorant derived for the genuine error term, not supplied as input. -/
theorem local_domination : ∃ C : ℝ, 0 ≤ C ∧
    (∀ ε x, x ∈ a.monomial.region →
      ‖((cutoffTerm e ε (a.map x)).compContinuousLinearMap (fderiv ℝ a.map x)) (frame N)‖ ≤
        BoundedLogMonomialCombination.bound a.monomial C *
          NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) x) := by
  obtain ⟨C, hC, hb⟩ := RatioCutoff.exists_bound_signedCoefficient
  refine ⟨C, hC, fun ε x hx ↦ ?_⟩
  rw [pullback_eq_density e he a ε hx]
  exact BoundedLogMonomialCombination.norm_density_le a.monomial _ C hC
    (fun k ↦ by simpa only [Real.norm_eq_abs] using hb (N + 1) ε (a.map x) (map_configuration e a hx) k)
    (frame N) (CompactMonomialStokes.norm_frame_le_one N) hx

include he in
/-- Native local L1 convergence follows with all varying-coefficient hypotheses discharged. -/
theorem tendsto_local_integral_norm :
    Tendsto (fun ε ↦ ∫ x in a.monomial.region,
      ‖((cutoffTerm e ε (a.map x)).compContinuousLinearMap (fderiv ℝ a.map x)) (frame N)‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := RatioCutoff.exists_bound_signedCoefficient
  have ht := BoundedLogMonomialCombination.tendsto_integral_norm_density a.monomial
    (fun ε k x ↦ RatioCutoff.signedCoefficient ε (a.map x) k)
    (Eventually.of_forall (fun ε k ↦ (continuousOn_coefficient e a ε k).aestronglyMeasurable
      a.monomial.measurable_region)) C hC
    (Eventually.of_forall (fun ε x hx k ↦ by
      simpa only [Real.norm_eq_abs] using hb (N + 1) ε (a.map x) (map_configuration e a hx) k))
    (fun x hx k ↦ tendsto_coefficient e a hx k) (frame N) (CompactMonomialStokes.norm_frame_le_one N)
  apply ht.congr
  intro ε
  apply setIntegral_congr_fun a.monomial.measurable_region
  intro x hx
  exact congrArg norm (pullback_eq_density e he a ε hx).symm

/-- The coordinate conjugation uses the actual derivative of the chart. -/
theorem cartesian_fderiv_realChart {x : BoxStokes.Coord (NormalCrossingStokes.Dim N)}
    (hx : cartesian N x ∈ a.monomial.region) (v : BoxStokes.Coord (NormalCrossingStokes.Dim N)) :
    cartesian N (fderiv ℝ (FiniteChartPartition.realChart (cartesian N) a.map) x v) =
      fderiv ℝ a.map (cartesian N x) (cartesian N v) := by
  have hd := (cartesian N).symm.hasFDerivAt.comp x
    (((a.map_C1 _ hx).differentiableAt (by norm_num)).hasFDerivAt.comp x (cartesian N).hasFDerivAt)
  change HasFDerivAt (FiniteChartPartition.realChart (cartesian N) a.map) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

include he in
/-- The signed determinant factor is proved from the actual pulled-back form.
Taking norms below gives the absolute Jacobian required by change of variables. -/
theorem jacobian_mul_error_eq_density (ε : ℝ) {x : BoxStokes.Coord (NormalCrossingStokes.Dim N)}
    (hx : cartesian N x ∈ a.monomial.region) :
    OrientedFormChangeVariables.jacobian (FiniteChartPartition.realChart (cartesian N) a.map) x *
      errorDensity e ε (a.map (cartesian N x)) =
    BoundedLogMonomialCombination.density a.monomial
      (RatioCutoff.signedCoefficient ε (a.map (cartesian N x))) (frame N) (cartesian N x) := by
  have ht := OrientedFormChangeVariables.topForm_linear_change
    ((cutoffTerm e ε (a.map (cartesian N x))).compContinuousLinearMap (cartesian N).toContinuousLinearMap)
    (fderiv ℝ (FiniteChartPartition.realChart (cartesian N) a.map) x)
  have hv : (fun j ↦ cartesian N
      (fderiv ℝ (FiniteChartPartition.realChart (cartesian N) a.map) x (BoxStokes.standardBasis (NormalCrossingStokes.Dim N) j))) =
      fun j ↦ fderiv ℝ a.map (cartesian N x) (frame N j) := by
    funext j
    exact cartesian_fderiv_realChart e a hx _
  simp only [compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe] at ht
  change (cutoffTerm e ε (a.map (cartesian N x)))
      (fun j ↦ cartesian N (fderiv ℝ (FiniteChartPartition.realChart (cartesian N) a.map) x
        (BoxStokes.standardBasis (NormalCrossingStokes.Dim N) j))) = _ at ht
  rw [hv] at ht
  exact ht.symm.trans (pullback_eq_density e he a ε hx)

include he in
/-- On the actual configuration locus the error coefficient is continuous for
all parameters, including the harmless total values at nonpositive epsilon. -/
theorem continuousAt_errorDensity (ε : ℝ) {η : Space N}
    (hη : η ∈ shapeConfiguration (N + 1)) : ContinuousAt (errorDensity e ε) η := by
  have hχ : ContDiffAt ℝ 2 (RatioCutoff.chi ε) η := by
    apply contDiffAt_prod
    intro k hk
    have hp : ContDiff ℝ 2 RatioCutoff.psi := RatioCutoff.contDiff_psi.of_le (by exact WithTop.coe_le_coe.mpr le_top)
    exact hp.contDiffAt.comp η
      (((RatioCutoff.contDiffAt_gamma k hη).of_le (by norm_num)).div_const ε)
  have hDχ := hχ.continuousAt_fderiv (by norm_num)
  have hβ := (RatioCutoffStokes.contDiffAt_beta e he hη).continuousAt
  unfold errorDensity cutoffTerm
  simp only [alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
  apply tendsto_finsetSum
  intro j hj
  exact continuousAt_const.mul ((hDχ.clm_apply continuousAt_const).mul
    ((ContinuousAlternatingMap.apply ℝ _ ℝ (j.removeNth (frame N))).continuous.continuousAt.comp hβ))

variable {A : Type*} [Fintype A] (charts : A → ErrorChart e)
    (hcover : shapeConfiguration (N + 1) ⊆ ⋃ i, (charts i).map '' (charts i).monomial.region)

/-- Construct the genuine finite partition and the real-coordinate chart cover. -/
def realCover : LocalChartDominatedConvergence.ChartCover (NormalCrossingStokes.Dim N) A :=
  FiniteChartPartition.chartCover_via_linearEquiv (cartesian N)
    (shapeConfiguration (N + 1)) (isOpen_shapeConfiguration (N + 1))
    (fun i ↦ (charts i).map) (fun i ↦ (charts i).monomial.region)
    (fun i ↦ (charts i).monomial.measurable_region) (fun i ↦ (charts i).map_C1)
    (fun i ↦ (charts i).map_injective) (fun i ↦ (charts i).image_configuration)
    (fun i ↦ (charts i).image_open) hcover

theorem weight_measurable (i : A) : Measurable ((realCover e charts hcover).weight i) :=
  (FiniteChartPartition.chartCover_via_linearEquiv_weight_properties (cartesian N)
    (shapeConfiguration (N + 1)) (isOpen_shapeConfiguration (N + 1))
    (fun i ↦ (charts i).map) (fun i ↦ (charts i).monomial.region)
    (fun i ↦ (charts i).monomial.measurable_region) (fun i ↦ (charts i).map_C1)
    (fun i ↦ (charts i).map_injective) (fun i ↦ (charts i).image_configuration)
    (fun i ↦ (charts i).image_open) hcover i).1

theorem weight_norm_le (i : A) (x : BoxStokes.Coord (NormalCrossingStokes.Dim N)) :
    ‖(realCover e charts hcover).weight i x‖ ≤ 1 :=
  (FiniteChartPartition.chartCover_via_linearEquiv_weight_properties (cartesian N)
    (shapeConfiguration (N + 1)) (isOpen_shapeConfiguration (N + 1))
    (fun i ↦ (charts i).map) (fun i ↦ (charts i).monomial.region)
    (fun i ↦ (charts i).monomial.measurable_region) (fun i ↦ (charts i).map_C1)
    (fun i ↦ (charts i).map_injective) (fun i ↦ (charts i).image_configuration)
    (fun i ↦ (charts i).image_open) hcover i).2.2 x

include he in
/-- The actual source density contains precisely the absolute Jacobian and the
partition weight. The identity uses the derived signed determinant formula. -/
theorem sourceNorm_eq (ε : ℝ) (i : A) {x : BoxStokes.Coord (NormalCrossingStokes.Dim N)}
    (hx : x ∈ (realCover e charts hcover).source i) :
    LocalChartDominatedConvergence.sourceNorm (realCover e charts hcover) (realError e ε) i x =
      ‖(realCover e charts hcover).weight i ((realCover e charts hcover).chart i x) *
        BoundedLogMonomialCombination.density (charts i).monomial
          (RatioCutoff.signedCoefficient ε ((charts i).map (cartesian N x))) (frame N) (cartesian N x)‖ := by
  rw [← jacobian_mul_error_eq_density e he (charts i) ε hx]
  change |OrientedFormChangeVariables.jacobian
      (FiniteChartPartition.realChart (cartesian N) (charts i).map) x| *
    ‖(realCover e charts hcover).weight i ((realCover e charts hcover).chart i x) *
      realError e ε ((realCover e charts hcover).chart i x)‖ = _
  have hv : realError e ε ((realCover e charts hcover).chart i x) =
      errorDensity e ε ((charts i).map (cartesian N x)) := by
    simp only [realError, realCover, FiniteChartPartition.chartCover_via_linearEquiv,
      FiniteChartPartition.chartCover, FiniteChartPartition.realChart,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hv]
  simp only [norm_mul, Real.norm_eq_abs]
  ring

include he in
theorem measurable_sourceSigned (ε : ℝ) (i : A) :
    AEStronglyMeasurable
      (LocalChartDominatedConvergence.sourceSigned (realCover e charts hcover) (realError e ε) i)
      (volume.restrict ((realCover e charts hcover).source i)) := by
  let c := realCover e charts hcover
  have hm := c.measurable_source i
  have hφ : ContinuousOn (c.chart i) (c.source i) := fun x hx ↦ (c.chart_C1 i x hx).continuousAt.continuousWithinAt
  have hwc : AEStronglyMeasurable (fun x ↦ c.weight i (c.chart i x)) (volume.restrict (c.source i)) := by
    exact ((weight_measurable e charts hcover i).comp_aemeasurable
      (hφ.aestronglyMeasurable hm).aemeasurable).aestronglyMeasurable
  have hf : ContinuousOn (fun x ↦ realError e ε (c.chart i x)) (c.source i) := by
    intro x hx
    have hxconf : cartesian N (c.chart i x) ∈ shapeConfiguration (N + 1) :=
      c.image_domain i ⟨x, hx, rfl⟩
    exact (((continuousAt_errorDensity e he ε hxconf).comp (cartesian N).continuous.continuousAt).comp
      (c.chart_C1 i x hx).continuousAt).continuousWithinAt
  exact ((UnorientedFormIntegrability.continuousOn_jacobian (c.chart i) (c.source i)
    (c.chart_C1 i)).abs.aestronglyMeasurable hm).mul (hwc.mul (hf.aestronglyMeasurable hm))

/-- The fixed local majorant in actual real source coordinates. -/
def realMajorant (C : ℝ) (i : A) (x : BoxStokes.Coord (NormalCrossingStokes.Dim N)) : ℝ :=
  BoundedLogMonomialCombination.bound (charts i).monomial C *
    NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) (cartesian N x)

theorem integrable_realMajorant (C : ℝ) (i : A) :
    IntegrableOn (realMajorant e charts C i) ((realCover e charts hcover).source i) := by
  have h := (volume_preserving_cartesian N).integrableOn_comp_preimage
    (cartesianMeas N).measurableEmbedding
    (f := fun z ↦ BoundedLogMonomialCombination.bound (charts i).monomial C *
      NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) z)
    (s := (charts i).monomial.region)
  exact h.mpr (BoundedLogMonomialCombination.integrable_majorant (charts i).monomial C)

include he in
/-- All hypotheses of local-to-global DCT are now discharged for the actual
ratio-cutoff error. Only geometric monomial chart data remain as inputs. -/
theorem exists_localDomination :
    Nonempty (LocalChartDominatedConvergence.LocalDomination (realCover e charts hcover)
      (l := 𝓝[>] (0 : ℝ)) (realError e)) := by
  obtain ⟨C, hC, hb⟩ := RatioCutoff.exists_bound_signedCoefficient
  refine ⟨{
    majorant := realMajorant e charts C
    integrable_majorant := integrable_realMajorant e charts hcover C
    measurable := measurable_sourceSigned e he charts hcover
    dominated := ?_
    tendsto_zero := ?_ }⟩
  · intro ε i
    filter_upwards [ae_restrict_mem ((realCover e charts hcover).measurable_source i)] with x hx
    rw [sourceNorm_eq e he charts hcover ε i hx, norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (weight_norm_le e charts hcover i _)).trans
    exact BoundedLogMonomialCombination.norm_density_le (charts i).monomial _ C hC
      (fun k ↦ by
        simpa only [Real.norm_eq_abs] using
          hb (N + 1) ε ((charts i).map (cartesian N x)) (map_configuration e (charts i) hx) k)
      (frame N) (CompactMonomialStokes.norm_frame_le_one N) hx
  · intro i
    filter_upwards [ae_restrict_mem ((realCover e charts hcover).measurable_source i)] with x hx
    have ht := BoundedLogMonomialCombination.tendsto_density (charts i).monomial
      (fun ε k z ↦ RatioCutoff.signedCoefficient ε ((charts i).map z) k)
      (frame N) hx (fun k ↦ tendsto_coefficient e (charts i) hx k)
    have hw := (ht.const_mul ((realCover e charts hcover).weight i ((realCover e charts hcover).chart i x))).norm
    simpa only [sourceNorm_eq e he charts hcover _ i hx, mul_zero, norm_zero] using hw

include he in
/-- The actual original error tends to zero in L1 after assembling the finite
charts with the constructed measurable partition and native change of variables. -/
theorem tendsto_real_integral_norm_error :
    Tendsto (fun ε ↦ ∫ x in (realCover e charts hcover).domain, ‖realError e ε x‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨h⟩ := exists_localDomination e he charts hcover
  exact LocalChartDominatedConvergence.tendsto_integral_norm _ _ h

include he charts hcover in
/-- Original complex configuration coordinates, with their genuine volume. -/
theorem tendsto_integral_norm_error :
    Tendsto (fun ε ↦ ∫ η in shapeConfiguration (N + 1), ‖errorDensity e ε η‖)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := tendsto_real_integral_norm_error e he charts hcover
  have heq (ε : ℝ) :
      (∫ x in (realCover e charts hcover).domain, ‖realError e ε x‖) =
        ∫ η in shapeConfiguration (N + 1), ‖errorDensity e ε η‖ :=
    (volume_preserving_cartesian N).setIntegral_preimage_emb (cartesianMeas N).measurableEmbedding
      (fun η : Space N ↦ ‖errorDensity e ε η‖) (shapeConfiguration (N + 1))
  simpa only [heq] using ht

include he charts hcover in
theorem tendsto_integral_error :
    Tendsto (fun ε ↦ ∫ η in shapeConfiguration (N + 1), errorDensity e ε η)
      (𝓝[>] 0) (𝓝 0) :=
  squeeze_zero_norm (fun ε ↦ norm_integral_le_integral_norm _)
    (tendsto_integral_norm_error e he charts hcover)

/-- For positive epsilon the actual error vanishes off the original configuration locus. -/
theorem errorDensity_zero_outside {ε : ℝ} (hε : 0 < ε) {η : Space N}
    (hη : η ∉ shapeConfiguration (N + 1)) : errorDensity e ε η = 0 := by
  have hs : η ∉ tsupport (RatioCutoff.chi ε) :=
    fun h ↦ hη (RatioCutoff.tsupport_chi_subset hε h)
  simp only [errorDensity, cutoffTerm, fderiv_of_notMem_tsupport ℝ hs,
    ContinuousLinearMap.zero_smulRight, RatioCutoffStokes.alternatizeUncurryFinCLM_zero]
  rfl

theorem integral_norm_error_eq_configuration {ε : ℝ} (hε : 0 < ε) :
    (∫ η : Space N, ‖errorDensity e ε η‖) =
      ∫ η in shapeConfiguration (N + 1), ‖errorDensity e ε η‖ := by
  have hh := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (μ := (volume : Measure (Space N))) (f := fun η ↦ ‖errorDensity e ε η‖)
    MeasurableSet.univ (subset_univ (shapeConfiguration (N + 1)))
    (fun η hη ↦ by rw [errorDensity_zero_outside e hε hη.2, norm_zero])
  simpa only [setIntegral_univ] using hh

include he charts hcover in
/-- Whole ambient-space L1 convergence, as used by finite-cutoff Stokes. -/
theorem tendsto_integral_norm_error_whole :
    Tendsto (fun ε ↦ ∫ η : Space N, ‖errorDensity e ε η‖) (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_integral_norm_error e he charts hcover).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_norm_error_eq_configuration e hε).symm

/-- Any fixed top-degree frame differs by its actual basis determinant. -/
theorem cutoffTerm_apply_eq (ε : ℝ) (η : Space N)
    (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    cutoffTerm e ε η v = (cartesianBasis N).det v * errorDensity e ε η := by
  have h := congrArg (fun A : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→ₗ[ℝ] ℝ ↦ A v)
    ((cutoffTerm e ε η).toAlternatingMap.eq_smul_basis_det (cartesianBasis N))
  simp only [AlternatingMap.smul_apply, smul_eq_mul, cartesianBasis_eq_frame] at h
  change cutoffTerm e ε η v = errorDensity e ε η * (cartesianBasis N).det v at h
  exact h.trans (mul_comm _ _)

include he charts hcover in
/-- Actual L1 convergence for the top frame used by the original fiber forms. -/
theorem tendsto_integral_norm_cutoffTerm
    (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Tendsto (fun ε ↦ ∫ η : Space N, ‖cutoffTerm e ε η v‖) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_integral_norm_error_whole e he charts hcover).const_mul ‖(cartesianBasis N).det v‖
  have heq (ε : ℝ) : (∫ η : Space N, ‖cutoffTerm e ε η v‖) =
      ‖(cartesianBasis N).det v‖ * ∫ η : Space N, ‖errorDensity e ε η‖ := by
    simp only [cutoffTerm_apply_eq, norm_mul, integral_const_mul]
  simpa only [← heq, mul_zero] using ht

include he charts hcover in
/-- The actual signed cutoff error in finite Stokes tends to zero. -/
theorem tendsto_integral_cutoffTerm
    (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Tendsto (fun ε ↦ ∫ η : Space N, cutoffTerm e ε η v) (𝓝[>] 0) (𝓝 0) :=
  squeeze_zero_norm (fun _ ↦ norm_integral_le_integral_norm _)
    (tendsto_integral_norm_cutoffTerm e he charts hcover v)

end EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffGlobalDomination
