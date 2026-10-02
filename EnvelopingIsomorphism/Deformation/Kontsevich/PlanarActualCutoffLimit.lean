import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCutoffLimit
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularPrimitive

/-! The actual ratio-cutoff Stokes identity on the planar configuration domain,
and its limiting consequence. Global L¹ and the actual error integral limit
remain explicit analytic inputs. All finite-cutoff identities are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarActualCutoffLimit

open InteriorFiberAngleSplit NormalCrossingStokes RatioCutoffStokes
open Set MeasureTheory Filter ContinuousAlternatingMap
open scoped Topology

abbrev body {N : ℕ} (e : RatioCutoffStokes.Edges N) (η : Space N) : ℝ :=
  extDeriv (beta e) η (actualFrame N)

abbrev error {N : ℕ} (e : RatioCutoffStokes.Edges N) (ε : ℝ) (η : Space N) : ℝ :=
  cutoffTerm e ε η (actualFrame N)

theorem chi_zero_off_configuration {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : η ∉ shapeConfiguration N) : RatioCutoff.chi ε η = 0 :=
  (RatioCutoff.chi_eventually_zero_of_not_configuration hε hη).eq_of_nhds

theorem fderiv_chi_zero_off_configuration {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : η ∉ shapeConfiguration N) : fderiv ℝ (RatioCutoff.chi ε) η = 0 := by
  rw [(RatioCutoff.chi_eventually_zero_of_not_configuration hε hη).fderiv_eq]
  exact fderiv_const_apply 0

theorem error_zero_off_configuration {N : ℕ} (e : RatioCutoffStokes.Edges N)
    {ε : ℝ} (hε : 0 < ε) {η : Space N} (hη : η ∉ shapeConfiguration (N + 1)) :
    error e ε η = 0 := by
  simp only [error, cutoffTerm, fderiv_chi_zero_off_configuration hε hη,
    ContinuousLinearMap.zero_smulRight, alternatizeUncurryFinCLM_zero]
  rfl

theorem integral_cutoff_body_eq_whole {N : ℕ} (e : RatioCutoffStokes.Edges N)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ η in shapeConfiguration (N + 1), RatioCutoff.chi ε η * body e η) =
      ∫ η, RatioCutoff.chi ε η * body e η := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro η hη
  rw [chi_zero_off_configuration hε hη, zero_mul]

theorem integral_error_eq_whole {N : ℕ} (e : RatioCutoffStokes.Edges N)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ η in shapeConfiguration (N + 1), error e ε η) = ∫ η, error e ε η :=
  setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hη ↦ error_zero_off_configuration e hε hη)

/-- The actual compact Stokes identity restricted to the normalized collision-free configurations. -/
theorem actual_cutoff_identity {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) {ε : ℝ} (hε : 0 < ε) :
    (∫ η in shapeConfiguration (N + 1), RatioCutoff.chi ε η * body e η) =
      -(∫ η in shapeConfiguration (N + 1), error e ε η) := by
  rw [integral_cutoff_body_eq_whole e hε, integral_error_eq_whole e hε]
  exact (actual_finite_cutoff_stokes e he hε).2.2.2

/-- The finite-cutoff terms are integrable on the actual domain, with no integrability premises. -/
theorem integrableOn_cutoff_terms {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun η ↦ RatioCutoff.chi ε η * body e η) (shapeConfiguration (N + 1)) ∧
    IntegrableOn (error e ε) (shapeConfiguration (N + 1)) :=
  ⟨(actual_finite_cutoff_stokes e he hε).1.integrableOn,
    (actual_finite_cutoff_stokes e he hε).2.1.integrableOn⟩

/-- Every fixed configuration eventually lies outside the differential-cutoff region. -/
theorem error_eventually_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    {η : Space N} (hη : η ∈ shapeConfiguration (N + 1)) :
    (fun ε : ℝ ↦ error e ε η) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ ↦ 0) := by
  filter_upwards [RatioCutoff.fderiv_chi_eventually_zero hη] with ε hε
  simp only [error, cutoffTerm, hε, ContinuousLinearMap.zero_smulRight,
    alternatizeUncurryFinCLM_zero]
  rfl

theorem tendsto_error_pointwise {N : ℕ} (e : RatioCutoffStokes.Edges N)
    {η : Space N} (hη : η ∈ shapeConfiguration (N + 1)) :
    Tendsto (fun ε : ℝ ↦ error e ε η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_const_nhds.congr' (error_eventually_zero e hη).symm

/-- Vanishing follows from actual global L¹ and actual error convergence.
The finite-cutoff Stokes premise is discharged by the constructed ratio cutoff. -/
theorem integral_body_eq_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (hL1 : IntegrableOn (body e) (shapeConfiguration (N + 1)))
    (herror : Tendsto (fun ε : ℝ ↦ ∫ η in shapeConfiguration (N + 1), error e ε η)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ η in shapeConfiguration (N + 1), extDeriv (beta e) η (actualFrame N)) = 0 :=
  PlanarCutoffLimit.integral_eq_zero_of_cutoff_identity (body e) hL1 (error e) herror
    (fun _ hε ↦ actual_cutoff_identity e he hε)

/-- Equivalent producer when the error limit is supplied with ambient whole-space integrals. -/
theorem integral_body_eq_zero_of_whole_error {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (hL1 : IntegrableOn (body e) (shapeConfiguration (N + 1)))
    (herror : Tendsto (fun ε : ℝ ↦ ∫ η, error e ε η) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ η in shapeConfiguration (N + 1), extDeriv (beta e) η (actualFrame N)) = 0 := by
  apply integral_body_eq_zero e he hL1
  apply herror.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_error_eq_whole e hε).symm

/-- The derivative body is precisely the actual shape angular density on the configuration domain. -/
theorem body_eq_shapeDensity {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) {η : Space N}
    (hη : η ∈ shapeConfiguration (N + 1)) : body e η = shapeDensity (angularEdges e) η :=
  extDeriv_beta_actualFrame_eq_shapeDensity e he hη

/-- Actual angular-density vanishing, with precisely the two remaining analytic inputs exposed. -/
theorem integral_shapeDensity_eq_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (hL1 : IntegrableOn (shapeDensity (angularEdges e)) (shapeConfiguration (N + 1)))
    (herror : Tendsto (fun ε : ℝ ↦ ∫ η in shapeConfiguration (N + 1), error e ε η)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ η in shapeConfiguration (N + 1), shapeDensity (angularEdges e) η) = 0 := by
  have hbody : IntegrableOn (body e) (shapeConfiguration (N + 1)) :=
    hL1.congr_fun (fun _ hη ↦ (body_eq_shapeDensity e he hη).symm)
      (isOpen_shapeConfiguration (N + 1)).measurableSet
  rw [← setIntegral_congr_fun (isOpen_shapeConfiguration (N + 1)).measurableSet
    (fun _ hη ↦ body_eq_shapeDensity e he hη)]
  exact integral_body_eq_zero e he hbody herror

/-- The original angular fiber vanishes after the already-proved positive rotation extraction. -/
theorem integral_rotatedFiberDensity_eq_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (hL1 : IntegrableOn (shapeDensity (angularEdges e)) (shapeConfiguration (N + 1)))
    (herror : Tendsto (fun ε : ℝ ↦ ∫ η in shapeConfiguration (N + 1), error e ε η)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    IntegrableOn (fiberDensity (angularEdges e)) (integrationRegion (N + 1)) ∧
    (∫ x in integrationRegion (N + 1), fiberDensity (angularEdges e) x) = 0 := by
  refine ⟨(integrableOn_fiberDensity_iff (angularEdges e)).mpr hL1, ?_⟩
  rw [integral_fiberDensity_eq, integral_shapeDensity_eq_zero e he hL1 herror, mul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarActualCutoffLimit
