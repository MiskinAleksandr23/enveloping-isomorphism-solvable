import EnvelopingIsomorphism.Deformation.Kontsevich.CutoffDifferential
import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialForms

/-! Actual chart pullbacks of the distance-ratio cutoff differential. The only
normal-form hypotheses are equalities of complex-valued functions on an open set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
open InteriorFiberAngleSplit Set Filter
open scoped Topology BigOperators

 theorem productRadialCoefficient_eventually_zero {N : ℕ} {η : Shape N}
    (hη : η ∈ shapeConfiguration N) (t : Triple N) :
    (fun ε : ℝ ↦ productRadialCoefficient ε η t) =ᶠ[𝓝[>] 0] (fun _ ↦ 0) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < gamma t η / 2 :=
    (gt_mem_nhds (half_pos (gamma_pos t hη))).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, self_mem_nhdsWithin] with ε hε hε0
  have hs : 2 < gamma t η / ε := (lt_div_iff₀ hε0).mpr (by linarith)
  simp [productRadialCoefficient, radialCutoffCoefficient, deriv_psi_zero_of_gt hs]

theorem signedCoefficient_eventually_zero {N : ℕ} {η : Shape N}
    (hη : η ∈ shapeConfiguration N) (k : RadialIndex N) :
    (fun ε : ℝ ↦ signedCoefficient ε η k) =ᶠ[𝓝[>] 0] (fun _ ↦ 0) := by
  cases k with
  | inl t => exact productRadialCoefficient_eventually_zero hη t
  | inr t =>
    filter_upwards [productRadialCoefficient_eventually_zero hη t] with ε hε
    simp [signedCoefficient, hε]

theorem tendsto_signedCoefficient {N : ℕ} {η : Shape N}
    (hη : η ∈ shapeConfiguration N) (k : RadialIndex N) :
    Tendsto (fun ε : ℝ ↦ signedCoefficient ε η k) (𝓝[>] 0) (𝓝 0) :=
  tendsto_const_nhds.congr' (signedCoefficient_eventually_zero hη k).symm

theorem differentiableAt_radialFunction {N : ℕ} (k : RadialIndex N) (η : Shape N) :
    DifferentiableAt ℝ (radialFunction k) η := by
  cases k with
  | inl t => exact (hasFDerivAt_shapeDifference _ _ η).differentiableAt
  | inr t => exact (hasFDerivAt_shapeDifference _ _ η).differentiableAt

theorem radialFunction_ne_zero {N : ℕ} (k : RadialIndex N) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) : radialFunction k η ≠ 0 := by
  cases k with
  | inl t => exact shapeDifference_ne_zero hη t.property.1
  | inr t => exact shapeDifference_ne_zero hη t.property.2

/-- Coefficients need only continuity, obtained on the genuine configuration locus. -/
theorem continuousAt_productRadialCoefficient {N : ℕ} (ε : ℝ) (t : Triple N)
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    ContinuousAt (fun ζ ↦ productRadialCoefficient ε ζ t) η := by
  have hg (v : Triple N) := (contDiffAt_gamma v hη).continuousAt
  have hs (v : Triple N) := (hg v).div_const ε
  have hp : ContinuousAt (fun ζ ↦ ∏ v ∈ Finset.univ.erase t, psi (gamma v ζ / ε)) η :=
    tendsto_finsetProd _ (fun v _ ↦ contDiff_psi.continuous.continuousAt.comp (hs v))
  have hd := (contDiff_psi.continuous_deriv (by simp)).continuousAt.comp (hs t)
  exact hp.mul (((hs t).mul hd).mul (continuousAt_const.sub (hg t)))

theorem continuousAt_signedCoefficient {N : ℕ} (ε : ℝ) (k : RadialIndex N)
    {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    ContinuousAt (fun ζ ↦ signedCoefficient ε ζ k) η := by
  cases k with
  | inl t => exact continuousAt_productRadialCoefficient ε t hη
  | inr t => exact (continuousAt_productRadialCoefficient ε t hη).neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine chain rule, before invoking any monomial representation. -/
theorem fderiv_chi_comp_eq_sum_radial {N : ℕ} {F : E → Shape N} {x : E}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration N) (ε : ℝ) :
    fderiv ℝ (fun y ↦ chi ε (F y)) x =
      ∑ k : RadialIndex N, signedCoefficient ε (F x) k •
        ((radialLinearCoefficient (radialFunction k (F x))⁻¹).comp
          (fderiv ℝ (fun y ↦ radialFunction k (F y)) x)) := by
  change fderiv ℝ (chi ε ∘ F) x =
    ∑ k : RadialIndex N, signedCoefficient ε (F x) k •
      ((radialLinearCoefficient (radialFunction k (F x))⁻¹).comp
        (fderiv ℝ (radialFunction k ∘ F) x))
  rw [fderiv_comp x (hasFDerivAt_chi_radial ε hx).differentiableAt hF,
    fderiv_chi_eq_sum_radial ε hx]
  simp only [fderiv_comp x (differentiableAt_radialFunction _ _) hF]
  ext v
  simp

/-- Native radial forms obey function identities; derivative identities are derived. -/
theorem radial_comp_eq_monomial {N : ℕ} {F : E → Shape N} {x : E}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration N)
    (k : RadialIndex N) {J : Type*} [Fintype J]
    (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    (hu : DifferentiableAt ℝ u x) (hz : ∀ j, DifferentiableAt ℝ (z j) x)
    (hu0 : u x ≠ 0) (hz0 : ∀ j, z j x ≠ 0)
    (hid : (fun y ↦ radialFunction k (F y)) =ᶠ[𝓝 x] LogMonomial.function a u z) :
    (radialLinearCoefficient (radialFunction k (F x))⁻¹).comp
        (fderiv ℝ (fun y ↦ radialFunction k (F y)) x) =
      LogMonomial.radialDerivative a u z x := by
  have hlog := hasFDerivAt_log_norm_comp
    ((differentiableAt_radialFunction k (F x)).comp x hF).hasFDerivAt
    (radialFunction_ne_zero k hx)
  have hm := LogMonomial.hasFDerivAt_log_norm_function a u z hu hz hu0 hz0
  have he : (fun y ↦ Real.log ‖radialFunction k (F y)‖) =ᶠ[𝓝 x]
      (fun y ↦ Real.log ‖LogMonomial.function a u z y‖) :=
    hid.fun_comp (fun w : ℂ ↦ Real.log ‖w‖)
  exact hlog.unique (hm.congr_of_eventuallyEq he)

/-- Monomial data on an actual open chart determines the cutoff pullback. -/
theorem fderiv_chi_comp_eq_monomial {N : ℕ} {F : E → Shape N} {x : E}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration N) (ε : ℝ)
    {J : Type*} [Fintype J] (a : RadialIndex N → J → ℤ)
    (u : RadialIndex N → E → ℂ) (z : J → E → ℂ)
    (hu : ∀ k, DifferentiableAt ℝ (u k) x) (hz : ∀ j, DifferentiableAt ℝ (z j) x)
    (hu0 : ∀ k, u k x ≠ 0) (hz0 : ∀ j, z j x ≠ 0)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hid : ∀ k, ∀ y ∈ U, radialFunction k (F y) = LogMonomial.function (a k) (u k) z y) :
    fderiv ℝ (fun y ↦ chi ε (F y)) x =
      ∑ k : RadialIndex N, signedCoefficient ε (F x) k •
        LogMonomial.radialDerivative (a k) (u k) z x := by
  rw [fderiv_chi_comp_eq_sum_radial hF hx ε]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply radial_comp_eq_monomial hF hx k (a k) (u k) z (hu k) hz (hu0 k) hz0
  filter_upwards [hU.mem_nhds hxU] with y hy
  exact hid k y hy

/-- Direct covector expression for the augmented-determinant interface. -/
theorem fderiv_chi_comp_eq_monomial_covectors {N : ℕ} {F : E → Shape N} {x : E}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration N) (ε : ℝ)
    {J : Type*} [Fintype J] (a : RadialIndex N → J → ℤ)
    (u : RadialIndex N → E → ℂ) (z : J → E → ℂ)
    (hu : ∀ k, DifferentiableAt ℝ (u k) x) (hz : ∀ j, DifferentiableAt ℝ (z j) x)
    (hu0 : ∀ k, u k x ≠ 0) (hz0 : ∀ j, z j x ≠ 0)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hid : ∀ k, ∀ y ∈ U, radialFunction k (F y) = LogMonomial.function (a k) (u k) z y) :
    fderiv ℝ (fun y ↦ chi ε (F y)) x =
      ∑ k : RadialIndex N, signedCoefficient ε (F x) k •
        ((radialLinearCoefficient (LogMonomial.function (a k) (u k) z x)⁻¹).comp
          (fderiv ℝ (LogMonomial.function (a k) (u k) z) x)) := by
  rw [fderiv_chi_comp_eq_monomial hF hx ε a u z hu hz hu0 hz0 hU hxU hid]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact (LogMonomial.hasFDerivAt_log_norm_function (a k) (u k) z (hu k) hz (hu0 k) hz0).unique
    (hasFDerivAt_log_norm_comp
      (LogMonomial.differentiableAt_function (a k) (u k) z (hu k) hz hz0).hasFDerivAt
      (LogMonomial.value_ne_zero (a k) (hu0 k) hz0))

/-- The same formula in Mathlib's native alternating one-form representation. -/
theorem form_chi_comp_eq_monomial {N : ℕ} {F : E → Shape N} {x : E}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration N) (ε : ℝ)
    {J : Type*} [Fintype J] (a : RadialIndex N → J → ℤ)
    (u : RadialIndex N → E → ℂ) (z : J → E → ℂ)
    (hu : ∀ k, DifferentiableAt ℝ (u k) x) (hz : ∀ j, DifferentiableAt ℝ (z j) x)
    (hu0 : ∀ k, u k x ≠ 0) (hz0 : ∀ j, z j x ≠ 0)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hid : ∀ k, ∀ y ∈ U, radialFunction k (F y) = LogMonomial.function (a k) (u k) z y) :
    ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (fderiv ℝ (fun y ↦ chi ε (F y)) x) =
      ∑ k : RadialIndex N, signedCoefficient ε (F x) k •
        (logRadiusForm (LogMonomial.function (a k) (u k) z x)).compContinuousLinearMap
          (fderiv ℝ (LogMonomial.function (a k) (u k) z) x) := by
  rw [fderiv_chi_comp_eq_monomial hF hx ε a u z hu hz hu0 hz0 hU hxU hid]
  simp only [LogMonomial.radial_pullback _ _ _ (hu _) hz (hu0 _) hz0]
  ext v
  simp

end EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
