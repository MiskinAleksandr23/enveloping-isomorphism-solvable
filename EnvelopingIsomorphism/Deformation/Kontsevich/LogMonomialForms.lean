import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadiusForm
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
The actual logarithmic radial differential of a monomial times a nonvanishing
unit. Integer exponents include poles at infinity. Every formula is proved on
the complement of the coordinate zero loci.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open Filter
open scoped Topology BigOperators

variable {J : Type*} [Fintype J]

def value (a : J → ℤ) (u : ℂ) (z : J → ℂ) : ℂ := u * ∏ ν, z ν ^ a ν

theorem value_ne_zero (a : J → ℤ) {u : ℂ} {z : J → ℂ}
    (hu : u ≠ 0) (hz : ∀ ν, z ν ≠ 0) : value a u z ≠ 0 :=
  mul_ne_zero hu (Finset.prod_ne_zero_iff.mpr fun ν _ => zpow_ne_zero _ (hz ν))

theorem log_norm_value (a : J → ℤ) {u : ℂ} {z : J → ℂ}
    (hu : u ≠ 0) (hz : ∀ ν, z ν ≠ 0) :
    Real.log ‖value a u z‖ = Real.log ‖u‖ + ∑ ν, (a ν : ℝ) * Real.log ‖z ν‖ := by
  rw [value, norm_mul, Complex.norm_prod,
    Real.log_mul (norm_ne_zero_iff.mpr hu)
      (Finset.prod_ne_zero_iff.mpr fun ν _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz ν))),
    Real.log_prod (fun ν _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz ν)))]
  simp only [Complex.norm_zpow, Real.log_zpow]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def function (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ) (x : E) : ℂ :=
  value a (u x) (fun ν => z ν x)

def radialDerivative (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ) (x : E) : E →L[ℝ] ℝ :=
  (radialLinearCoefficient (u x)⁻¹).comp (fderiv ℝ u x) +
    ∑ ν, (a ν : ℝ) • (radialLinearCoefficient (z ν x)⁻¹).comp (fderiv ℝ (z ν) x)

omit [NormedSpace ℝ E] in
theorem eventually_log_norm_function (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    {x : E} (hu : ContinuousAt u x) (hz : ∀ ν, ContinuousAt (z ν) x)
    (hu0 : u x ≠ 0) (hz0 : ∀ ν, z ν x ≠ 0) :
    (fun y => Real.log ‖function a u z y‖) =ᶠ[𝓝 x]
      (fun y => Real.log ‖u y‖ + ∑ ν, (a ν : ℝ) * Real.log ‖z ν y‖) := by
  filter_upwards [hu.eventually_ne hu0,
    eventually_all.mpr (fun ν => (hz ν).eventually_ne (hz0 ν))] with y huy hzy
  exact log_norm_value a huy hzy

theorem hasFDerivAt_log_norm_function (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    {x : E} (hu : DifferentiableAt ℝ u x) (hz : ∀ ν, DifferentiableAt ℝ (z ν) x)
    (hu0 : u x ≠ 0) (hz0 : ∀ ν, z ν x ≠ 0) :
    HasFDerivAt (fun y => Real.log ‖function a u z y‖) (radialDerivative a u z x) x := by
  have hunit := hasFDerivAt_log_norm_comp hu.hasFDerivAt hu0
  have hcoordinate := fun ν =>
    (hasFDerivAt_log_norm_comp (hz ν).hasFDerivAt (hz0 ν)).const_smul (a ν : ℝ)
  have hsum := hunit.add (HasFDerivAt.fun_sum (u := Finset.univ) fun ν _ => hcoordinate ν)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [eventually_log_norm_function a u z hu.continuousAt
    (fun ν => (hz ν).continuousAt) hu0 hz0] with y hy
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hy

theorem differentiableAt_function (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    {x : E} (hu : DifferentiableAt ℝ u x) (hz : ∀ ν, DifferentiableAt ℝ (z ν) x)
    (hz0 : ∀ ν, z ν x ≠ 0) : DifferentiableAt ℝ (function a u z) x := by
  classical
  have hpow (ν : J) : DifferentiableAt ℝ (fun y => z ν y ^ a ν) x :=
    ((differentiableAt_zpow.mpr (Or.inl (hz0 ν))).restrictScalars ℝ).comp x (hz ν)
  have hp (s : Finset J) : DifferentiableAt ℝ (fun y => ∏ ν ∈ s, z ν y ^ a ν) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiableAt_const (c := (1 : ℂ)))
    | @insert ν s hν ih =>
      simp only [Finset.prod_insert hν]
      exact (hpow ν).mul ih
  exact hu.mul (hp Finset.univ)

/-- Genuine pullback of the radial form, with all integer valuations visible. -/
theorem radial_pullback (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    {x : E} (hu : DifferentiableAt ℝ u x) (hz : ∀ ν, DifferentiableAt ℝ (z ν) x)
    (hu0 : u x ≠ 0) (hz0 : ∀ ν, z ν x ≠ 0) :
    (logRadiusForm (function a u z x)).compContinuousLinearMap
        (fderiv ℝ (function a u z) x) =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (radialDerivative a u z x) := by
  rw [logRadiusForm_pullback (differentiableAt_function a u z hu hz hz0).hasFDerivAt
      (value_ne_zero a hu0 hz0), (hasFDerivAt_log_norm_function a u z hu hz hu0 hz0).fderiv]

theorem radial_pullback_apply (a : J → ℤ) (u : E → ℂ) (z : J → E → ℂ)
    {x : E} (hu : DifferentiableAt ℝ u x) (hz : ∀ ν, DifferentiableAt ℝ (z ν) x)
    (hu0 : u x ≠ 0) (hz0 : ∀ ν, z ν x ≠ 0) (v : Fin 1 → E) :
    ((logRadiusForm (function a u z x)).compContinuousLinearMap
      (fderiv ℝ (function a u z) x)) v =
      (fderiv ℝ u x (v 0) / u x).re +
        ∑ ν, (a ν : ℝ) * (fderiv ℝ (z ν) x (v 0) / z ν x).re := by
  rw [radial_pullback a u z hu hz hu0 hz0]
  simp [radialDerivative, div_eq_inv_mul]

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
