import EnvelopingIsomorphism.Deformation.Kontsevich.LogPoleEstimates
import Mathlib.MeasureTheory.Integral.Pi

/-!
Finite products of genuine logarithmic-pole densities on complex polydiscs.
The proofs use Mathlib's finite product measures and finite-dimensional Fubini
identities. No compactification chart or Stokes assertion is an input.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogPole

open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι]

/-- A bounded product of complex discs, with a possibly different radius in each coordinate. -/
def polydisc (ε : ι → ℝ) : Set (ι → ℂ) :=
  Set.univ.pi (fun i => ball (0 : ℂ) (ε i))

/-- The actual product of logarithmic-pole densities. -/
def productDensity (a : ι → ℕ) (z : ι → ℂ) : ℝ :=
  ∏ i, density (a i) (z i)

theorem measurableSet_polydisc (ε : ι → ℝ) : MeasurableSet (polydisc ε) :=
  MeasurableSet.univ_pi (fun _ => isOpen_ball.measurableSet)

theorem productDensity_nonneg (a : ι → ℕ) (z : ι → ℂ) : 0 ≤ productDensity a z :=
  Finset.prod_nonneg (fun i _ => density_nonneg (a i) (z i))

@[fun_prop] theorem measurable_productDensity (a : ι → ℕ) : Measurable (productDensity a) := by
  unfold productDensity
  fun_prop

/-- The restricted Lebesgue measure of the polydisc is the actual product of
its restricted one-coordinate measures. -/
theorem volume_restrict_polydisc (ε : ι → ℝ) :
    (volume : Measure (ι → ℂ)).restrict (polydisc ε) =
      Measure.pi (fun i => (volume : Measure ℂ).restrict (ball 0 (ε i))) := by
  rw [volume_pi, polydisc, Measure.restrict_pi_pi]

/-- Products of one-coordinate logarithmic-pole densities are integrable on
every bounded complex polydisc. The number of coordinates may be zero. -/
theorem integrableOn_productDensity_polydisc (a : ι → ℕ) (ε : ι → ℝ) :
    IntegrableOn (productDensity a) (polydisc ε) volume := by
  change Integrable (fun z : ι → ℂ => ∏ i, density (a i) (z i))
    ((volume : Measure (ι → ℂ)).restrict (polydisc ε))
  rw [volume_restrict_polydisc]
  exact Integrable.fintype_prod (fun i => integrableOn_density_ball (a i) (ε i))

/-- Genuine finite-product Fubini identity for the logarithmic-pole density. -/
theorem integral_productDensity_polydisc (a : ι → ℕ) (ε : ι → ℝ) :
    (∫ z : ι → ℂ in polydisc ε, productDensity a z) =
      ∏ i, ∫ z : ℂ in ball 0 (ε i), density (a i) z := by
  rw [volume_restrict_polydisc]
  exact integral_fintype_prod_eq_prod (fun i => density (a i))

/-- The nonnegative product has a finite Lebesgue integral in the extended reals. -/
theorem lintegral_productDensity_polydisc_lt_top (a : ι → ℕ) (ε : ι → ℝ) :
    (∫⁻ z : ι → ℂ in polydisc ε, ENNReal.ofReal (productDensity a z)) < ⊤ :=
  (integrableOn_productDensity_polydisc a ε).setLIntegral_lt_top

theorem integral_productDensity_polydisc_nonneg (a : ι → ℕ) (ε : ι → ℝ) :
    0 ≤ ∫ z : ι → ℂ in polydisc ε, productDensity a z :=
  integral_nonneg (productDensity_nonneg a)

section Domination

variable {E : Type*} [NormedAddCommGroup E]

/-- Any a.e. measurable coefficient dominated by a constant times the product
density is integrable, in an arbitrary normed additive target. -/
theorem integrableOn_of_norm_le_productDensity (a : ι → ℕ) (ε : ι → ℝ)
    (f : (ι → ℂ) → E) (C : ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (ι → ℂ)).restrict (polydisc ε)))
    (hbound : ∀ᵐ z ∂((volume : Measure (ι → ℂ)).restrict (polydisc ε)),
      ‖f z‖ ≤ C * productDensity a z) :
    IntegrableOn f (polydisc ε) volume :=
  ((integrableOn_productDensity_polydisc a ε).const_mul C).mono' hf hbound

/-- A pointwise domination estimate only needs to hold on the polydisc itself. -/
theorem integrableOn_of_norm_le_productDensity_on (a : ι → ℕ) (ε : ι → ℝ)
    (f : (ι → ℂ) → E) (C : ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (ι → ℂ)).restrict (polydisc ε)))
    (hbound : ∀ z ∈ polydisc ε, ‖f z‖ ≤ C * productDensity a z) :
    IntegrableOn f (polydisc ε) volume := by
  apply integrableOn_of_norm_le_productDensity a ε f C hf
  filter_upwards [ae_restrict_mem (measurableSet_polydisc ε)] with z hz
  exact hbound z hz

end Domination

/-- A bounded measurable scalar multiplier preserves integrability of the pole product. -/
theorem integrableOn_bounded_mul_productDensity (a : ι → ℕ) (ε : ι → ℝ)
    (c : (ι → ℂ) → ℝ) (C : ℝ)
    (hc : AEStronglyMeasurable c ((volume : Measure (ι → ℂ)).restrict (polydisc ε)))
    (hbound : ∀ᵐ z ∂((volume : Measure (ι → ℂ)).restrict (polydisc ε)), |c z| ≤ C) :
    IntegrableOn (fun z => c z * productDensity a z) (polydisc ε) volume := by
  apply integrableOn_of_norm_le_productDensity a ε _ C
    (hc.mul (measurable_productDensity a).aestronglyMeasurable.restrict)
  filter_upwards [hbound] with z hz
  rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (productDensity_nonneg a z)]
  exact mul_le_mul_of_nonneg_right hz (productDensity_nonneg a z)

/-- The usual radial boundary factor annihilates the fixed, genuinely finite
integral in all remaining normal coordinates. -/
theorem tendsto_radius_log_mul_product_integral (b : ℕ) (a : ι → ℕ) (ε : ι → ℝ) :
    Tendsto (fun r : ℝ => r * |Real.log r| ^ b *
      (∫ z : ι → ℂ in polydisc ε, productDensity a z)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [zero_mul] using
    (tendsto_radius_mul_abs_log_pow b).mul_const
      (∫ z : ι → ℂ in polydisc ε, productDensity a z)

/-- The same statement as a limit of actual integrals over the fixed remaining polydisc. -/
theorem tendsto_integral_radius_log_mul_productDensity (b : ℕ) (a : ι → ℕ) (ε : ι → ℝ) :
    Tendsto (fun r : ℝ => ∫ z : ι → ℂ in polydisc ε,
      (r * |Real.log r| ^ b) * productDensity a z) (𝓝[>] 0) (𝓝 0) := by
  simp_rw [integral_const_mul]
  exact tendsto_radius_log_mul_product_integral b a ε

end EnvelopingIsomorphism.Deformation.Kontsevich.LogPole
