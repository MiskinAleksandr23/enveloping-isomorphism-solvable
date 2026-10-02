import EnvelopingIsomorphism.Deformation.Kontsevich.LogPoleProducts

/-! A genuine L¹ simple-pole/logarithmic majorant on finite punctured complex
polydiscs. All measures are the native real two-dimensional volume in each complex coordinate.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossing

open MeasureTheory Set Filter Metric
open scoped BigOperators Topology

/-- The actual punctured complex disc. -/
def puncturedDisc (ε : ℝ) : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < ε}

theorem measurableSet_puncturedDisc (ε : ℝ) : MeasurableSet (puncturedDisc ε) := by
  exact ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet

/-- The logarithmic polynomial divided by one radial factor. -/
def logPolynomialDensity (a : ℕ) (z : ℂ) : ℝ := (1 + |Real.log ‖z‖|) ^ a / ‖z‖

/-- The requested single-coordinate factor, with its harmless total value at zero. -/
def factor (a : ℕ) (z : ℂ) : ℝ :=
  max 1 (1 / ‖z‖) * (1 + |Real.log ‖z‖|) ^ a

theorem factor_nonneg (a : ℕ) (z : ℂ) : 0 ≤ factor a z := by
  exact mul_nonneg (zero_le_one.trans (le_max_left _ _))
    (pow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _)

@[fun_prop] theorem measurable_factor (a : ℕ) : Measurable (factor a) := by
  have hl : Measurable (fun z : ℂ ↦ Real.log ‖z‖) := Real.measurable_log.comp measurable_norm
  have h1 : Measurable (fun _ : ℂ ↦ (1 : ℝ)) := measurable_const
  change Measurable (fun z : ℂ ↦ max 1 (1 / ‖z‖) * (1 + |Real.log ‖z‖|) ^ a)
  convert
    (h1.max (h1.div (measurable_norm : Measurable (norm : ℂ → ℝ)))).mul
      ((h1.add hl.norm).pow_const a) using 1
  funext z
  simp only [Pi.mul_apply, Pi.add_apply, Pi.div_apply, Real.norm_eq_abs]

/-- A finite binomial expansion into already verified genuine logarithmic-pole densities. -/
theorem logPolynomialDensity_eq_sum (a : ℕ) (z : ℂ) :
    logPolynomialDensity a z =
      ∑ j ∈ Finset.range (a + 1), LogPole.density j z * (a.choose j : ℝ) := by
  rw [logPolynomialDensity, add_comm, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one, LogPole.density]
  ring

theorem integrableOn_logPolynomialDensity (a : ℕ) (ε : ℝ) :
    IntegrableOn (logPolynomialDensity a) (puncturedDisc ε) := by
  have h : IntegrableOn
      (fun z ↦ ∑ j ∈ Finset.range (a + 1), LogPole.density j z * (a.choose j : ℝ))
      (puncturedDisc ε) := integrable_finsetSum (Finset.range (a + 1)) (fun j _ ↦
    (LogPole.integrableOn_log_pole_puncturedDisc j ε).mul_const (a.choose j : ℝ))
  have heq : logPolynomialDensity a =
      (fun z ↦ ∑ j ∈ Finset.range (a + 1), LogPole.density j z * (a.choose j : ℝ)) :=
    funext (logPolynomialDensity_eq_sum a)
  rw [heq]
  exact h

/-- On a bounded positive radial interval, the max factor is controlled by one simple pole. -/
theorem max_one_inv_le {r ε : ℝ} (hr : 0 < r) (hrε : r < ε) :
    max 1 (1 / r) ≤ max 1 ε / r := by
  apply max_le
  · apply (le_div_iff₀ hr).mpr
    simpa only [one_mul] using hrε.le.trans (le_max_right 1 ε)
  · exact div_le_div_of_nonneg_right (le_max_left 1 ε) hr.le

theorem factor_le_logPolynomialDensity (a : ℕ) (ε : ℝ) {z : ℂ}
    (hz : z ∈ puncturedDisc ε) : factor a z ≤ max 1 ε * logPolynomialDensity a z := by
  calc
    factor a z ≤ (max 1 ε / ‖z‖) * (1 + |Real.log ‖z‖|) ^ a :=
      mul_le_mul_of_nonneg_right (max_one_inv_le hz.1 hz.2)
        (pow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _)
    _ = _ := by unfold logPolynomialDensity; ring

/-- Absolute integrability of one coordinate for every bounded punctured disc. -/
theorem integrableOn_factor (a : ℕ) (ε : ℝ) : IntegrableOn (factor a) (puncturedDisc ε) := by
  apply ((integrableOn_logPolynomialDensity a ε).const_mul (max 1 ε)).mono'
    (measurable_factor a).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem (measurableSet_puncturedDisc ε)] with z hz
  rw [Real.norm_of_nonneg (factor_nonneg a z)]
  exact factor_le_logPolynomialDensity a ε hz

variable {ι : Type*} [Fintype ι]

/-- A finite product of actual punctured complex discs, allowing the empty index type. -/
def puncturedPolydisc (ε : ι → ℝ) : Set (ι → ℂ) :=
  Set.univ.pi (fun i ↦ puncturedDisc (ε i))

theorem measurableSet_puncturedPolydisc (ε : ι → ℝ) : MeasurableSet (puncturedPolydisc ε) :=
  MeasurableSet.univ_pi (fun i ↦ measurableSet_puncturedDisc (ε i))

/-- The all-coordinate normal-crossing majorant. -/
def majorant (a : ι → ℕ) (z : ι → ℂ) : ℝ := ∏ i, factor (a i) (z i)

theorem majorant_eq_prod_mul (a : ι → ℕ) (z : ι → ℂ) :
    majorant a z = (∏ i, max 1 (1 / ‖z i‖)) * ∏ i, (1 + |Real.log ‖z i‖|) ^ a i := by
  simp only [majorant, factor, Finset.prod_mul_distrib]

theorem majorant_nonneg (a : ι → ℕ) (z : ι → ℂ) : 0 ≤ majorant a z :=
  Finset.prod_nonneg (fun i _ ↦ factor_nonneg (a i) (z i))

@[fun_prop] theorem measurable_majorant (a : ι → ℕ) : Measurable (majorant a) := by
  unfold majorant
  fun_prop

theorem volume_restrict_puncturedPolydisc (ε : ι → ℝ) :
    (volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε) =
      Measure.pi (fun i ↦ (volume : Measure ℂ).restrict (puncturedDisc (ε i))) := by
  rw [volume_pi, puncturedPolydisc, Measure.restrict_pi_pi]

/-- Genuine finite-product L¹ integrability. No positivity hypothesis on ε is needed;
nonpositive radii simply yield empty coordinate discs. -/
theorem integrableOn_majorant (a : ι → ℕ) (ε : ι → ℝ) :
    IntegrableOn (majorant a) (puncturedPolydisc ε) := by
  change Integrable (fun z : ι → ℂ ↦ ∏ i, factor (a i) (z i))
    ((volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε))
  rw [volume_restrict_puncturedPolydisc]
  exact Integrable.fintype_prod (fun i ↦ integrableOn_factor (a i) (ε i))

/-- The actual finite integral factors by finite-product Fubini. -/
theorem integral_majorant_eq_prod (a : ι → ℕ) (ε : ι → ℝ) :
    (∫ z in puncturedPolydisc ε, majorant a z) =
      ∏ i, ∫ z in puncturedDisc (ε i), factor (a i) z := by
  rw [volume_restrict_puncturedPolydisc]
  exact integral_fintype_prod_eq_prod (fun i ↦ factor (a i))

theorem integral_majorant_nonneg (a : ι → ℕ) (ε : ι → ℝ) :
    0 ≤ ∫ z in puncturedPolydisc ε, majorant a z := integral_nonneg (majorant_nonneg a)

/-- Finiteness in the extended reals excludes any undefined default-value integral argument. -/
theorem lintegral_majorant_lt_top (a : ι → ℕ) (ε : ι → ℝ) :
    (∫⁻ z in puncturedPolydisc ε, ENNReal.ofReal (majorant a z)) < ⊤ :=
  (integrableOn_majorant a ε).setLIntegral_lt_top

theorem ofReal_integral_majorant_eq (a : ι → ℕ) (ε : ι → ℝ) :
    ENNReal.ofReal (∫ z in puncturedPolydisc ε, majorant a z) =
      ∫⁻ z in puncturedPolydisc ε, ENNReal.ofReal (majorant a z) :=
  ofReal_integral_eq_lintegral_ofReal (integrableOn_majorant a ε)
    (Filter.Eventually.of_forall (majorant_nonneg a))

section Domination

variable {V : Type*} [NormedAddCommGroup V]

/-- Local a.e. domination yields actual integrability for any normed coefficient target. -/
theorem integrableOn_of_norm_le_majorant (a : ι → ℕ) (ε : ι → ℝ)
    (f : (ι → ℂ) → V) (C : ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε)))
    (hbound : ∀ᵐ z ∂((volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε)),
      ‖f z‖ ≤ C * majorant a z) : IntegrableOn f (puncturedPolydisc ε) :=
  ((integrableOn_majorant a ε).const_mul C).mono' hf hbound

theorem integrableOn_of_norm_le_majorant_on (a : ι → ℕ) (ε : ι → ℝ)
    (f : (ι → ℂ) → V) (C : ℝ)
    (hf : AEStronglyMeasurable f ((volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε)))
    (hbound : ∀ z ∈ puncturedPolydisc ε, ‖f z‖ ≤ C * majorant a z) :
    IntegrableOn f (puncturedPolydisc ε) := by
  apply integrableOn_of_norm_le_majorant a ε f C hf
  filter_upwards [ae_restrict_mem (measurableSet_puncturedPolydisc ε)] with z hz
  exact hbound z hz

end Domination

/-- Ordinary measurable real coefficients satisfy the local a.e. domination criterion. -/
theorem integrableOn_of_measurable_norm_le_majorant (a : ι → ℕ) (ε : ι → ℝ)
    (f : (ι → ℂ) → ℝ) (C : ℝ) (hf : Measurable f)
    (hbound : ∀ᵐ z ∂((volume : Measure (ι → ℂ)).restrict (puncturedPolydisc ε)),
      ‖f z‖ ≤ C * majorant a z) : IntegrableOn f (puncturedPolydisc ε) :=
  integrableOn_of_norm_le_majorant a ε f C hf.aestronglyMeasurable.restrict hbound

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossing
