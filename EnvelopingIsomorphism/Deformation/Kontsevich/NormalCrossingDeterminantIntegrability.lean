import EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleUniformBound
import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingMajorant

/-! The actual determinant with shared radial pole rows is locally L1, even
with logarithmic weights. The simple-pole estimate is applied after determinant
alternation; no product of the singular norms of the original rows is used. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingDeterminantIntegrability

open MeasureTheory Set
open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- One actual inverse radial factor per normal-crossing coordinate. -/
def radialParameters (z : J → ℂ) (ν : J) : ℝ := 1 / ‖z ν‖

/-- The logarithmic weight, with its harmless total value on the deleted divisors. -/
def logWeight (a : J → ℕ) (z : J → ℂ) : ℝ := ∏ ν, (1 + |Real.log ‖z ν‖|) ^ a ν

/-- The determinant of the actual matrix B + sum c_iν tν ρν. -/
def determinantField (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ)
    (c : (J → ℂ) → I → J → ℝ) (z : J → ℂ) : ℝ :=
  Matrix.det (RadialPoleDeterminant.matrix (B z) (ρ z) (c z) (radialParameters z))

def weightedDeterminant (a : J → ℕ) (B : (J → ℂ) → Matrix I I ℝ)
    (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ) (z : J → ℂ) : ℝ :=
  determinantField B ρ c z * logWeight a z

omit [Fintype J] [DecidableEq J] in
theorem radialParameters_nonneg (z : J → ℂ) (ν : J) : 0 ≤ radialParameters z ν :=
  div_nonneg zero_le_one (norm_nonneg _)

omit [DecidableEq J] in
theorem logWeight_nonneg (a : J → ℕ) (z : J → ℂ) : 0 ≤ logWeight a z :=
  Finset.prod_nonneg (fun ν _ ↦ pow_nonneg (by positivity) _)

omit [Fintype J] [DecidableEq J] in
@[fun_prop] theorem measurable_radialParameters (ν : J) : Measurable (fun z : J → ℂ ↦ radialParameters z ν) :=
  measurable_const.div ((measurable_pi_apply ν).norm)

omit [DecidableEq J] in
@[fun_prop] theorem measurable_logWeight (a : J → ℕ) : Measurable (logWeight a) := by
  have hlog (ν : J) : Measurable (fun z : J → ℂ ↦ Real.log ‖z ν‖) :=
    Real.measurable_log.comp ((measurable_pi_apply ν).norm)
  unfold logWeight
  fun_prop

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
/-- Every matrix entry is an actual finite measurable sum of the stated fields. -/
theorem measurable_matrix_entry (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ)
    (c : (J → ℂ) → I → J → ℝ) (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν))
    (i j : I) :
    Measurable (fun z ↦ RadialPoleDeterminant.matrix (B z) (ρ z) (c z) (radialParameters z) i j) := by
  have hb : Measurable (fun z ↦ B z i j) := hB i j
  have hr (ν : J) : Measurable (fun z ↦ ρ z ν j) :=
    hρ ν j
  have hh (ν : J) : Measurable (fun z ↦ c z i ν) :=
    hc i ν
  simp only [RadialPoleDeterminant.matrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

omit [DecidableEq J] in
@[fun_prop] theorem measurable_determinantField (B : (J → ℂ) → Matrix I I ℝ)
    (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν)) : Measurable (determinantField B ρ c) := by
  have hm := measurable_matrix_entry B ρ c hB hρ hc
  unfold determinantField
  simp only [Matrix.det_apply]
  fun_prop

omit [DecidableEq J] in
@[fun_prop] theorem measurable_weightedDeterminant (a : J → ℕ) (B : (J → ℂ) → Matrix I I ℝ)
    (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν)) :
    Measurable (weightedDeterminant a B ρ c) :=
  (measurable_determinantField B ρ c hB hρ hc).mul (measurable_logWeight a)

/-- Alternation has already removed all repeated radial poles before this norm estimate. -/
theorem norm_weightedDeterminant_le (a : J → ℕ) (B : (J → ℂ) → Matrix I I ℝ)
    (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ) (z : J → ℂ) :
    ‖weightedDeterminant a B ρ c z‖ ≤
      RadialPoleDeterminant.coefficientBound (B z) (ρ z) (c z) * NormalCrossing.majorant a z := by
  rw [weightedDeterminant, Real.norm_eq_abs, abs_mul, abs_of_nonneg (logWeight_nonneg a z)]
  have h := mul_le_mul_of_nonneg_right
    (RadialPoleDeterminant.abs_det_le_simple_poles (B z) (ρ z) (c z) (radialParameters z)
      (radialParameters_nonneg z)) (logWeight_nonneg a z)
  simpa only [determinantField, NormalCrossing.majorant_eq_prod_mul, radialParameters,
    logWeight, mul_assoc] using h

/-- Uniform control of the genuine smooth determinant coefficients gives actual local L1.
The radii may be arbitrary; nonpositive radii simply give empty punctured discs. -/
theorem integrableOn_weightedDeterminant_of_coefficientBound (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν)) (C : ℝ)
    (hbound : ∀ z ∈ NormalCrossing.puncturedPolydisc ε,
      RadialPoleDeterminant.coefficientBound (B z) (ρ z) (c z) ≤ C) :
    IntegrableOn (weightedDeterminant a B ρ c) (NormalCrossing.puncturedPolydisc ε) := by
  apply NormalCrossing.integrableOn_of_norm_le_majorant_on a ε _ C
    (measurable_weightedDeterminant a B ρ c hB hρ hc).aestronglyMeasurable.restrict
  intro z hz
  exact (norm_weightedDeterminant_le a B ρ c z).trans
    (mul_le_mul_of_nonneg_right (hbound z hz) (NormalCrossing.majorant_nonneg a z))

theorem integrableOn_abs_weightedDeterminant_of_coefficientBound (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν)) (C : ℝ)
    (hbound : ∀ z ∈ NormalCrossing.puncturedPolydisc ε,
      RadialPoleDeterminant.coefficientBound (B z) (ρ z) (c z) ≤ C) :
    IntegrableOn (fun z ↦ |weightedDeterminant a B ρ c z|) (NormalCrossing.puncturedPolydisc ε) := by
  change Integrable (fun z ↦ |weightedDeterminant a B ρ c z|) (volume.restrict (NormalCrossing.puncturedPolydisc ε))
  simpa only [Real.norm_eq_abs] using
    (integrableOn_weightedDeterminant_of_coefficientBound a ε B ρ c hB hρ hc C hbound).norm

theorem lintegral_abs_weightedDeterminant_lt_top_of_coefficientBound (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν)) (C : ℝ)
    (hbound : ∀ z ∈ NormalCrossing.puncturedPolydisc ε,
      RadialPoleDeterminant.coefficientBound (B z) (ρ z) (c z) ≤ C) :
    (∫⁻ z in NormalCrossing.puncturedPolydisc ε, ENNReal.ofReal |weightedDeterminant a B ρ c z|) < ⊤ :=
  (integrableOn_abs_weightedDeterminant_of_coefficientBound a ε B ρ c hB hρ hc C hbound).setLIntegral_lt_top


/-- Entry bounds supply the coefficient estimate by the actual finite determinant expansion,
so no integrability or coefficient-bound assumption is left to the caller. -/
theorem integrableOn_weightedDeterminant_of_entryBounds (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν))
    (B₀ C₀ : ℝ) (hB₀ : 1 ≤ B₀) (hC₀ : 1 ≤ C₀)
    (hBb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i j, |B z i j| ≤ B₀)
    (hρb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ ν j, |ρ z ν j| ≤ B₀)
    (hcb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i ν, |c z i ν| ≤ C₀) :
    IntegrableOn (weightedDeterminant a B ρ c) (NormalCrossing.puncturedPolydisc ε) := by
  apply integrableOn_weightedDeterminant_of_coefficientBound a ε B ρ c hB hρ hc
    (((Fintype.card J : ℝ) + 1) ^ Fintype.card I * C₀ ^ Fintype.card I *
      ((Fintype.card I).factorial : ℝ) * B₀ ^ Fintype.card I)
  intro z hz
  exact RadialPoleDeterminant.coefficientBound_le_uniform (B z) (ρ z) (c z) B₀ C₀ hB₀ hC₀
    (hBb z hz) (hρb z hz) (hcb z hz)

/-- The absolute logarithmically weighted density is genuinely L1. -/
theorem integrableOn_abs_weightedDeterminant_of_entryBounds (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν))
    (B₀ C₀ : ℝ) (hB₀ : 1 ≤ B₀) (hC₀ : 1 ≤ C₀)
    (hBb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i j, |B z i j| ≤ B₀)
    (hρb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ ν j, |ρ z ν j| ≤ B₀)
    (hcb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i ν, |c z i ν| ≤ C₀) :
    IntegrableOn (fun z ↦ |weightedDeterminant a B ρ c z|) (NormalCrossing.puncturedPolydisc ε) := by
  change Integrable (fun z ↦ |weightedDeterminant a B ρ c z|) (volume.restrict (NormalCrossing.puncturedPolydisc ε))
  simpa only [Real.norm_eq_abs] using
    (integrableOn_weightedDeterminant_of_entryBounds a ε B ρ c hB hρ hc B₀ C₀ hB₀ hC₀ hBb hρb hcb).norm

/-- Finite extended-real mass rules out reliance on the integral's nonintegrable default value. -/
theorem lintegral_abs_weightedDeterminant_lt_top_of_entryBounds (a : J → ℕ) (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν))
    (B₀ C₀ : ℝ) (hB₀ : 1 ≤ B₀) (hC₀ : 1 ≤ C₀)
    (hBb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i j, |B z i j| ≤ B₀)
    (hρb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ ν j, |ρ z ν j| ≤ B₀)
    (hcb : ∀ z ∈ NormalCrossing.puncturedPolydisc ε, ∀ i ν, |c z i ν| ≤ C₀) :
    (∫⁻ z in NormalCrossing.puncturedPolydisc ε, ENNReal.ofReal |weightedDeterminant a B ρ c z|) < ⊤ :=
  (integrableOn_abs_weightedDeterminant_of_entryBounds a ε B ρ c hB hρ hc B₀ C₀ hB₀ hC₀ hBb hρb hcb).setLIntegral_lt_top

/-- In particular the original determinant itself, with no logarithmic weight, is integrable. -/
theorem integrableOn_determinant_of_coefficientBound (ε : J → ℝ)
    (B : (J → ℂ) → Matrix I I ℝ) (ρ : (J → ℂ) → J → I → ℝ) (c : (J → ℂ) → I → J → ℝ)
    (hB : ∀ i j, Measurable (fun z ↦ B z i j))
    (hρ : ∀ ν j, Measurable (fun z ↦ ρ z ν j)) (hc : ∀ i ν, Measurable (fun z ↦ c z i ν))
    (C : ℝ) (hbound : ∀ z ∈ NormalCrossing.puncturedPolydisc ε,
      RadialPoleDeterminant.coefficientBound (B z) (ρ z) (c z) ≤ C) :
    IntegrableOn (determinantField B ρ c) (NormalCrossing.puncturedPolydisc ε) := by
  have heq : weightedDeterminant (fun _ ↦ 0) B ρ c = determinantField B ρ c := by
    funext z
    simp only [weightedDeterminant, logWeight, pow_zero, Finset.prod_const_one, mul_one]
  rw [← heq]
  exact integrableOn_weightedDeterminant_of_coefficientBound (fun _ ↦ 0) ε B ρ c hB hρ hc C hbound

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingDeterminantIntegrability
