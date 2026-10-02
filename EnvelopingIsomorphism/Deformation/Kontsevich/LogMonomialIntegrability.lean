import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialMatrix
import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingDeterminantIntegrability
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine local L1 bounds for actual logarithmic monomial determinants

The regular row bounds follow from the actual unit derivative and lower-norm
bounds. Integer exponent bounds follow from their finite array. The actual
matrix identity and normal-crossing simple-pole integrability are then applied.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open MeasureTheory Set
open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A numerical bound derived from the given finite integer exponent array. -/
def exponentBound (a : I → J → ℤ) : ℝ := 1 + ∑ p : I × J, |(a p.1 p.2 : ℝ)|

omit [DecidableEq I] [DecidableEq J] in
theorem one_le_exponentBound (a : I → J → ℤ) : 1 ≤ exponentBound a := by
  unfold exponentBound
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => abs_nonneg _)

omit [DecidableEq I] [DecidableEq J] in
theorem integerCoefficients_bound (a : I → J → ℤ) (i : I) (ν : J) :
    |integerCoefficients a i ν| ≤ exponentBound a := by
  have h : |(a i ν : ℝ)| ≤ ∑ p : I × J, |(a p.1 p.2 : ℝ)| :=
    Finset.single_le_sum (f := fun p : I × J => |(a p.1 p.2 : ℝ)|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (i, ν))
  exact h.trans (le_add_of_nonneg_left zero_le_one)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem smoothRows_bound (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ)
    (x : J → ℂ) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D) (hu : ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) (i j : I) : |smoothRows u v x i j| ≤ D / c := by
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD i)
  have he : ‖fderiv ℝ (u i) x (v j)‖ ≤ D :=
    ((fderiv ℝ (u i) x).le_opNorm (v j)).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hv j)).trans (hD i))
  calc
    |smoothRows u v x i j| ≤ ‖fderiv ℝ (u i) x (v j)‖ / ‖u i x‖ := by
      simpa only [smoothRows, norm_div] using Complex.abs_re_le_norm (fderiv ℝ (u i) x (v j) / u i x)
    _ ≤ D / ‖u i x‖ := div_le_div_of_nonneg_right he (norm_nonneg _)
    _ ≤ D / c := div_le_div_of_nonneg_left hDn hc (hu i)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem unitRadialRows_bound_one (v : I → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1)
    (x : J → ℂ) (ν : J) (j : I) : |unitRadialRows v x ν j| ≤ 1 :=
  (unitRadialRows_bound v x ν j).trans ((norm_le_pi_norm (v j) ν).trans (hv j))

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem measurable_smoothRows (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (i j : I) : Measurable (fun x => smoothRows u v x i j) := by
  have hd : Continuous (fun x => fderiv ℝ (u i) x (v j)) :=
    ((hu i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact Complex.continuous_re.measurable.comp (hd.measurable.div (hu i).continuous.measurable)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem measurable_unitRadialRows (v : I → J → ℂ) (ν : J) (j : I) :
    Measurable (fun x : J → ℂ => unitRadialRows v x ν j) := by
  unfold unitRadialRows unitRadial
  exact ((measurable_pi_apply ν).norm).mul
    (Complex.continuous_re.measurable.comp (measurable_const.div (measurable_pi_apply ν)))

/-- The actual determinant density with an optional finite logarithmic weight. -/
def weightedActualDeterminant (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (w : J → ℕ) (x : J → ℂ) : ℝ :=
  Matrix.det (actualRadialMatrix a u v x) * NormalCrossingDeterminantIntegrability.logWeight w x

omit [DecidableEq J] in
/-- On the punctured locus this is the proved actual normal-crossing matrix, not a supplied identity. -/
theorem weightedActualDeterminant_eq (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (w : J → ℕ) (x : J → ℂ)
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    weightedActualDeterminant a u v w x =
      NormalCrossingDeterminantIntegrability.weightedDeterminant w
        (smoothRows u v) (unitRadialRows v) (fun _ => integerCoefficients a) x := by
  rw [weightedActualDeterminant, actualRadialMatrix_eq a u v hu hu0 hx]
  rfl

/-- Actual monomial radial determinants are L1. The C1 hypothesis is global only
to provide measurability; all quantitative unit bounds are restricted to the specified polydisc. -/
theorem integrableOn_weightedActualDeterminant (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (w : J → ℕ) (ε : J → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (weightedActualDeterminant a u v w) (NormalCrossing.puncturedPolydisc ε) := by
  have hi := NormalCrossingDeterminantIntegrability.integrableOn_weightedDeterminant_of_entryBounds
    w ε (smoothRows u v) (unitRadialRows v) (fun _ => integerCoefficients a)
    (measurable_smoothRows u v hu) (measurable_unitRadialRows v) (fun _ _ => measurable_const)
    (max 1 (D / c)) (exponentBound a) (le_max_left _ _) (one_le_exponentBound a)
    (fun x hx i j => (smoothRows_bound u v x D c hc (hD x hx) (hunit x hx) hv i j).trans (le_max_right _ _))
    (fun x _ ν j => (unitRadialRows_bound_one v hv x ν j).trans (le_max_left _ _))
    (fun _ _ i ν => integerCoefficients_bound a i ν)
  apply hi.congr_fun _ (NormalCrossing.measurableSet_puncturedPolydisc ε)
  intro x hx
  symm
  apply weightedActualDeterminant_eq
  · intro i
    exact (hu i).differentiable (by norm_num) x
  · intro i
    exact norm_pos_iff.mp (hc.trans_le (hunit x hx i))
  · intro ν
    exact norm_pos_iff.mp ((hx ν (Set.mem_univ ν)).1)

theorem integrableOn_actualRadialDeterminant (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (ε : J → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x => Matrix.det (actualRadialMatrix a u v x)) (NormalCrossing.puncturedPolydisc ε) := by
  have heq : weightedActualDeterminant a u v (fun _ => 0) = fun x => Matrix.det (actualRadialMatrix a u v x) := by
    funext x
    simp only [weightedActualDeterminant, NormalCrossingDeterminantIntegrability.logWeight,
      pow_zero, Finset.prod_const_one, mul_one]
  rw [← heq]
  exact integrableOn_weightedActualDeterminant a u v (fun _ => 0) ε hu D c hc hD hunit hv

theorem integrableOn_abs_weightedActualDeterminant (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (w : J → ℕ) (ε : J → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x => |weightedActualDeterminant a u v w x|) (NormalCrossing.puncturedPolydisc ε) := by
  change Integrable (fun x => |weightedActualDeterminant a u v w x|)
    (volume.restrict (NormalCrossing.puncturedPolydisc ε))
  simpa only [Real.norm_eq_abs] using
    (integrableOn_weightedActualDeterminant a u v w ε hu D c hc hD hunit hv).norm

theorem lintegral_abs_weightedActualDeterminant_lt_top (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (w : J → ℕ) (ε : J → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    (∫⁻ x in NormalCrossing.puncturedPolydisc ε, ENNReal.ofReal |weightedActualDeterminant a u v w x|) < ⊤ :=
  (integrableOn_abs_weightedActualDeterminant a u v w ε hu D c hc hD hunit hv).setLIntegral_lt_top

/-- The explicit finite constant obtained after determinant alternation. -/
def uniformDeterminantBound (a : I → J → ℤ) (D c : ℝ) : ℝ :=
  ((Fintype.card J : ℝ) + 1) ^ Fintype.card I * (exponentBound a) ^ Fintype.card I *
    ((Fintype.card I).factorial : ℝ) * (max 1 (D / c)) ^ Fintype.card I

theorem coefficientBound_le_unitBounds (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (x : J → ℂ) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D) (hunit : ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    RadialPoleDeterminant.coefficientBound (smoothRows u v x) (unitRadialRows v x)
      (integerCoefficients a) ≤ uniformDeterminantBound a D c :=
  RadialPoleDeterminant.coefficientBound_le_uniform _ _ _ (max 1 (D / c)) (exponentBound a)
    (le_max_left _ _) (one_le_exponentBound a)
    (fun i j => (smoothRows_bound u v x D c hc hD hunit hv i j).trans (le_max_right _ _))
    (fun ν j => (unitRadialRows_bound_one v hv x ν j).trans (le_max_left _ _))
    (integerCoefficients_bound a)

/-- C1 regularity is needed only on an open neighborhood of the actual punctured polydisc. -/
theorem continuousOn_modelDeterminant_of_localC1 (a : I → J → ℤ)
    (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, u i x ≠ 0) :
    ContinuousOn (NormalCrossingDeterminantIntegrability.determinantField
      (smoothRows u v) (unitRadialRows v) (fun _ => integerCoefficients a))
      (NormalCrossing.puncturedPolydisc ε) := by
  have hx0 (x : J → ℂ) (hx : x ∈ NormalCrossing.puncturedPolydisc ε) (ν : J) : x ν ≠ 0 :=
    norm_pos_iff.mp ((hx ν (Set.mem_univ ν)).1)
  have hB (i j : I) : ContinuousOn (fun x => smoothRows u v x i j) (NormalCrossing.puncturedPolydisc ε) := by
    have hd := ((hu i).continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply (continuousOn_const (c := v j))
    exact Complex.continuous_re.comp_continuousOn
      ((hd.mono hsub).div ((hu i).continuousOn.mono hsub) (fun x hx => hunit x hx i))
  have hρ (ν : J) (j : I) : ContinuousOn (fun x => unitRadialRows v x ν j)
      (NormalCrossing.puncturedPolydisc ε) := by
    have hz := (continuous_apply ν : Continuous (fun x : J → ℂ => x ν)).continuousOn
      (s := NormalCrossing.puncturedPolydisc ε)
    exact hz.norm.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_const.div hz (fun x hx => hx0 x hx ν)))
  have ht (ν : J) : ContinuousOn (fun x => NormalCrossingDeterminantIntegrability.radialParameters x ν)
      (NormalCrossing.puncturedPolydisc ε) :=
    continuousOn_const.div (continuous_apply ν).continuousOn.norm
      (fun x hx => norm_ne_zero_iff.mpr (hx0 x hx ν))
  have hm (i j : I) : ContinuousOn
      (fun x => RadialPoleDeterminant.matrix (smoothRows u v x) (unitRadialRows v x)
        (integerCoefficients a) (NormalCrossingDeterminantIntegrability.radialParameters x) i j)
      (NormalCrossing.puncturedPolydisc ε) := by
    simp only [RadialPoleDeterminant.matrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply (hB i j).add
    apply continuousOn_finsetSum
    intro ν _
    exact (continuousOn_const.mul (ht ν)).mul (hρ ν j)
  unfold NormalCrossingDeterminantIntegrability.determinantField
  simp only [Matrix.det_apply]
  fun_prop

/-- Local C1 unit hypotheses suffice: no global extension, global measurability
of the actual monomial derivative, or supplied coefficient bound is assumed. -/
theorem integrableOn_weightedActualDeterminant_of_localC1
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (w : J → ℕ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (weightedActualDeterminant a u v w) (NormalCrossing.puncturedPolydisc ε) := by
  have hu0 (x : J → ℂ) (hx : x ∈ NormalCrossing.puncturedPolydisc ε) (i : I) : u i x ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le (hunit x hx i))
  have hd := continuousOn_modelDeterminant_of_localC1 a u v ε U hU hsub hu hu0
  have hm := (hd.aestronglyMeasurable (μ := volume) (NormalCrossing.measurableSet_puncturedPolydisc ε)).mul
    (NormalCrossingDeterminantIntegrability.measurable_logWeight w).aestronglyMeasurable.restrict
  have hi := NormalCrossing.integrableOn_of_norm_le_majorant_on w ε
    (NormalCrossingDeterminantIntegrability.weightedDeterminant w
      (smoothRows u v) (unitRadialRows v) (fun _ => integerCoefficients a))
    (uniformDeterminantBound a D c) hm (fun x hx =>
      (NormalCrossingDeterminantIntegrability.norm_weightedDeterminant_le w
        (smoothRows u v) (unitRadialRows v) (fun _ => integerCoefficients a) x).trans
        (mul_le_mul_of_nonneg_right
          (coefficientBound_le_unitBounds a u v x D c hc (hD x hx) (hunit x hx) hv)
          (NormalCrossing.majorant_nonneg w x)))
  apply hi.congr_fun _ (NormalCrossing.measurableSet_puncturedPolydisc ε)
  intro x hx
  symm
  apply weightedActualDeterminant_eq
  · intro i
    exact ((hu i).contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num)
  · exact hu0 x hx
  · intro ν
    exact norm_pos_iff.mp ((hx ν (Set.mem_univ ν)).1)

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
