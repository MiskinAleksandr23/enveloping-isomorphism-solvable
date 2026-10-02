import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual one-vertex configuration integrals for the harmonic angle density.
Integrability is proved before applying improper integration or Fubini. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open MeasureTheory Set Filter
open scoped Topology

/-- The harmonic edge density after fixing the upper-half-plane point at i. -/
def edgeDensity (x : ℝ) : ℝ := 2 / (1 + x ^ 2)

/-- The empty configuration has its genuine zero-dimensional product measure. -/
theorem integrable_ordered_zero : Integrable (fun _ : Fin 0 → ℝ ↦ (1 : ℝ)) := by
  rw [Measure.volume_pi_eq_dirac (fun i : Fin 0 ↦ Fin.elim0 i)]
  exact integrable_const 1

theorem integral_ordered_zero : ∫ _ : Fin 0 → ℝ, (1 : ℝ) = 1 := by
  rw [Measure.volume_pi_eq_dirac (fun i : Fin 0 ↦ Fin.elim0 i)]
  simp

theorem edgeDensity_nonneg (x : ℝ) : 0 ≤ edgeDensity x := by
  unfold edgeDensity
  positivity

theorem integrable_edgeDensity : Integrable edgeDensity := by
  change Integrable (fun x : ℝ ↦ 2 / (1 + x ^ 2))
  simpa only [div_eq_mul_inv] using
    integrable_inv_one_add_sq.const_mul (2 : ℝ)

theorem integral_edgeDensity : ∫ x : ℝ, edgeDensity x = 2 * Real.pi := by
  simp only [edgeDensity, div_eq_mul_inv, integral_const_mul, integral_univ_inv_one_add_sq]

/-- Cumulative mass of the edge density to the left of x. -/
def edgeMass (x : ℝ) : ℝ := 2 * (Real.arctan x + Real.pi / 2)

@[fun_prop] theorem continuous_edgeMass : Continuous edgeMass := by
  unfold edgeMass
  fun_prop

theorem edgeMass_nonneg (x : ℝ) : 0 ≤ edgeMass x := by
  have h := Real.neg_pi_div_two_lt_arctan x
  unfold edgeMass
  linarith

theorem edgeMass_le (x : ℝ) : edgeMass x ≤ 2 * Real.pi := by
  have h := Real.arctan_lt_pi_div_two x
  unfold edgeMass
  linarith

theorem hasDerivAt_edgeMass (x : ℝ) : HasDerivAt edgeMass (edgeDensity x) x := by
  change HasDerivAt (fun y : ℝ ↦ 2 * (Real.arctan y + Real.pi / 2)) (2 / (1 + x ^ 2)) x
  simpa only [div_eq_mul_inv] using
    ((Real.hasDerivAt_arctan' x).add_const (Real.pi / 2)).const_mul (2 : ℝ)

theorem tendsto_edgeMass_atBot : Tendsto edgeMass atBot (𝓝 0) := by
  change Tendsto (fun x : ℝ ↦ 2 * (Real.arctan x + Real.pi / 2)) atBot (𝓝 0)
  have h := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).add_const
    (Real.pi / 2)).const_mul 2
  simpa only [neg_add_cancel, mul_zero] using h

theorem tendsto_edgeMass_atTop : Tendsto edgeMass atTop (𝓝 (2 * Real.pi)) := by
  change Tendsto (fun x : ℝ ↦ 2 * (Real.arctan x + Real.pi / 2)) atTop (𝓝 (2 * Real.pi))
  have h := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).add_const
    (Real.pi / 2)).const_mul 2
  rw [show 2 * (Real.pi / 2 + Real.pi / 2) = 2 * Real.pi by ring] at h
  exact h

/-- All cumulative-mass weighted densities are absolutely integrable. -/
theorem integrable_edgeDensity_mul_edgeMass_pow (n : ℕ) :
    Integrable (fun x : ℝ ↦ edgeDensity x * edgeMass x ^ n) := by
  apply integrable_edgeDensity.mul_bdd (continuous_edgeMass.pow n).aestronglyMeasurable
    (c := (2 * Real.pi) ^ n)
  filter_upwards [] with x
  change ‖edgeMass x ^ n‖ ≤ (2 * Real.pi) ^ n
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (edgeMass_nonneg x) n)]
  exact pow_le_pow_left₀ (edgeMass_nonneg x) (edgeMass_le x) n

private theorem hasDerivAt_massPrimitive (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ edgeMass y ^ (n + 1) / (n + 1 : ℝ))
      (edgeDensity x * edgeMass x ^ n) x := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have heq : ((n + 1 : ℝ) * edgeMass x ^ n * edgeDensity x) / (n + 1 : ℝ) =
      edgeDensity x * edgeMass x ^ n := by
    field_simp
  simpa only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one, Pi.pow_apply, heq] using
    ((hasDerivAt_edgeMass x).pow (n + 1)).div_const (n + 1 : ℝ)

private theorem tendsto_massPrimitive_atBot (n : ℕ) :
    Tendsto (fun x : ℝ ↦ edgeMass x ^ (n + 1) / (n + 1 : ℝ)) atBot (𝓝 0) := by
  simpa using (tendsto_edgeMass_atBot.pow (n + 1)).div_const (n + 1 : ℝ)

/-- Fundamental theorem of calculus for every iterated ordered-integral layer. -/
theorem integral_edgeDensity_mul_edgeMass_pow (n : ℕ) :
    ∫ x : ℝ, edgeDensity x * edgeMass x ^ n = (2 * Real.pi) ^ (n + 1) / (n + 1 : ℝ) := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_massPrimitive n)
    (integrable_edgeDensity_mul_edgeMass_pow n) (tendsto_massPrimitive_atBot n)
    ((tendsto_edgeMass_atTop.pow (n + 1)).div_const (n + 1 : ℝ))
  simpa only [sub_zero] using h

theorem integral_Iio_edgeDensity_mul_edgeMass_pow (n : ℕ) (b : ℝ) :
    ∫ x : ℝ in Iio b, edgeDensity x * edgeMass x ^ n = edgeMass b ^ (n + 1) / (n + 1 : ℝ) := by
  rw [← integral_Iic_eq_integral_Iio]
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := b)
    (fun x _ ↦ hasDerivAt_massPrimitive n x)
    (integrable_edgeDensity_mul_edgeMass_pow n).integrableOn (tendsto_massPrimitive_atBot n)
  simpa only [sub_zero] using h

theorem integral_Iio_edgeDensity (b : ℝ) : ∫ x : ℝ in Iio b, edgeDensity x = edgeMass b := by
  simpa using integral_Iio_edgeDensity_mul_edgeMass_pow 0 b

/-- The ordered two-point real configuration chamber. -/
def orderedPairSet : Set (ℝ × ℝ) := {p | p.1 < p.2}

theorem measurableSet_orderedPair : MeasurableSet orderedPairSet :=
  measurableSet_lt measurable_fst measurable_snd

theorem integrableOn_orderedPair {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    IntegrableOn (fun p : ℝ × ℝ ↦ f p.1 * g p.2) orderedPairSet :=
  (hf.mul_prod hg).integrableOn

/-- Actual Fubini bridge from the ordered chamber to an iterated integral. -/
theorem orderedPair_fubini {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ p : ℝ × ℝ in orderedPairSet, f p.1 * g p.2 =
      ∫ y : ℝ, (∫ x : ℝ in Iio y, f x) * g y := by
  rw [← integral_indicator measurableSet_orderedPair]
  rw [Measure.volume_eq_prod]
  rw [integral_prod_symm _ ((hf.mul_prod hg).indicator measurableSet_orderedPair)]
  apply integral_congr_ae
  filter_upwards [] with y
  change (∫ x : ℝ, (Iio y).indicator (fun x ↦ f x * g y) x) = _
  rw [integral_indicator measurableSet_Iio, integral_mul_const]

theorem integrableOn_ordered_two :
    IntegrableOn (fun p : ℝ × ℝ ↦ edgeDensity p.1 * edgeDensity p.2) orderedPairSet :=
  integrableOn_orderedPair integrable_edgeDensity integrable_edgeDensity

/-- The ordered two-edge weight is the actual absolutely convergent chamber
integral, equal to `(2π)^2 / 2!`. -/
theorem integral_ordered_two :
    ∫ p : ℝ × ℝ in orderedPairSet, edgeDensity p.1 * edgeDensity p.2 =
      (2 * Real.pi) ^ 2 / 2 := by
  rw [orderedPair_fubini integrable_edgeDensity integrable_edgeDensity]
  simp_rw [integral_Iio_edgeDensity]
  have h := integral_edgeDensity_mul_edgeMass_pow 1
  simpa only [pow_one, Nat.cast_one, one_add_one_eq_two, mul_comm] using h

/-- The ordered three-point chamber, in the ordinary product Lebesgue space. -/
def orderedTripleSet : Set (ℝ × ℝ × ℝ) := {p | p.1 < p.2.1 ∧ p.2.1 < p.2.2}

theorem measurableSet_orderedTriple : MeasurableSet orderedTripleSet :=
  (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)).inter
    (measurableSet_lt (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd))

theorem integrableOn_ordered_three :
    IntegrableOn (fun p : ℝ × ℝ × ℝ ↦
      edgeDensity p.1 * (edgeDensity p.2.1 * edgeDensity p.2.2)) orderedTripleSet :=
  (integrable_edgeDensity.mul_prod (integrable_edgeDensity.mul_prod integrable_edgeDensity)).integrableOn

/-- An explicit Fubini reduction of the genuine three-dimensional chamber
integral; the integrable indicator, rather than an undefined integral, is used. -/
theorem orderedTriple_fubini :
    ∫ p : ℝ × ℝ × ℝ in orderedTripleSet,
      edgeDensity p.1 * (edgeDensity p.2.1 * edgeDensity p.2.2) =
      ∫ p : ℝ × ℝ in orderedPairSet, (edgeDensity p.1 * edgeMass p.1) * edgeDensity p.2 := by
  rw [← integral_indicator measurableSet_orderedTriple]
  rw [Measure.volume_eq_prod]
  have hi : Integrable (orderedTripleSet.indicator
      (fun p : ℝ × ℝ × ℝ ↦ edgeDensity p.1 * (edgeDensity p.2.1 * edgeDensity p.2.2)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    simpa only [Measure.volume_eq_prod] using
      (integrable_edgeDensity.mul_prod (integrable_edgeDensity.mul_prod integrable_edgeDensity)).indicator
        measurableSet_orderedTriple
  rw [integral_prod_symm _ hi]
  have hinner (p : ℝ × ℝ) :
      (∫ x : ℝ, orderedTripleSet.indicator
        (fun q : ℝ × ℝ × ℝ ↦ edgeDensity q.1 * (edgeDensity q.2.1 * edgeDensity q.2.2)) (x, p)) =
        orderedPairSet.indicator
          (fun q : ℝ × ℝ ↦ (edgeDensity q.1 * edgeMass q.1) * edgeDensity q.2) p := by
    by_cases hp : p.1 < p.2
    · have hfun : (fun x : ℝ ↦ orderedTripleSet.indicator
          (fun q : ℝ × ℝ × ℝ ↦ edgeDensity q.1 * (edgeDensity q.2.1 * edgeDensity q.2.2)) (x, p)) =
          (Iio p.1).indicator (fun x ↦ edgeDensity x * (edgeDensity p.1 * edgeDensity p.2)) := by
        funext x
        simp [orderedTripleSet, Set.indicator_apply, hp]
      rw [hfun, integral_indicator measurableSet_Iio, integral_mul_const, integral_Iio_edgeDensity]
      rw [Set.indicator_of_mem (show p ∈ orderedPairSet from hp)]
      ring
    · simp [orderedTripleSet, orderedPairSet, hp]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_orderedPair]

/-- The ordered three-edge weight is the actual absolutely convergent chamber
integral, equal to `(2π)^3 / 3!`. -/
theorem integral_ordered_three :
    ∫ p : ℝ × ℝ × ℝ in orderedTripleSet,
      edgeDensity p.1 * (edgeDensity p.2.1 * edgeDensity p.2.2) =
      (2 * Real.pi) ^ 3 / 6 := by
  have hi : Integrable (fun x : ℝ ↦ edgeDensity x * edgeMass x) := by
    simpa using integrable_edgeDensity_mul_edgeMass_pow 1
  rw [orderedTriple_fubini, orderedPair_fubini hi integrable_edgeDensity]
  have hinner (y : ℝ) :
      (∫ x : ℝ in Iio y, edgeDensity x * edgeMass x) = edgeMass y ^ 2 / 2 := by
    simpa only [pow_one, Nat.cast_one, one_add_one_eq_two] using
      integral_Iio_edgeDensity_mul_edgeMass_pow 1 y
  simp_rw [hinner]
  calc
    (∫ y : ℝ, edgeMass y ^ 2 / 2 * edgeDensity y) =
        (∫ y : ℝ, edgeDensity y * edgeMass y ^ 2) / 2 := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = (2 * Real.pi) ^ 3 / 6 := by
      rw [integral_edgeDensity_mul_edgeMass_pow]
      norm_num
      ring

end EnvelopingIsomorphism.Deformation.Kontsevich
