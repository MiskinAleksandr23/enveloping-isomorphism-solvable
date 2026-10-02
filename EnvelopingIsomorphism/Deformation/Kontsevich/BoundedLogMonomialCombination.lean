import EnvelopingIsomorphism.Deformation.Kontsevich.CompactMonomialStokes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bounded measurable combinations of actual logarithmic radial covectors,
wedge the native logarithmic primitive. The exact alternating coefficient is a
finite sum of augmented monomial determinants. Repeated radial rows cancel in
those determinants before any norm estimate is taken. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination

open ContinuousAlternatingMap MeasureTheory Set Filter
open scoped BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Insert an extra logarithmic differential immediately after the logarithmic multiplier. -/
def augment {A : Type*} (f : Fin (n + 1) → A) (g : A) : Fin (n + 2) → A :=
  Fin.cons (f 0) (Fin.cons g (fun j : Fin n ↦ f j.succ))

@[simp] theorem augment_zero {A : Type*} (f : Fin (n + 1) → A) (g : A) :
    augment f g 0 = f 0 := rfl

@[simp] theorem augment_one {A : Type*} (f : Fin (n + 1) → A) (g : A) :
    augment f g 1 = g := rfl

@[simp] theorem augment_succ_succ {A : Type*} (f : Fin (n + 1) → A) (g : A) (j : Fin n) :
    augment f g j.succ.succ = f j.succ := rfl

/-- The actual pulled back logarithmic radial covector. -/
def radialCovector (g : E → ℂ) (x : E) : E →L[ℝ] ℝ :=
  (radialLinearCoefficient (g x)⁻¹).comp (fderiv ℝ g x)

@[simp] theorem radialCovector_apply (g : E → ℂ) (x v : E) :
    radialCovector g x v = (fderiv ℝ g x v / g x).re := by
  simp [radialCovector, div_eq_inv_mul]

/-- Native one-form wedge primitive, in the same normalization as the exterior derivative. -/
def wedgePrimitive (ℓ : E →L[ℝ] ℝ) (f : Fin (n + 1) → E → ℂ) (x : E) :
    E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  alternatizeUncurryFin (ℓ.smulRight (LogRadialPrimitive.primitive f x))

/-- Exact Laplace expansion of the native alternating coefficient. -/
theorem wedgePrimitive_radial_eq (f : Fin (n + 1) → E → ℂ) (g : E → ℂ) (x : E)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (hg : DifferentiableAt ℝ g x)
    (hf0 : ∀ j, f j x ≠ 0) (hg0 : g x ≠ 0) :
    wedgePrimitive (radialCovector g x) f x = LogRadialPrimitive.primitive (augment f g) x := by
  have haug : ∀ j, DifferentiableAt ℝ (augment f g j) x := by
    intro j
    refine Fin.cases (hf 0) (fun j ↦ ?_) j
    exact Fin.cases hg (fun j ↦ hf j.succ) j
  have haug0 : ∀ j, augment f g j x ≠ 0 := by
    intro j
    refine Fin.cases (hf0 0) (fun j ↦ ?_) j
    exact Fin.cases hg0 (fun j ↦ hf0 j.succ) j
  ext v
  simp only [wedgePrimitive, alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    radialCovector_apply, LogRadialPrimitive.primitive_apply _ hf hf0,
    LogRadialPrimitive.primitive_apply _ haug haug0, augment_zero]
  rw [Matrix.det_succ_column_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1 : ℝ) ^ i.val * ((fderiv ℝ g x (v i) / g x).re *
      (Real.log ‖f 0 x‖ * Matrix.det (fun a b : Fin n ↦
        (fderiv ℝ (f b.succ) x (v (i.succAbove a)) / f b.succ x).re))) =
    Real.log ‖f 0 x‖ * ((-1 : ℝ) ^ i.val * (fderiv ℝ g x (v i) / g x).re *
      Matrix.det (fun a b : Fin n ↦
        (fderiv ℝ (f b.succ) x (v (i.succAbove a)) / f b.succ x).re))
  ring

variable {K : Type*} [Fintype K]

/-- Coefficients are scalars at a point; this construction takes no derivative of them. -/
def combination (c : K → ℝ) (g : K → E → ℂ) (x : E) : E →L[ℝ] ℝ :=
  ∑ k, c k • radialCovector (g k) x

/-- The exact finite determinant expression, before estimates. -/
theorem wedgePrimitive_combination_eq (c : K → ℝ) (f : Fin (n + 1) → E → ℂ)
    (g : K → E → ℂ) (x : E)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (hg : ∀ k, DifferentiableAt ℝ (g k) x)
    (hf0 : ∀ j, f j x ≠ 0) (hg0 : ∀ k, g k x ≠ 0) :
    wedgePrimitive (combination c g x) f x =
      ∑ k, c k • LogRadialPrimitive.primitive (augment f (g k)) x := by
  ext v
  simp only [wedgePrimitive, combination, alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, _root_.sum_apply,
    _root_.smul_apply, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply, smul_eq_mul,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have h := congrArg (fun ω ↦ ω v) (wedgePrimitive_radial_eq f (g k) x hf (hg k) hf0 (hg0 k))
  simp only [wedgePrimitive, alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- An elementary finite-family fact used for the actual units and their exponents. -/
theorem augment_forall {A : Type*} (P : A → Prop) (f : Fin (n + 1) → A) (g : A)
    (hf : ∀ j, P (f j)) (hg : P g) : ∀ j, P (augment f g j) := by
  intro j
  refine Fin.cases (hf 0) (fun j ↦ ?_) j
  exact Fin.cases hg (fun j ↦ hf j.succ) j

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- All assumptions concern the actual local unit functions and a bounded chart
region. The region may be any measurable subset of the punctured polydisc. -/
structure LocalData (J K : Type*) [Fintype J] (n : ℕ) where
  a : Fin (n + 1) → J → ℤ
  b : K → J → ℤ
  u : Fin (n + 1) → (J → ℂ) → ℂ
  q : K → (J → ℂ) → ℂ
  radius : J → ℝ
  region : Set (J → ℂ)
  measurable_region : MeasurableSet region
  region_polydisc : region ⊆ NormalCrossing.puncturedPolydisc radius
  U : Set (J → ℂ)
  open_U : IsOpen U
  region_U : region ⊆ U
  units_C2 : ∀ j, ContDiffOn ℝ 2 (u j) U
  extra_units_C2 : ∀ k, ContDiffOn ℝ 2 (q k) U
  D : ℝ
  c : ℝ
  M : ℝ
  c_pos : 0 < c
  unit_lower : ∀ x ∈ region, ∀ j, c ≤ ‖u j x‖
  extra_unit_lower : ∀ x ∈ region, ∀ k, c ≤ ‖q k x‖
  unit_derivative : ∀ x ∈ region, ∀ j, ‖fderiv ℝ (u j) x‖ ≤ D
  extra_unit_derivative : ∀ x ∈ region, ∀ k, ‖fderiv ℝ (q k) x‖ ≤ D
  first_unit_upper : ∀ x ∈ region, ‖u 0 x‖ ≤ M

variable (d : LocalData J K n)

def baseFunctions : Fin (n + 1) → (J → ℂ) → ℂ :=
  LogMonomial.coordinateMonomial d.a d.u

def extraFunctions : K → (J → ℂ) → ℂ :=
  fun k x ↦ LogMonomial.value (d.b k) (d.q k x) x

/-- The genuine top-form density on a fixed coordinate tangent tuple. -/
def density (c : K → ℝ) (v : Fin (n + 1) → J → ℂ) (x : J → ℂ) : ℝ :=
  wedgePrimitive (combination c (extraFunctions d) x) (baseFunctions d) x v

/-- The determinant summand is itself a native augmented primitive. -/
def coefficient (k : K) (v : Fin (n + 1) → J → ℂ) (x : J → ℂ) : ℝ :=
  LogRadialPrimitive.primitive
    (LogMonomial.coordinateMonomial (augment d.a (d.b k)) (augment d.u (d.q k))) x v

def coefficientBound (k : K) : ℝ :=
  LogMonomial.primitiveIntegrabilityBound (augment d.a (d.b k)) d.D d.c d.M

/-- A finite, explicit numerical constant independent of the varying coefficients. -/
def bound (C : ℝ) : ℝ := C * ∑ k, coefficientBound d k

omit [Fintype K] [DecidableEq J] in
theorem coordinates_ne_zero {x : J → ℂ} (hx : x ∈ d.region) : ∀ ν, x ν ≠ 0 :=
  fun ν ↦ norm_pos_iff.mp ((d.region_polydisc hx ν (mem_univ ν)).1)

omit [Fintype K] [DecidableEq J] in
theorem augmented_units_C2 (k : K) {x : J → ℂ} (hx : x ∈ d.region) :
    ∀ j, ContDiffAt ℝ 2 (augment d.u (d.q k) j) x :=
  augment_forall (fun u ↦ ContDiffAt ℝ 2 u x) d.u (d.q k) (fun j ↦ (d.units_C2 j).contDiffAt (d.open_U.mem_nhds (d.region_U hx)))
    ((d.extra_units_C2 k).contDiffAt (d.open_U.mem_nhds (d.region_U hx)))

omit [Fintype K] [DecidableEq J] in
theorem augmented_units_lower (k : K) {x : J → ℂ} (hx : x ∈ d.region) :
    ∀ j, d.c ≤ ‖augment d.u (d.q k) j x‖ :=
  augment_forall (fun u ↦ d.c ≤ ‖u x‖) d.u (d.q k) (d.unit_lower x hx) (d.extra_unit_lower x hx k)

omit [Fintype K] [DecidableEq J] in
theorem augmented_functions_eq (k : K) :
    LogMonomial.coordinateMonomial (augment d.a (d.b k)) (augment d.u (d.q k)) =
      augment (baseFunctions d) (extraFunctions d k) := by
  funext j
  refine Fin.cases rfl (fun j ↦ ?_) j
  exact Fin.cases rfl (fun _ ↦ rfl) j

omit [DecidableEq J] in
/-- Exact finite sum of actual monomial determinants with the additional row.
The pole cancellation theorem is applied to each whole summand below. -/
theorem density_eq_sum (c : K → ℝ) (v : Fin (n + 1) → J → ℂ)
    {x : J → ℂ} (hx : x ∈ d.region) :
    density d c v x = ∑ k, c k * coefficient d k v x := by
  have hf (j : Fin (n + 1)) : DifferentiableAt ℝ (baseFunctions d j) x :=
    (LogMonomial.contDiffAt_coordinateMonomial d.a d.u j x
      ((d.units_C2 j).contDiffAt (d.open_U.mem_nhds (d.region_U hx)))
      (coordinates_ne_zero d hx)).differentiableAt (by norm_num)
  have hg (k : K) : DifferentiableAt ℝ (extraFunctions d k) x :=
    LogMonomial.differentiableAt_function (d.b k) (d.q k) (fun ν y ↦ y ν)
      (((d.extra_units_C2 k).contDiffAt (d.open_U.mem_nhds (d.region_U hx))).differentiableAt (by norm_num))
      (fun ν ↦ (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ).differentiableAt)
      (coordinates_ne_zero d hx)
  have hf0 (j : Fin (n + 1)) : baseFunctions d j x ≠ 0 :=
    LogMonomial.value_ne_zero _ (norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower x hx j)))
      (coordinates_ne_zero d hx)
  have hg0 (k : K) : extraFunctions d k x ≠ 0 :=
    LogMonomial.value_ne_zero _ (norm_pos_iff.mp (d.c_pos.trans_le (d.extra_unit_lower x hx k)))
      (coordinates_ne_zero d hx)
  rw [density, wedgePrimitive_combination_eq _ _ _ _ hf hg hf0 hg0]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    coefficient, augmented_functions_eq]

omit [Fintype K] [DecidableEq J] in
/-- The original alternating coefficient, before bounding, is the logarithm
multiplier times the actual augmented derivative determinant. -/
theorem coefficient_eq_log_mul_det (k : K) (v : Fin (n + 1) → J → ℂ)
    {x : J → ℂ} (hx : x ∈ d.region) :
    coefficient d k v x = Real.log ‖LogMonomial.value (d.a 0) (d.u 0 x) x‖ *
      Matrix.det (LogMonomial.actualRadialMatrix
        (Fin.cons (d.b k) (fun j : Fin n ↦ d.a j.succ))
        (Fin.cons (d.q k) (fun j : Fin n ↦ d.u j.succ)) v x) := by
  exact LogMonomial.primitive_eq_log_mul_actualDeterminant _ _ v x
    (fun j ↦ (augmented_units_C2 d k hx j).differentiableAt (by norm_num))
    (fun j ↦ norm_pos_iff.mp (d.c_pos.trans_le (augmented_units_lower d k hx j)))
    (coordinates_ne_zero d hx)

omit [Fintype K] in
/-- The determinant theorem cancels repeated radial rows before this estimate.
Only one simple radial pole per normal coordinate survives, despite the extra covector. -/
theorem norm_coefficient_le (k : K) (v : Fin (n + 1) → J → ℂ)
    (hv : ∀ j, ‖v j‖ ≤ 1) {x : J → ℂ} (hx : x ∈ d.region) :
    ‖coefficient d k v x‖ ≤ coefficientBound d k * NormalCrossing.majorant (fun _ : J ↦ 1) x := by
  apply LogMonomial.norm_primitiveCoefficient_le_majorant _ _ _ _
    (fun j ↦ (augmented_units_C2 d k hx j).differentiableAt (by norm_num))
    (coordinates_ne_zero d hx) d.D d.c d.M d.c_pos
  · intro j
    exact augment_forall (fun u ↦ ‖fderiv ℝ u x‖ ≤ d.D) d.u (d.q k)
      (d.unit_derivative x hx) (d.extra_unit_derivative x hx k) j.succ
  · exact augmented_units_lower d k hx
  · exact d.first_unit_upper x hx
  · exact hv

/-- A single integrable majorant independent of the coefficient parameter. -/
theorem norm_density_le (c : K → ℝ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ k, ‖c k‖ ≤ C)
    (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1)
    {x : J → ℂ} (hx : x ∈ d.region) :
    ‖density d c v x‖ ≤ bound d C * NormalCrossing.majorant (fun _ : J ↦ 1) x := by
  rw [density_eq_sum d c v hx]
  calc
    _ ≤ ∑ k, ‖c k * coefficient d k v x‖ := norm_sum_le _ _
    _ ≤ ∑ k, C * (coefficientBound d k * NormalCrossing.majorant (fun _ : J ↦ 1) x) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (hc k) (norm_coefficient_le d k v hv hx) (norm_nonneg _) hC
    _ = _ := by simp only [bound, ← Finset.mul_sum, ← Finset.sum_mul]; ring

omit [Fintype K] [DecidableEq J] in
/-- Continuity comes from the local C2 unit functions, with no regularity input for the density. -/
theorem continuousOn_coefficient (k : K) (v : Fin (n + 1) → J → ℂ) :
    ContinuousOn (coefficient d k v) d.region := by
  intro x hx
  have hC : ContDiffAt ℝ 1
      (LogRadialPrimitive.primitive
        (LogMonomial.coordinateMonomial (augment d.a (d.b k)) (augment d.u (d.q k)))) x := by
    apply CompactMonomialStokes.contDiffAt_primitive_of_C2
    · intro j
      exact LogMonomial.contDiffAt_coordinateMonomial _ _ j x (augmented_units_C2 d k hx j)
        (coordinates_ne_zero d hx)
    · intro j
      exact LogMonomial.value_ne_zero _
        (norm_pos_iff.mp (d.c_pos.trans_le (augmented_units_lower d k hx j)))
        (coordinates_ne_zero d hx)
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ v).continuous.continuousAt.comp
    hC.continuousAt).continuousWithinAt

omit [DecidableEq J] in
/-- Measurability of the actual density needs only measurable scalar coefficients. -/
theorem aestronglyMeasurable_density (c : K → (J → ℂ) → ℝ)
    (hc : ∀ k, AEStronglyMeasurable (c k) (volume.restrict d.region))
    (v : Fin (n + 1) → J → ℂ) :
    AEStronglyMeasurable (fun x ↦ density d (fun k ↦ c k x) v x) (volume.restrict d.region) := by
  have hm : AEStronglyMeasurable (fun x ↦ ∑ k, c k x * coefficient d k v x)
      (volume.restrict d.region) :=
    Finset.aestronglyMeasurable_fun_sum _ (fun k hk ↦ (hc k).mul
      ((continuousOn_coefficient d k v).aestronglyMeasurable d.measurable_region))
  apply hm.congr
  filter_upwards [ae_restrict_mem d.measurable_region] with x hx
  exact (density_eq_sum d (fun k ↦ c k x) v hx).symm

omit [DecidableEq J] in
theorem integrable_majorant (C : ℝ) :
    IntegrableOn (fun x ↦ bound d C * NormalCrossing.majorant (fun _ : J ↦ 1) x) d.region :=
  ((NormalCrossing.integrableOn_majorant (fun _ : J ↦ 1) d.radius).mono_set d.region_polydisc).const_mul _

/-- Actual local L1 of the native wedge coefficient, derived from unit data. -/
theorem integrableOn_density (c : K → (J → ℂ) → ℝ)
    (hc : ∀ k, AEStronglyMeasurable (c k) (volume.restrict d.region))
    (C : ℝ) (hC : 0 ≤ C) (hc_bound : ∀ x ∈ d.region, ∀ k, ‖c k x‖ ≤ C)
    (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x ↦ density d (fun k ↦ c k x) v x) d.region := by
  apply (integrable_majorant d C).mono' (aestronglyMeasurable_density d c hc v)
  filter_upwards [ae_restrict_mem d.measurable_region] with x hx
  exact norm_density_le d _ C hC (hc_bound x hx) v hv hx

variable {T : Type*} {l : Filter T} [l.IsCountablyGenerated]

omit [l.IsCountablyGenerated] [DecidableEq J] in
/-- Pointwise coefficient convergence passes through the finite native determinant expression. -/
theorem tendsto_density (c : T → K → (J → ℂ) → ℝ)
    (v : Fin (n + 1) → J → ℂ) {x : J → ℂ} (hx : x ∈ d.region)
    (hc : ∀ k, Tendsto (fun t ↦ c t k x) l (𝓝 0)) :
    Tendsto (fun t ↦ density d (fun k ↦ c t k x) v x) l (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun k hk ↦ (hc k).mul_const (coefficient d k v x))
  simpa only [density_eq_sum d _ v hx, zero_mul, Finset.sum_const_zero] using h

/-- Dominated convergence for the actual native top-form density on a fixed
bounded chart region. Scalar coefficients need only measurability, a uniform
bound, and pointwise convergence to zero. No coefficient is differentiated. -/
theorem tendsto_integral_density (c : T → K → (J → ℂ) → ℝ)
    (hc_meas : ∀ᶠ t in l, ∀ k, AEStronglyMeasurable (c t k) (volume.restrict d.region))
    (C : ℝ) (hC : 0 ≤ C)
    (hc_bound : ∀ᶠ t in l, ∀ x ∈ d.region, ∀ k, ‖c t k x‖ ≤ C)
    (hc_zero : ∀ x ∈ d.region, ∀ k, Tendsto (fun t ↦ c t k x) l (𝓝 0))
    (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) :
    Tendsto (fun t ↦ ∫ x in d.region, density d (fun k ↦ c t k x) v x) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict d.region) (F := fun t x ↦ density d (fun k ↦ c t k x) v x)
    (f := fun _ ↦ (0 : ℝ))
    (fun x ↦ bound d C * NormalCrossing.majorant (fun _ : J ↦ 1) x)
    (hc_meas.mono (fun t ht ↦ aestronglyMeasurable_density d (c t) ht v))
    (hc_bound.mono (fun t ht ↦ ?_)) (integrable_majorant d C) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem d.measurable_region] with x hx
    exact norm_density_le d _ C hC (ht x hx) v hv hx
  · filter_upwards [ae_restrict_mem d.measurable_region] with x hx
    exact tendsto_density d c v hx (hc_zero x hx)

/-- The same fixed integrable majorant proves convergence in actual local L1. -/
theorem tendsto_integral_norm_density (c : T → K → (J → ℂ) → ℝ)
    (hc_meas : ∀ᶠ t in l, ∀ k, AEStronglyMeasurable (c t k) (volume.restrict d.region))
    (C : ℝ) (hC : 0 ≤ C)
    (hc_bound : ∀ᶠ t in l, ∀ x ∈ d.region, ∀ k, ‖c t k x‖ ≤ C)
    (hc_zero : ∀ x ∈ d.region, ∀ k, Tendsto (fun t ↦ c t k x) l (𝓝 0))
    (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) :
    Tendsto (fun t ↦ ∫ x in d.region, ‖density d (fun k ↦ c t k x) v x‖) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict d.region) (F := fun t x ↦ ‖density d (fun k ↦ c t k x) v x‖)
    (f := fun _ ↦ (0 : ℝ))
    (fun x ↦ bound d C * NormalCrossing.majorant (fun _ : J ↦ 1) x)
    (hc_meas.mono (fun t ht ↦ (aestronglyMeasurable_density d (c t) ht v).norm))
    (hc_bound.mono (fun t ht ↦ ?_)) (integrable_majorant d C) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem d.measurable_region] with x hx
    rw [norm_norm]
    exact norm_density_le d _ C hC (ht x hx) v hv hx
  · filter_upwards [ae_restrict_mem d.measurable_region] with x hx
    simpa only [norm_zero] using (tendsto_density d c v hx (hc_zero x hx)).norm

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination
