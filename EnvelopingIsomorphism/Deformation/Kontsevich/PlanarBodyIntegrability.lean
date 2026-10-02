import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularPrimitive
import EnvelopingIsomorphism.Deformation.Kontsevich.CutoffErrorPullback
import EnvelopingIsomorphism.Deformation.Kontsevich.HolomorphicMonomialForms
import EnvelopingIsomorphism.Deformation.Kontsevich.LocalChartDominatedConvergence

/-! Local L1 for the actual planar body top form. Only top-degree radial
monomial determinants are estimated; no Cartesian L1 of the primitive is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyIntegrability
open Set MeasureTheory Filter ContinuousAlternatingMap
open InteriorFiberAngleSplit
open scoped BigOperators Topology

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

/-- Exactly the local data needed by the body determinant. -/
structure LocalData (J : Type*) [Fintype J] (n : ℕ) where
  a : Fin (n + 1) → J → ℤ
  u : Fin (n + 1) → (J → ℂ) → ℂ
  radius : J → ℝ
  region : Set (J → ℂ)
  measurable_region : MeasurableSet region
  region_polydisc : region ⊆ NormalCrossing.puncturedPolydisc radius
  U : Set (J → ℂ)
  open_U : IsOpen U
  region_U : region ⊆ U
  units_C1 : ∀ j, ContDiffOn ℝ 1 (u j) U
  D : ℝ
  c : ℝ
  c_pos : 0 < c
  unit_lower : ∀ x ∈ region, ∀ j, c ≤ ‖u j x‖
  unit_derivative : ∀ x ∈ region, ∀ j, ‖fderiv ℝ (u j) x‖ ≤ D

/-- The body uses only the base-unit part of the same local data as the error term. -/
def LocalData.ofCombinationData {K : Type*}
    (d : BoundedLogMonomialCombination.LocalData J K n) : LocalData J n where
  a := d.a
  u := d.u
  radius := d.radius
  region := d.region
  measurable_region := d.measurable_region
  region_polydisc := d.region_polydisc
  U := d.U
  open_U := d.open_U
  region_U := d.region_U
  units_C1 := fun j ↦ (d.units_C2 j).of_le (by norm_num)
  D := d.D
  c := d.c
  c_pos := d.c_pos
  unit_lower := d.unit_lower
  unit_derivative := d.unit_derivative

def functions (d : LocalData J n) := LogMonomial.coordinateMonomial d.a d.u

def density (d : LocalData J n) (v : Fin (n + 1) → J → ℂ) (x : J → ℂ) : ℝ :=
  Matrix.det (LogMonomial.actualRadialMatrix d.a d.u v x)

def bound (d : LocalData J n) : ℝ := LogMonomial.uniformDeterminantBound d.a d.D d.c

variable (d : LocalData J n)

theorem coordinates_ne_zero {x : J → ℂ} (hx : x ∈ d.region) : ∀ j, x j ≠ 0 :=
  fun j ↦ norm_pos_iff.mp ((d.region_polydisc hx j (mem_univ j)).1)

theorem units_C1_at {x : J → ℂ} (hx : x ∈ d.region) (j : Fin (n + 1)) :
    ContDiffAt ℝ 1 (d.u j) x := (d.units_C1 j).contDiffAt (d.open_U.mem_nhds (d.region_U hx))

theorem functions_C1_at {x : J → ℂ} (hx : x ∈ d.region) (j : Fin (n + 1)) :
    ContDiffAt ℝ 1 (functions d j) x :=
  LogMonomial.contDiffAt_coordinateMonomial d.a d.u j x (units_C1_at d hx j) (coordinates_ne_zero d hx)

theorem functions_ne_zero {x : J → ℂ} (hx : x ∈ d.region) (j : Fin (n + 1)) :
    functions d j x ≠ 0 := LogMonomial.value_ne_zero _
      (norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower x hx j))) (coordinates_ne_zero d hx)

/-- Repeated normal rows cancel before the bound, leaving one simple pole per coordinate. -/
theorem norm_density_le (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1)
    {x : J → ℂ} (hx : x ∈ d.region) :
    ‖density d v x‖ ≤ bound d * NormalCrossing.majorant (fun _ : J ↦ 0) x := by
  have h := LogMonomial.abs_actualRadialMatrix_det_le d.a d.u v
    (fun j ↦ (units_C1_at d hx j).differentiableAt (by norm_num))
    (fun j ↦ norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower x hx j))) (coordinates_ne_zero d hx)
  have hb := LogMonomial.coefficientBound_le_unitBounds d.a d.u v x d.D d.c d.c_pos
    (d.unit_derivative x hx) (d.unit_lower x hx) hv
  change |Matrix.det (LogMonomial.actualRadialMatrix d.a d.u v x)| ≤ _
  apply h.trans
  have hp : 0 ≤ ∏ j : J, max 1 (1 / ‖x j‖) :=
    Finset.prod_nonneg (fun j _ ↦ le_trans zero_le_one (le_max_left (1 : ℝ) _))
  simpa [bound, NormalCrossing.majorant, NormalCrossing.factor] using
    mul_le_mul_of_nonneg_right hb hp

theorem continuousOn_density (v : Fin (n + 1) → J → ℂ) : ContinuousOn (density d v) d.region := by
  intro x hx
  have hm (i j : Fin (n + 1)) : ContinuousAt
      (fun y ↦ (fderiv ℝ (functions d i) y (v j) / functions d i y).re) x :=
    Complex.continuous_re.continuousAt.comp
      ((((functions_C1_at d hx i).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).div
        (functions_C1_at d hx i).continuousAt (functions_ne_zero d hx i))
  change ContinuousWithinAt (fun y ↦ Matrix.det
    (fun i j : Fin (n + 1) ↦ (fderiv ℝ (functions d i) y (v j) / functions d i y).re)) d.region x
  exact ((continuous_id.matrix_det.continuousAt.comp (continuousAt_pi.mpr (fun i ↦ continuousAt_pi.mpr (hm i))))).continuousWithinAt

/-- An actual integrable simple-pole majorant on any measurable bounded chart region. -/
theorem integrable_majorant : IntegrableOn
    (fun x ↦ bound d * NormalCrossing.majorant (fun _ : J ↦ 0) x) d.region :=
  ((NormalCrossing.integrableOn_majorant (fun _ : J ↦ 0) d.radius).mono_set d.region_polydisc).const_mul _

theorem integrableOn_density (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (density d v) d.region := by
  apply (integrable_majorant d).mono'
    ((continuousOn_density d v).aestronglyMeasurable d.measurable_region)
  filter_upwards [ae_restrict_mem d.measurable_region] with x hx
  exact norm_density_le d v hv hx

/-- Any measurable bounded chart weight preserves the derived local body L1. -/
theorem integrableOn_weighted_density (v : Fin (n + 1) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1)
    (w : (J → ℂ) → ℝ) (hw : AEStronglyMeasurable w (volume.restrict d.region))
    (hw1 : ∀ x ∈ d.region, ‖w x‖ ≤ 1) :
    IntegrableOn (fun x ↦ w x * density d v x) d.region := by
  apply (integrableOn_density d v hv).norm.mono'
    (hw.mul ((continuousOn_density d v).aestronglyMeasurable d.measurable_region))
  filter_upwards [ae_restrict_mem d.measurable_region] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw1 x hx)

/-- Exact native pullback of the actual body dβ, derived from complex function identities. -/
theorem body_pullback_eq_density {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (d : LocalData J (NormalCrossingStokes.Degree N))
    {F : (J → ℂ) → NormalCrossingStokes.Space N} {x : J → ℂ}
    (hF : DifferentiableAt ℝ F x) (hx : F x ∈ shapeConfiguration (N + 1))
    {U : Set (J → ℂ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hid : ∀ j, ∀ y ∈ U, RatioCutoffStokes.edgeFunctions e j (F y) = functions d j y)
    (v : Fin (NormalCrossingStokes.Dim N) → J → ℂ) :
    ((extDeriv (RatioCutoffStokes.beta e) (F x)).compContinuousLinearMap (fderiv ℝ F x)) v =
      density d v x := by
  rw [RatioCutoffStokes.extDeriv_beta e he hx, compContinuousLinearMap_apply,
    LogRadialPrimitive.radialForm_apply]
  have hc (j : Fin (NormalCrossingStokes.Dim N)) :
      (fun y ↦ RatioCutoffStokes.edgeFunctions e j (F y)) =ᶠ[𝓝 x] functions d j := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hid j y hy
  have hd (j : Fin (NormalCrossingStokes.Dim N)) :
      fderiv ℝ (functions d j) x =
        (fderiv ℝ (RatioCutoffStokes.edgeFunctions e j) (F x)).comp (fderiv ℝ F x) := by
    rw [← (hc j).fderiv_eq]
    exact fderiv_comp x (hasFDerivAt_shapeDifference _ _ (F x)).differentiableAt hF
  rw [density, ← Matrix.det_transpose]
  congr 1
  funext i j
  change (fderiv ℝ (RatioCutoffStokes.edgeFunctions e i) (F x) (fderiv ℝ F x (v j)) /
    RatioCutoffStokes.edgeFunctions e i (F x)).re =
    (fderiv ℝ (functions d i) x (v j) / functions d i x).re
  rw [hd, (hc i).eq_of_nhds]
  rfl

/-- Local L1 of the actual pulled-back body, without primitive integrability. -/
theorem integrableOn_body_pullback {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2)
    (d : LocalData J (NormalCrossingStokes.Degree N))
    (F : (J → ℂ) → NormalCrossingStokes.Space N)
    (hF : ∀ x ∈ d.region, DifferentiableAt ℝ F x)
    (hX : ∀ x ∈ d.region, F x ∈ shapeConfiguration (N + 1))
    {U : Set (J → ℂ)} (hU : IsOpen U) (hregion : d.region ⊆ U)
    (hid : ∀ j, ∀ y ∈ U, RatioCutoffStokes.edgeFunctions e j (F y) = functions d j y)
    (v : Fin (NormalCrossingStokes.Dim N) → J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x ↦ ((extDeriv (RatioCutoffStokes.beta e) (F x)).compContinuousLinearMap
      (fderiv ℝ F x)) v) d.region := by
  apply (integrableOn_density d v hv).congr_fun _ d.measurable_region
  intro x hx
  exact (body_pullback_eq_density e he d (hF x hx) (hX x hx) hU (hregion hx) hid v).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyIntegrability
