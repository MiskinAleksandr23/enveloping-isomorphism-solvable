import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Group.Indicator

/-! Genuine polar change of variables on complex annuli, including L¹ transfer,
the finite-coordinate rectangle, and removal of the inner radial cutoff.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PolarAnnulus

open MeasureTheory Set Filter Metric
open scoped Topology

def annulus (ε R : ℝ) : Set ℂ := {z | ε < ‖z‖ ∧ ‖z‖ < R}
def rectangle (ε R : ℝ) : Set (ℝ × ℝ) := Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi
def polarFin (x : Fin 2 → ℝ) : ℂ := Complex.polarCoord.symm (x 0, x 1)
def finRectangle (ε R : ℝ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi (fun i ↦ Ioo (![ε, -Real.pi] i) (![R, Real.pi] i))

theorem measurableSet_annulus (ε R : ℝ) : MeasurableSet (annulus ε R) :=
  ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet

theorem measurableSet_rectangle (ε R : ℝ) : MeasurableSet (rectangle ε R) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem rectangle_subset_polarTarget {ε R : ℝ} (hε : 0 ≤ ε) : rectangle ε R ⊆ polarCoord.target := by
  intro p hp
  exact ⟨lt_of_le_of_lt hε hp.1.1, hp.2⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The native Jacobian theorem also transfers integrability, with no measurability shortcut. -/
theorem integrable_polar_iff (f : ℂ → V) :
    Integrable f ↔ IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p)) polarCoord.target := by
  have hc := (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (g := f)
  have hj := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (ℝ × ℝ))
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn
    (f ∘ Complex.measurableEquivRealProd.symm)
  rw [polarCoord.symm_image_target_eq_source] at hj
  have hsource : (volume : Measure (ℝ × ℝ)).restrict polarCoord.source = volume := by
    rw [Measure.restrict_congr_set polarCoord_source_ae_eq_univ, Measure.restrict_univ]
  change Integrable (f ∘ Complex.measurableEquivRealProd.symm)
    ((volume : Measure (ℝ × ℝ)).restrict polarCoord.source) ↔ _ at hj
  rw [hsource] at hj
  refine hc.symm.trans (hj.trans (integrable_congr ?_))
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
  rfl

theorem polar_indicator_eq (ε R : ℝ) (f : ℂ → V) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (annulus ε R).indicator f (Complex.polarCoord.symm p) =
      (rectangle ε R).indicator (fun q ↦ q.1 • f (Complex.polarCoord.symm q)) p := by
  classical
  have hm : Complex.polarCoord.symm p ∈ annulus ε R ↔ p ∈ rectangle ε R := by
    have hr : 0 < p.1 := hp.1
    change (ε < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ < R) ↔
      (ε < p.1 ∧ p.1 < R) ∧ (-Real.pi < p.2 ∧ p.2 < Real.pi)
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    exact ⟨fun h ↦ ⟨h, hp.2⟩, fun h ↦ h.1⟩
  by_cases h : Complex.polarCoord.symm p ∈ annulus ε R
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hm.mpr h), smul_zero]

/-- Actual polar-annulus change of variables. Radius is positive on the rectangle,
so the absolute Jacobian is exactly r with the standard complex coordinate orientation. -/
theorem integral_annulus_eq_polar (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    (∫ z in annulus ε R, f z) =
      ∫ p in rectangle ε R, p.1 • f (Complex.polarCoord.symm p) := by
  rw [← integral_indicator (measurableSet_annulus ε R), ← Complex.integral_comp_polarCoord_symm]
  calc
    _ = ∫ p in polarCoord.target,
        (rectangle ε R).indicator (fun q ↦ q.1 • f (Complex.polarCoord.symm q)) p :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet (polar_indicator_eq ε R f)
    _ = _ := by
      rw [setIntegral_indicator (measurableSet_rectangle ε R),
        Set.inter_eq_right.mpr (rectangle_subset_polarTarget hε)]

/-- L¹ is equivalent on the actual annulus and the polar rectangle, including the Jacobian. -/
theorem integrableOn_annulus_iff_polar (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    IntegrableOn f (annulus ε R) ↔
      IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p)) (rectangle ε R) := by
  rw [← integrable_indicator_iff (measurableSet_annulus ε R), integrable_polar_iff]
  calc
    _ ↔ IntegrableOn ((rectangle ε R).indicator
        (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))) polarCoord.target := by
      apply integrable_congr
      filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
      exact polar_indicator_eq ε R f p hp
    _ ↔ _ := by
      rw [integrableOn_indicator_iff (measurableSet_rectangle ε R),
        Set.inter_eq_left.mpr (rectangle_subset_polarTarget hε)]

theorem finTwoArrow_preimage_rectangle (ε R : ℝ) :
    MeasurableEquiv.finTwoArrow ⁻¹' rectangle ε R = finRectangle ε R := by
  ext x
  simp [rectangle, finRectangle, Fin.forall_fin_two]

/-- The exact Fin 2 coordinate formula consumed by rectangle Stokes. -/
theorem integral_annulus_eq_finRectangle (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    (∫ z in annulus ε R, f z) = ∫ x in finRectangle ε R, x 0 • f (polarFin x) := by
  rw [integral_annulus_eq_polar ε R hε]
  have h := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p)) (rectangle ε R)
  rw [finTwoArrow_preimage_rectangle] at h
  exact h.symm

theorem integrableOn_annulus_iff_finRectangle (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    IntegrableOn f (annulus ε R) ↔
      IntegrableOn (fun x : Fin 2 → ℝ ↦ x 0 • f (polarFin x)) (finRectangle ε R) := by
  rw [integrableOn_annulus_iff_polar ε R hε]
  have h := (volume_preserving_finTwoArrow ℝ).integrableOn_comp_preimage
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (f := fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p)) (s := rectangle ε R)
  rw [finTwoArrow_preimage_rectangle] at h
  exact h.symm

/-- The componentwise open rectangle differs from the closed box only by null faces. -/
theorem finRectangle_ae_eq_closed (ε R : ℝ) :
    finRectangle ε R =ᵐ[volume] Icc ![ε, -Real.pi] ![R, Real.pi] := by
  change (Set.univ.pi (fun i : Fin 2 ↦ Ioo (![ε, -Real.pi] i) (![R, Real.pi] i))) =ᵐ[volume] _
  rw [volume_pi]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

theorem integral_annulus_eq_closedFinRectangle (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    (∫ z in annulus ε R, f z) =
      ∫ x in Icc ![ε, -Real.pi] ![R, Real.pi], x 0 • f (polarFin x) := by
  rw [integral_annulus_eq_finRectangle ε R hε]
  exact setIntegral_congr_set (finRectangle_ae_eq_closed ε R)

theorem integrableOn_annulus_iff_closedFinRectangle (ε R : ℝ) (hε : 0 ≤ ε) (f : ℂ → V) :
    IntegrableOn f (annulus ε R) ↔
      IntegrableOn (fun x : Fin 2 → ℝ ↦ x 0 • f (polarFin x))
        (Icc ![ε, -Real.pi] ![R, Real.pi]) := by
  rw [integrableOn_annulus_iff_finRectangle ε R hε]
  unfold IntegrableOn
  rw [Measure.restrict_congr_set (finRectangle_ae_eq_closed ε R)]

/-- Remove the inner radial disc, retaining arbitrary values of f elsewhere. -/
def innerCutoff (ε : ℝ) (f : ℂ → V) : ℂ → V := {z : ℂ | ε < ‖z‖}.indicator f

theorem measurableSet_innerCutoff (ε : ℝ) : MeasurableSet {z : ℂ | ε < ‖z‖} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

omit [NormedSpace ℝ V] in
theorem integrableOn_innerCutoff (R ε : ℝ) (f : ℂ → V)
    (hf : IntegrableOn f (ball 0 R)) : IntegrableOn (innerCutoff ε f) (ball 0 R) :=
  hf.indicator (measurableSet_innerCutoff ε)

theorem integral_innerCutoff_eq_annulus (R ε : ℝ) (f : ℂ → V) :
    (∫ z in ball 0 R, innerCutoff ε f z) = ∫ z in annulus ε R, f z := by
  rw [innerCutoff, setIntegral_indicator (measurableSet_innerCutoff ε)]
  have hs : ball (0 : ℂ) R ∩ {z : ℂ | ε < ‖z‖} = annulus ε R := by
    ext z
    simp only [annulus, mem_inter_iff, mem_ball, dist_zero_right, mem_setOf_eq]
    exact and_comm
  rw [hs]

omit [NormedSpace ℝ V] in
theorem integrableOn_annulus_of_ball (R ε : ℝ) (f : ℂ → V)
    (hf : IntegrableOn f (ball 0 R)) : IntegrableOn f (annulus ε R) := by
  apply hf.mono_set
  intro z hz
  simpa only [mem_ball, dist_zero_right] using hz.2

omit [NormedSpace ℝ V] in
theorem tendsto_innerCutoff_value (f : ℂ → V) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun ε : ℝ ↦ innerCutoff ε f z) (𝓝[>] 0) (𝓝 (f z)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ‖z‖ :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖z‖ from Iio_mem_nhds (norm_pos_iff.mpr hz)).filter_mono
      nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with ε hε
  have hzmem : z ∈ {w : ℂ | ε < ‖w‖} := hε
  exact (Set.indicator_of_mem hzmem f).symm

private theorem ae_ne_zero_on_ball (R : ℝ) :
    ∀ᵐ z : ℂ ∂((volume : Measure ℂ).restrict (ball 0 R)), z ≠ 0 := by
  apply ae_restrict_of_ae
  simp [ae_iff]

omit [NormedSpace ℝ V] in
/-- Actual L¹ convergence of the inner-cutoff functions on the fixed outer disc. -/
theorem tendsto_innerCutoff_L1 (R : ℝ) (f : ℂ → V) (hf : IntegrableOn f (ball 0 R)) :
    Tendsto (fun ε : ℝ ↦ ∫ z in ball 0 R, ‖innerCutoff ε f z - f z‖)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure ℂ).restrict (ball 0 R))
    (F := fun ε z ↦ ‖innerCutoff ε f z - f z‖)
    (f := fun _ ↦ (0 : ℝ)) (fun z ↦ 2 * ‖f z‖)
    (Filter.Eventually.of_forall (fun ε ↦
      ((hf.aestronglyMeasurable.indicator (measurableSet_innerCutoff ε)).sub hf.aestronglyMeasurable).norm))
    (Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall (fun z ↦ ?_)))
    (hf.norm.const_mul 2) ?_
  · simpa only [integral_zero] using h
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖innerCutoff ε f z - f z‖ ≤ ‖innerCutoff ε f z‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ ‖f z‖ + ‖f z‖ :=
        add_le_add (norm_indicator_le_norm_self (s := {w : ℂ | ε < ‖w‖}) (f := f) (a := z)) le_rfl
      _ = 2 * ‖f z‖ := (two_mul _).symm
  · filter_upwards [ae_ne_zero_on_ball R] with z hz
    have hh : Tendsto (fun ε : ℝ ↦ innerCutoff ε f z - f z) (𝓝[>] 0) (𝓝 (f z - f z)) :=
      (tendsto_innerCutoff_value f hz).sub tendsto_const_nhds
    simpa only [sub_self, norm_zero] using hh.norm

/-- An L¹ function on the fixed outer disc has the genuine annulus-integral limit. -/
theorem tendsto_integral_annulus (R : ℝ) (f : ℂ → V) (hf : IntegrableOn f (ball 0 R)) :
    Tendsto (fun ε : ℝ ↦ ∫ z in annulus ε R, f z) (𝓝[>] 0)
      (𝓝 (∫ z in ball 0 R, f z)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure ℂ).restrict (ball 0 R))
    (F := fun ε ↦ innerCutoff ε f)
    (f := f) (fun z ↦ ‖f z‖)
    (Filter.Eventually.of_forall (fun ε ↦ hf.aestronglyMeasurable.indicator (measurableSet_innerCutoff ε)))
    (Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall (fun z ↦
      norm_indicator_le_norm_self (f := f) (a := z)))) hf.norm ?_
  · simpa only [integral_innerCutoff_eq_annulus] using h
  · filter_upwards [ae_ne_zero_on_ball R] with z hz
    exact tendsto_innerCutoff_value f hz

/-- A supported L¹ coefficient has the whole-plane integral as its cutoff limit. -/
theorem tendsto_integral_annulus_of_support (R : ℝ) (f : ℂ → V) (hf : Integrable f)
    (hsupp : ∀ z, R ≤ ‖z‖ → f z = 0) :
    Tendsto (fun ε : ℝ ↦ ∫ z in annulus ε R, f z) (𝓝[>] 0) (𝓝 (∫ z, f z)) := by
  have he : (∫ z in ball 0 R, f z) = ∫ z, f z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ hsupp z (by
      simpa only [mem_ball, dist_zero_right, not_lt] using hz))
  rw [← he]
  exact tendsto_integral_annulus R f hf.integrableOn

end EnvelopingIsomorphism.Deformation.Kontsevich.PolarAnnulus
