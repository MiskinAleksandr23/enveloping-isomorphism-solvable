import EnvelopingIsomorphism.Deformation.Kontsevich.UnorientedFormIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Local dominated convergence on a finite collection of actual injective C1
charts implies L1 convergence on the original domain. All norm integral
identities are derived from the native absolute-Jacobian change of variables.
The partition weights need no Cartesian derivatives. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LocalChartDominatedConvergence

open Set MeasureTheory Filter BoxStokes OrientedFormChangeVariables
open scoped BigOperators Topology

variable {d : ℕ} {J : Type*} [Fintype J]

/-- A finite measurable partition on an open original domain, subordinate to
actual injective C1 chart images. No integrability or convergence is bundled. -/
structure ChartCover (d : ℕ) (J : Type*) [Fintype J] where
  domain : Set (Coord d)
  open_domain : IsOpen domain
  chart : J → Coord d → Coord d
  source : J → Set (Coord d)
  measurable_source : ∀ j, MeasurableSet (source j)
  chart_C1 : ∀ j, ∀ x ∈ source j, ContDiffAt ℝ 1 (chart j) x
  chart_injective : ∀ j, InjOn (chart j) (source j)
  image_domain : ∀ j, chart j '' source j ⊆ domain
  weight : J → Coord d → ℝ
  weight_nonneg : ∀ y ∈ domain, ∀ j, 0 ≤ weight j y
  sum_weight : ∀ y ∈ domain, ∑ j, weight j y = 1
  weight_zero : ∀ j, ∀ y ∈ domain, y ∉ chart j '' source j → weight j y = 0

variable (c : ChartCover d J)

/-- A partition piece on the original coordinates. -/
def piece (f : Coord d → ℝ) (j : J) (y : Coord d) : ℝ := c.weight j y * f y

/-- The actual signed coefficient times the absolute Jacobian of its chart. -/
def sourceSigned (f : Coord d → ℝ) (j : J) (x : Coord d) : ℝ :=
  |jacobian (c.chart j) x| * piece c f j (c.chart j x)

/-- The local source norm density appearing in actual change of variables. -/
def sourceNorm (f : Coord d → ℝ) (j : J) (x : Coord d) : ℝ :=
  |jacobian (c.chart j) x| * ‖piece c f j (c.chart j x)‖

theorem norm_sourceSigned (f : Coord d → ℝ) (j : J) (x : Coord d) :
    ‖sourceSigned c f j x‖ = sourceNorm c f j x := by
  simp only [sourceSigned, sourceNorm, norm_mul, Real.norm_eq_abs, abs_abs]

theorem sourceNorm_nonneg (f : Coord d → ℝ) (j : J) (x : Coord d) :
    0 ≤ sourceNorm c f j x := mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem hasFDerivWithinAt_chart (j : J) (x : Coord d) (hx : x ∈ c.source j) :
    HasFDerivWithinAt (c.chart j) (fderiv ℝ (c.chart j) x) (c.source j) x :=
  ((c.chart_C1 j x hx).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt

/-- The original-domain L1 question is exactly the local signed source L1
question, by the actual absolute-Jacobian change of variables and support. -/
theorem integrableOn_piece_iff (f : Coord d → ℝ) (j : J) :
    IntegrableOn (piece c f j) c.domain ↔ IntegrableOn (sourceSigned c f j) (c.source j) := by
  have hcv := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (c.measurable_source j) (hasFDerivWithinAt_chart c j) (c.chart_injective j) (piece c f j)
  have he : IntegrableOn (piece c f j) c.domain ↔
      IntegrableOn (piece c f j) (c.chart j '' c.source j) := by
    constructor
    · exact fun h ↦ h.mono_set (c.image_domain j)
    · intro h
      apply h.of_forall_sdiff_eq_zero c.open_domain.measurableSet
      intro y hy
      simp only [piece, c.weight_zero j y hy.1 hy.2, zero_mul]
  apply he.trans
  change IntegrableOn (piece c f j) (c.chart j '' c.source j) ↔
    IntegrableOn (fun x ↦ |(fderiv ℝ (c.chart j) x).det| * piece c f j (c.chart j x)) (c.source j)
  simpa only [smul_eq_mul] using hcv

/-- This exact norm integral identity is a conclusion of native change of
variables. It is never a local-to-global hypothesis. -/
theorem integral_norm_piece_eq_source (f : Coord d → ℝ) (j : J) :
    (∫ y in c.domain, ‖piece c f j y‖) = ∫ x in c.source j, sourceNorm c f j x := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero c.open_domain.measurableSet
    (c.image_domain j) (fun y hy ↦ ?_)]
  · simpa only [sourceNorm, jacobian, smul_eq_mul] using
      integral_image_eq_integral_abs_det_fderiv_smul volume (c.measurable_source j)
        (hasFDerivWithinAt_chart c j) (c.chart_injective j) (fun y ↦ ‖piece c f j y‖)
  · simp only [piece, c.weight_zero j y hy.1 hy.2, zero_mul, norm_zero]

theorem sum_piece (f : Coord d → ℝ) {y : Coord d} (hy : y ∈ c.domain) :
    ∑ j, piece c f j y = f y := by
  simp only [piece, ← Finset.sum_mul, c.sum_weight y hy, one_mul]

/-- Nonnegative partition weights also partition the norm exactly. -/
theorem sum_norm_piece (f : Coord d → ℝ) {y : Coord d} (hy : y ∈ c.domain) :
    ∑ j, ‖piece c f j y‖ = ‖f y‖ := by
  simp only [piece, norm_mul, Real.norm_eq_abs, abs_of_nonneg (c.weight_nonneg y hy _),
    ← Finset.sum_mul, c.sum_weight y hy, one_mul]

/-- Finite local L1 transported by actual charts proves original-domain L1. -/
theorem integrableOn_of_sourceSigned (f : Coord d → ℝ)
    (hf : ∀ j, IntegrableOn (sourceSigned c f j) (c.source j)) : IntegrableOn f c.domain := by
  have hsum : IntegrableOn (fun y ↦ ∑ j, piece c f j y) c.domain :=
    integrable_finsetSum Finset.univ (fun j hj ↦ (integrableOn_piece_iff c f j).mpr (hf j))
  exact hsum.congr_fun (fun y hy ↦ sum_piece c f hy) c.open_domain.measurableSet

/-- A finite sum of genuine source norm integrals is the original norm integral. -/
theorem integral_norm_eq_sum_source (f : Coord d → ℝ)
    (hf : ∀ j, IntegrableOn (sourceSigned c f j) (c.source j)) :
    (∫ y in c.domain, ‖f y‖) = ∑ j, ∫ x in c.source j, sourceNorm c f j x := by
  calc
    (∫ y in c.domain, ‖f y‖) = ∫ y in c.domain, ∑ j, ‖piece c f j y‖ :=
      setIntegral_congr_fun c.open_domain.measurableSet (fun y hy ↦ (sum_norm_piece c f hy).symm)
    _ = ∑ j, ∫ y in c.domain, ‖piece c f j y‖ :=
      integral_finsetSum Finset.univ (fun j hj ↦ ((integrableOn_piece_iff c f j).mpr (hf j)).norm)
    _ = _ := Finset.sum_congr rfl (fun j hj ↦ integral_norm_piece_eq_source c f j)

variable {T : Type*} {l : Filter T} [l.IsCountablyGenerated]

/-- Only local measurability of signed source coefficients is required. It
implies measurability of their norm densities; absolute-value measurability
alone would not suffice to prove signed integrability. -/
structure LocalDomination (f : T → Coord d → ℝ) where
  majorant : J → Coord d → ℝ
  integrable_majorant : ∀ j, IntegrableOn (majorant j) (c.source j)
  measurable : ∀ t j, AEStronglyMeasurable (sourceSigned c (f t) j) (volume.restrict (c.source j))
  dominated : ∀ t j, ∀ᵐ x ∂(volume.restrict (c.source j)), sourceNorm c (f t) j x ≤ majorant j x
  tendsto_zero : ∀ j, ∀ᵐ x ∂(volume.restrict (c.source j)),
    Tendsto (fun t ↦ sourceNorm c (f t) j x) l (𝓝 0)

variable (f : T → Coord d → ℝ) (h : LocalDomination c (l := l) f)

include h

/-- Each signed local source is L1 by the supplied genuine local majorant. -/
theorem integrableOn_sourceSigned (t : T) (j : J) :
    IntegrableOn (sourceSigned c (f t) j) (c.source j) :=
  (h.integrable_majorant j).mono' (h.measurable t j)
    ((h.dominated t j).mono (fun x hx ↦ (norm_sourceSigned c (f t) j x).trans_le hx))

/-- Each partition piece is actually L1 on the original domain. -/
theorem integrableOn_piece (t : T) (j : J) : IntegrableOn (piece c (f t) j) c.domain :=
  (integrableOn_piece_iff c (f t) j).mpr (integrableOn_sourceSigned c f h t j)

/-- The original family is L1, assembled from finite local source estimates. -/
theorem integrableOn_family (t : T) : IntegrableOn (f t) c.domain :=
  integrableOn_of_sourceSigned c (f t) (integrableOn_sourceSigned c f h t)

/-- Native local DCT on one fixed chart source. -/
theorem tendsto_integral_sourceNorm (j : J) :
    Tendsto (fun t ↦ ∫ x in c.source j, sourceNorm c (f t) j x) l (𝓝 0) := by
  have hm (t : T) : AEStronglyMeasurable (sourceNorm c (f t) j)
      (volume.restrict (c.source j)) := by
    have he : sourceNorm c (f t) j = fun x ↦ ‖sourceSigned c (f t) j x‖ :=
      funext (fun x ↦ (norm_sourceSigned c (f t) j x).symm)
    rw [he]
    exact (h.measurable t j).norm
  have hd (t : T) : ∀ᵐ x ∂(volume.restrict (c.source j)),
      ‖sourceNorm c (f t) j x‖ ≤ h.majorant j x := by
    filter_upwards [h.dominated t j] with x hx
    simpa only [Real.norm_of_nonneg (sourceNorm_nonneg c (f t) j x)] using hx
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (c.source j)) (F := fun t x ↦ sourceNorm c (f t) j x)
    (f := fun _ ↦ (0 : ℝ)) (h.majorant j) (Eventually.of_forall hm) (Eventually.of_forall hd)
    (h.integrable_majorant j) (h.tendsto_zero j)
  simpa only [integral_zero] using hh

/-- Each original partition piece tends to zero in L1 by actual change of variables. -/
theorem tendsto_integral_norm_piece (j : J) :
    Tendsto (fun t ↦ ∫ y in c.domain, ‖piece c (f t) j y‖) l (𝓝 0) := by
  simpa only [integral_norm_piece_eq_source] using tendsto_integral_sourceNorm c f h j

/-- Actual L1 convergence on the original domain, with no global majorant,
no assumed global convergence, and no assumed integral transport identity. -/
theorem tendsto_integral_norm :
    Tendsto (fun t ↦ ∫ y in c.domain, ‖f t y‖) l (𝓝 0) := by
  have hh := tendsto_finsetSum Finset.univ (fun j hj ↦ tendsto_integral_sourceNorm c f h j)
  have he (t : T) := integral_norm_eq_sum_source c (f t) (integrableOn_sourceSigned c f h t)
  simpa only [← he, Finset.sum_const_zero] using hh

/-- Signed integrals vanish as a consequence of the proved original-domain L1 convergence. -/
theorem tendsto_integral : Tendsto (fun t ↦ ∫ y in c.domain, f t y) l (𝓝 0) := by
  apply squeeze_zero_norm (fun t ↦ norm_integral_le_integral_norm (f t))
    (tendsto_integral_norm c f h)

omit h in
/-- Norm integrability itself needs only the unsigned source measurability,
without imposing any unproved measurability of the sign of the target. -/
theorem integrableOn_norm_piece_iff (f : Coord d → ℝ) (j : J) :
    IntegrableOn (fun y ↦ ‖piece c f j y‖) c.domain ↔
      IntegrableOn (sourceNorm c f j) (c.source j) := by
  have hcv := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (c.measurable_source j) (hasFDerivWithinAt_chart c j) (c.chart_injective j)
    (fun y ↦ ‖piece c f j y‖)
  have he : IntegrableOn (fun y ↦ ‖piece c f j y‖) c.domain ↔
      IntegrableOn (fun y ↦ ‖piece c f j y‖) (c.chart j '' c.source j) := by
    constructor
    · exact fun h ↦ h.mono_set (c.image_domain j)
    · intro h
      apply h.of_forall_sdiff_eq_zero c.open_domain.measurableSet
      intro y hy
      simp only [piece, c.weight_zero j y hy.1 hy.2, zero_mul, norm_zero]
  apply he.trans
  change IntegrableOn (fun y ↦ ‖piece c f j y‖) (c.chart j '' c.source j) ↔
    IntegrableOn (fun x ↦ |(fderiv ℝ (c.chart j) x).det| * ‖piece c f j (c.chart j x)‖) (c.source j)
  simpa only [smul_eq_mul] using hcv

omit h in
theorem integrableOn_norm_of_sourceNorm (f : Coord d → ℝ)
    (hf : ∀ j, IntegrableOn (sourceNorm c f j) (c.source j)) :
    IntegrableOn (fun y ↦ ‖f y‖) c.domain := by
  have hsum : IntegrableOn (fun y ↦ ∑ j, ‖piece c f j y‖) c.domain :=
    integrable_finsetSum Finset.univ (fun j hj ↦ (integrableOn_norm_piece_iff c f j).mpr (hf j))
  exact hsum.congr_fun (fun y hy ↦ sum_norm_piece c f hy) c.open_domain.measurableSet

omit h in
theorem integral_norm_eq_sum_of_sourceNorm (f : Coord d → ℝ)
    (hf : ∀ j, IntegrableOn (sourceNorm c f j) (c.source j)) :
    (∫ y in c.domain, ‖f y‖) = ∑ j, ∫ x in c.source j, sourceNorm c f j x := by
  calc
    (∫ y in c.domain, ‖f y‖) = ∫ y in c.domain, ∑ j, ‖piece c f j y‖ :=
      setIntegral_congr_fun c.open_domain.measurableSet (fun y hy ↦ (sum_norm_piece c f hy).symm)
    _ = ∑ j, ∫ y in c.domain, ‖piece c f j y‖ :=
      integral_finsetSum Finset.univ (fun j hj ↦ (integrableOn_norm_piece_iff c f j).mpr (hf j))
    _ = _ := Finset.sum_congr rfl (fun j hj ↦ integral_norm_piece_eq_source c f j)

omit h in
/-- The global norm integral converges using only unsigned local data. Signed
integrability is separately established above from local signed measurability. -/
theorem norm_convergence_of_local_norm_domination
    (g : J → Coord d → ℝ) (hg : ∀ j, IntegrableOn (g j) (c.source j))
    (hm : ∀ t j, AEStronglyMeasurable (sourceNorm c (f t) j) (volume.restrict (c.source j)))
    (hb : ∀ t j, ∀ᵐ x ∂(volume.restrict (c.source j)), sourceNorm c (f t) j x ≤ g j x)
    (hz : ∀ j, ∀ᵐ x ∂(volume.restrict (c.source j)),
      Tendsto (fun t ↦ sourceNorm c (f t) j x) l (𝓝 0)) :
    (∀ t, IntegrableOn (fun y ↦ ‖f t y‖) c.domain) ∧
      Tendsto (fun t ↦ ∫ y in c.domain, ‖f t y‖) l (𝓝 0) := by
  have hb' (t : T) (j : J) : ∀ᵐ x ∂(volume.restrict (c.source j)),
      ‖sourceNorm c (f t) j x‖ ≤ g j x := by
    filter_upwards [hb t j] with x hx
    simpa only [Real.norm_of_nonneg (sourceNorm_nonneg c (f t) j x)] using hx
  have hi (t : T) (j : J) : IntegrableOn (sourceNorm c (f t) j) (c.source j) :=
    (hg j).mono' (hm t j) (hb' t j)
  refine ⟨fun t ↦ integrableOn_norm_of_sourceNorm c (f t) (hi t), ?_⟩
  have hlim (j : J) :
      Tendsto (fun t ↦ ∫ x in c.source j, sourceNorm c (f t) j x) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (c.source j)) (F := fun t x ↦ sourceNorm c (f t) j x)
      (f := fun _ ↦ (0 : ℝ)) (g j) (Eventually.of_forall (fun t ↦ hm t j))
      (Eventually.of_forall (fun t ↦ hb' t j)) (hg j) (hz j)
    simpa only [integral_zero] using hh
  have hh := tendsto_finsetSum Finset.univ (fun j hj ↦ hlim j)
  have he (t : T) := integral_norm_eq_sum_of_sourceNorm c (f t) (hi t)
  simpa only [← he, Finset.sum_const_zero] using hh

end EnvelopingIsomorphism.Deformation.Kontsevich.LocalChartDominatedConvergence
