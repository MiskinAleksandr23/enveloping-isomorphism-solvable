import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Absolute integrability of genuine top forms under arbitrary-sign coordinate changes. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.UnorientedFormIntegrability

open Set MeasureTheory ContinuousAlternatingMap
open BoxStokes OrientedFormChangeVariables
open scoped Topology Classical

/-- Norms of the actual pullback density see precisely the absolute Jacobian. -/
theorem norm_density_pullback {d : ℕ} (f : Coord d → Coord d) (form : TopForm d) (x : Coord d) :
    ‖density (pullback f form) x‖ = |jacobian f x| * ‖density form (f x)‖ := by
  rw [density_pullback, norm_mul, Real.norm_eq_abs]

private def signFactor (x : ℝ) : ℝ := if x < 0 then -1 else 1

private theorem measurable_signFactor : Measurable signFactor :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

private theorem norm_signFactor (x : ℝ) : ‖signFactor x‖ = 1 := by
  unfold signFactor
  split_ifs <;> norm_num

private theorem signFactor_mul_abs (x : ℝ) : signFactor x * |x| = x := by
  by_cases hx : x < 0
  · simp [signFactor, hx, abs_of_neg hx]
  · simp [signFactor, hx, abs_of_nonneg (le_of_not_gt hx)]

private theorem signFactor_mul (x : ℝ) : signFactor x * x = |x| := by
  by_cases hx : x < 0
  · simp [signFactor, hx, abs_of_neg hx]
  · simp [signFactor, hx, abs_of_nonneg (le_of_not_gt hx)]

/-- Measurability of the multiplier is enough to remove its sign, even when
the other factor was not initially known measurable. Zero Jacobians are allowed. -/
theorem integrable_abs_mul_iff {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (J g : A → ℝ) (hJ : AEStronglyMeasurable J μ) :
    Integrable (fun x => |J x| * g x) μ ↔ Integrable (fun x => J x * g x) μ := by
  have hsign : AEStronglyMeasurable (fun x => signFactor (J x)) μ :=
    (measurable_signFactor.comp_aemeasurable hJ.aemeasurable).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖signFactor (J x)‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun x => (norm_signFactor (J x)).le)
  constructor
  · intro h
    have hp := h.bdd_mul hsign hbound
    simpa only [← mul_assoc, signFactor_mul_abs] using hp
  · intro h
    have hp := h.bdd_mul hsign hbound
    simpa only [← mul_assoc, signFactor_mul] using hp

/-- C1 supplies continuity, hence actual restricted measurability, of the signed Jacobian. -/
theorem continuousOn_jacobian {d : ℕ} (f : Coord d → Coord d) (S : Set (Coord d))
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) : ContinuousOn (jacobian f) S := by
  intro x hx
  exact (ContinuousLinearMap.continuous_det.continuousAt.comp
    ((hf x hx).continuousAt_fderiv (by decide))).continuousWithinAt

/-- Genuine change of variables for top-form L1, with no Jacobian-sign premise
and no regularity or measurability premise on the target form. -/
theorem integrableOn_image_iff_pullback {d : ℕ} (f : Coord d → Coord d)
    (S : Set (Coord d)) (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) (hinj : InjOn f S) (form : TopForm d) :
    IntegrableOn (density form) (f '' S) ↔ IntegrableOn (density (pullback f form)) S := by
  have hder : ∀ x ∈ S, HasFDerivWithinAt f (fderiv ℝ f x) S x :=
    fun x hx => ((hf x hx).differentiableAt (by decide)).hasFDerivAt.hasFDerivWithinAt
  have hcv := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hder hinj (density form)
  refine hcv.trans ?_
  have hJ : AEStronglyMeasurable (jacobian f) (volume.restrict S) :=
    (continuousOn_jacobian f S hf).aestronglyMeasurable hS
  change Integrable (fun x => |jacobian f x| * density form (f x)) (volume.restrict S) ↔
    Integrable (density (pullback f form)) (volume.restrict S)
  have he : density (pullback f form) = fun x => jacobian f x * density form (f x) :=
    funext (density_pullback f form)
  rw [he]
  exact integrable_abs_mul_iff (jacobian f) (fun x => density form (f x)) hJ

/-- Native open chart specialization; arbitrary measurable source subregions are allowed. -/
theorem integrableOn_chart_image_iff_pullback {d : ℕ}
    (e : OpenPartialHomeomorph (Coord d) (Coord d)) (he : ContDiffOn ℝ 1 e e.source)
    (S : Set (Coord d)) (hS : MeasurableSet S) (hse : S ⊆ e.source) (form : TopForm d) :
    IntegrableOn (density form) (e '' S) ↔ IntegrableOn (density (pullback e form)) S :=
  integrableOn_image_iff_pullback e S hS
    (fun _ hx => he.contDiffAt (e.open_source.mem_nhds (hse hx))) (e.injOn.mono hse) form

theorem integrableOn_chart_target_iff_pullback {d : ℕ}
    (e : OpenPartialHomeomorph (Coord d) (Coord d)) (he : ContDiffOn ℝ 1 e e.source) (form : TopForm d) :
    IntegrableOn (density form) e.target ↔ IntegrableOn (density (pullback e form)) e.source := by
  simpa only [e.image_source_eq_target] using
    integrableOn_chart_image_iff_pullback e he e.source e.open_source.measurableSet subset_rfl form

/-- A target piece vanishing off the chart image has exactly the same L1 question
on its entire original domain as its actual pullback on the chart source. -/
theorem integrableOn_domain_iff_pullback {d : ℕ} (f : Coord d → Coord d)
    (S V : Set (Coord d)) (hS : MeasurableSet S) (hV : MeasurableSet V)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) (hinj : InjOn f S)
    (himage : f '' S ⊆ V) (form : TopForm d)
    (hzero : ∀ y ∈ V \ (f '' S), density form y = 0) :
    IntegrableOn (density form) V ↔ IntegrableOn (density (pullback f form)) S := by
  refine (show IntegrableOn (density form) V ↔ IntegrableOn (density form) (f '' S) from
    ⟨fun h => h.mono_set himage, fun h => h.of_forall_sdiff_eq_zero hV hzero⟩).trans ?_
  exact integrableOn_image_iff_pullback f S hS hf hinj form

/-- The exact source/image identification V∩T localizes pieces supported in chart target T. -/
theorem integrableOn_domain_iff_pullback_of_image_inter {d : ℕ} (f : Coord d → Coord d)
    (S V T : Set (Coord d)) (hS : MeasurableSet S) (hV : MeasurableSet V)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) (hinj : InjOn f S)
    (himage : f '' S = V ∩ T) (form : TopForm d)
    (hzero : ∀ y ∈ V, y ∉ T → density form y = 0) :
    IntegrableOn (density form) V ↔ IntegrableOn (density (pullback f form)) S := by
  apply integrableOn_domain_iff_pullback f S V hS hV hf hinj
    (by rw [himage]; exact inter_subset_left) form
  intro y hy
  exact hzero y hy.1 (fun hT => hy.2 (by rw [himage]; exact ⟨hy.1, hT⟩))

/-- Evaluation on the actual coordinate basis preserves compact support. -/
theorem hasCompactSupport_density {d : ℕ} (form : TopForm d) (hform : HasCompactSupport form) :
    HasCompactSupport (density form) :=
  hform.comp_left (g := fun A : Coord d [⋀^Fin d]→L[ℝ] ℝ => A (standardBasis d)) rfl

theorem continuous_density {d : ℕ} (form : TopForm d) (hform : Continuous form) :
    Continuous (density form) :=
  (ContinuousAlternatingMap.apply ℝ (Coord d) ℝ (standardBasis d)).continuous.comp hform

/-- Actual continuous compact source forms have Lebesgue-integrable coordinate densities. -/
theorem integrable_density_of_compact {d : ℕ} (form : TopForm d)
    (hform : Continuous form) (hcpt : HasCompactSupport form) : Integrable (density form) :=
  (continuous_density form hform).integrable_of_hasCompactSupport (hasCompactSupport_density form hcpt)

/-- A compact continuous form agreeing with the genuine pullback proves target
L1 on the full original domain whenever its piece vanishes outside the chart image. -/
theorem integrableOn_of_compact_pullback {d : ℕ} (f : Coord d → Coord d)
    (S V : Set (Coord d)) (hS : MeasurableSet S) (hV : MeasurableSet V)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) (hinj : InjOn f S)
    (himage : f '' S ⊆ V) (form η : TopForm d)
    (hzero : ∀ y ∈ V \ (f '' S), density form y = 0)
    (hη : Continuous η) (hcpt : HasCompactSupport η)
    (heq : EqOn (pullback f form) η S) : IntegrableOn (density form) V := by
  apply (integrableOn_domain_iff_pullback f S V hS hV hf hinj himage form hzero).mpr
  have hi := (integrable_density_of_compact η hη hcpt).integrableOn (s := S)
  apply (integrableOn_congr_fun (fun x hx => congrArg
    (fun A : Coord d [⋀^Fin d]→L[ℝ] ℝ => A (standardBasis d)) (heq hx)) hS).mpr
  exact hi

/-- Source/image support localization for a genuine original-domain intersection
with a chart target, requiring no orientation or constant-Jacobian-sign data. -/
theorem integrableOn_of_compact_pullback_image_inter {d : ℕ} (f : Coord d → Coord d)
    (S V T : Set (Coord d)) (hS : MeasurableSet S) (hV : MeasurableSet V)
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) (hinj : InjOn f S)
    (himage : f '' S = V ∩ T) (form η : TopForm d)
    (hzero : ∀ y ∈ V, y ∉ T → density form y = 0)
    (hη : Continuous η) (hcpt : HasCompactSupport η)
    (heq : EqOn (pullback f form) η S) : IntegrableOn (density form) V := by
  apply integrableOn_of_compact_pullback f S V hS hV hf hinj
    (by rw [himage]; exact inter_subset_left) form η
  · intro y hy
    exact hzero y hy.1 (fun hT => hy.2 (by rw [himage]; exact ⟨hy.1, hT⟩))
  · exact hη
  · exact hcpt
  · exact heq

end EnvelopingIsomorphism.Deformation.Kontsevich.UnorientedFormIntegrability
