import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffStokes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Passing from the genuine compact ratio-cutoff identity to a vanishing
integral. The remaining inputs are actual global L1 and error convergence,
which are supplied separately by the finite complex chart estimates. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCutoffLimit

open InteriorFiberAngleSplit Set MeasureTheory Filter
open scoped Topology

variable {N : ℕ}

theorem tendsto_integral_chi_mul (f : Shape N → ℝ)
    (hf : IntegrableOn f (shapeConfiguration N)) :
    Tendsto (fun ε : ℝ => ∫ η in shapeConfiguration N, RatioCutoff.chi ε η * f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ η in shapeConfiguration N, f η)) := by
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun η => RatioCutoff.chi ε η * f η) (volume.restrict (shapeConfiguration N)) := by
    filter_upwards [hε] with ε hε
    exact ((RatioCutoff.contDiff_chi hε).continuous.measurable.aestronglyMeasurable.restrict).mul
      hf.aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ η ∂volume.restrict (shapeConfiguration N),
      ‖RatioCutoff.chi ε η * f η‖ ≤ ‖f η‖ := by
    apply Eventually.of_forall
    intro η
    rw [norm_mul, Real.norm_of_nonneg (RatioCutoff.chi_nonneg ε η)]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatioCutoff.chi_le_one ε η)
  have hl : ∀ᵐ η ∂volume.restrict (shapeConfiguration N),
      Tendsto (fun ε : ℝ => RatioCutoff.chi ε η * f η) (𝓝[>] (0 : ℝ)) (𝓝 (f η)) := by
    filter_upwards [ae_restrict_mem (isOpen_shapeConfiguration N).measurableSet] with η hη
    simpa only [one_mul] using (RatioCutoff.tendsto_chi hη).mul_const (f η)
  exact tendsto_integral_filter_of_dominated_convergence (fun η => ‖f η‖)
    hm (Eventually.of_forall hb) hf.norm hl

/-- No vanishing integral is supplied: the conclusion follows from the
proved compact-cutoff identity and a separate actual error integral limit. -/
theorem integral_eq_zero_of_cutoff_identity (f : Shape N → ℝ)
    (hf : IntegrableOn f (shapeConfiguration N)) (error : ℝ → Shape N → ℝ)
    (herror : Tendsto (fun ε : ℝ => ∫ η in shapeConfiguration N, error ε η)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hidentity : ∀ ε : ℝ, 0 < ε →
      (∫ η in shapeConfiguration N, RatioCutoff.chi ε η * f η) =
        -(∫ η in shapeConfiguration N, error ε η)) :
    (∫ η in shapeConfiguration N, f η) = 0 := by
  have heq : (fun ε : ℝ => -(∫ η in shapeConfiguration N, error ε η)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ∫ η in shapeConfiguration N, RatioCutoff.chi ε η * f η) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hidentity ε hε).symm
  have hz : Tendsto (fun ε : ℝ => ∫ η in shapeConfiguration N, RatioCutoff.chi ε η * f η)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using herror.neg.congr' heq
  exact tendsto_nhds_unique (tendsto_integral_chi_mul f hf) hz

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCutoffLimit
