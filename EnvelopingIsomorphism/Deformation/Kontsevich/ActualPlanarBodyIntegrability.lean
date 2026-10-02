import EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarErrorCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyGlobalIntegrability

/-! Unconditional analytic estimates on the original planar configuration
space. The finite charts and all unit bounds come from the actual compact
forest geometry. No cover, local integrability or convergence is a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarBodyIntegrability

open Set MeasureTheory Filter ContinuousAlternatingMap
open InteriorFiberAngleSplit NormalCrossingStokes RatioCutoffStokes
open RatioCutoffGlobalDomination
open scoped Classical Topology

variable {N : ℕ} (e : RatioCutoffStokes.Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)

private def centers : Finset (FinitePlanarComplexChartCover.CompactPlanar (N + 1)) :=
  (ActualPlanarErrorCharts.finite_cover e he).choose

private def charts (c : centers e he) : ErrorChart e := ActualPlanarErrorCharts.chart e he c.val

private theorem covers : shapeConfiguration (N + 1) ⊆
    ⋃ c : centers e he, (charts e he c).map '' (charts e he c).monomial.region := by
  intro η hη
  have h := (ActualPlanarErrorCharts.finite_cover e he).choose_spec hη
  obtain ⟨c, hc⟩ := mem_iUnion.mp h
  obtain ⟨hc, hηc⟩ := mem_iUnion.mp hc
  exact mem_iUnion.mpr ⟨⟨c, hc⟩, hηc⟩

include he

/-- Actual body L1 in the Cartesian frame, with all geometric inputs discharged. -/
theorem integrableOn_body :
    IntegrableOn (PlanarBodyGlobalIntegrability.body e) (shapeConfiguration (N + 1)) :=
  PlanarBodyGlobalIntegrability.integrableOn_body e he (charts e he) (covers e he)

/-- Actual body L1 in the original interleaved complex frame. -/
theorem integrableOn_body_actualFrame :
    IntegrableOn (fun η ↦ extDeriv (beta e) η (actualFrame N)) (shapeConfiguration (N + 1)) :=
  PlanarBodyGlobalIntegrability.integrableOn_body_actualFrame e he (charts e he) (covers e he)

/-- Absolute convergence of the original planar angular shape integral. -/
theorem integrableOn_shapeDensity :
    IntegrableOn (shapeDensity (angularEdges e)) (shapeConfiguration (N + 1)) :=
  PlanarBodyGlobalIntegrability.integrableOn_shapeDensity e he (charts e he) (covers e he)

/-- L1 convergence of the actual error on the collision-free configurations. -/
theorem tendsto_integral_norm_error :
    Tendsto (fun ε ↦ ∫ η in shapeConfiguration (N + 1), ‖errorDensity e ε η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  RatioCutoffGlobalDomination.tendsto_integral_norm_error e he (charts e he) (covers e he)

theorem tendsto_integral_error :
    Tendsto (fun ε ↦ ∫ η in shapeConfiguration (N + 1), errorDensity e ε η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  RatioCutoffGlobalDomination.tendsto_integral_error e he (charts e he) (covers e he)

/-- Ambient-space L1 convergence uses the actual support of the ratio cutoff. -/
theorem tendsto_integral_norm_error_whole :
    Tendsto (fun ε ↦ ∫ η : Space N, ‖errorDensity e ε η‖) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  RatioCutoffGlobalDomination.tendsto_integral_norm_error_whole e he (charts e he) (covers e he)

/-- The actual cutoff error converges in L1 for every fixed top-degree frame. -/
theorem tendsto_integral_norm_cutoffTerm (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Tendsto (fun ε ↦ ∫ η : Space N, ‖cutoffTerm e ε η v‖) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  RatioCutoffGlobalDomination.tendsto_integral_norm_cutoffTerm e he (charts e he) (covers e he) v

/-- The signed error in the original compact Stokes identity tends to zero. -/
theorem tendsto_integral_cutoffTerm (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Tendsto (fun ε ↦ ∫ η : Space N, cutoffTerm e ε η v) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  RatioCutoffGlobalDomination.tendsto_integral_cutoffTerm e he (charts e he) (covers e he) v

end EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarBodyIntegrability
