import EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarBodyIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOrderedAngularForms

/-! Unconditional angular vanishing on the original planar configuration
space, and for every ordered internal edge list in first-edge coordinates.
The relation to native forest face measures is a separate geometric step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularVanishing

open InteriorFiberAngleSplit NormalCrossingStokes RatioCutoffStokes
open PlanarOrderedAngularForms
open Set MeasureTheory Filter ContinuousAlternatingMap
open scoped Topology

/-- Actual large planar shape integral; neither L1 nor a limiting identity is assumed. -/
theorem integral_shapeDensity_eq_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) :
    (∫ η in shapeConfiguration (N + 1), shapeDensity (angularEdges e) η) = 0 := by
  have h := PlanarActualCutoffLimit.integral_body_eq_zero_of_whole_error e he
    (ActualPlanarBodyIntegrability.integrableOn_body_actualFrame e he)
    (ActualPlanarBodyIntegrability.tendsto_integral_cutoffTerm e he (actualFrame N))
  rw [← setIntegral_congr_fun (isOpen_shapeConfiguration (N + 1)).measurableSet
    (fun _ hη ↦ PlanarActualCutoffLimit.body_eq_shapeDensity e he hη)]
  exact h

/-- Actual rotation extraction yields the original angular fiber integral zero. -/
theorem integral_fiberDensity_eq_zero {N : ℕ} (e : RatioCutoffStokes.Edges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) :
    IntegrableOn (fiberDensity (angularEdges e)) (integrationRegion (N + 1)) ∧
      (∫ x in integrationRegion (N + 1), fiberDensity (angularEdges e) x) = 0 := by
  refine ⟨(integrableOn_fiberDensity_iff _).mpr
    (ActualPlanarBodyIntegrability.integrableOn_shapeDensity e he), ?_⟩
  rw [integral_fiberDensity_eq, integral_shapeDensity_eq_zero e he, mul_zero]

/-- Every ordered list of exactly 2q−3 internal angular factors with q≥3
vanishes. Loops are treated by their literal zero column. The nonloop case
uses the first edge as reference and preserves every remaining edge's order. -/
theorem ordered_integral_eq_zero {N : ℕ} (e : OrderedEdges (N + 1)) :
    IntegrableOn (density e (reference e)) (integrationRegion (N + 1)) ∧
      (∫ x in integrationRegion (N + 1), density e (reference e) x) = 0 := by
  classical
  by_cases he : ∀ j, (e j).1 ≠ (e j).2
  · have h := integral_fiberDensity_eq_zero (primitiveEdges (remainingEdges e))
      (primitiveEdges_nonloop _ (remainingEdges_nonloop e he))
    simpa only [angularEdges_primitiveEdges,
      show density e (reference e) = fiberDensity (remainingEdges e) from
        funext (density_eq_fiberDensity e (he 0))] using h
  · push Not at he
    obtain ⟨j, hj⟩ := he
    have hz : density e (reference e) = 0 := funext (density_eq_zero_of_loop e (reference e) j hj)
    rw [hz]
    exact ⟨integrableOn_zero, by simp⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularVanishing
