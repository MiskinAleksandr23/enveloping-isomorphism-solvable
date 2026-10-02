import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphPathAlgebra
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalMixedTangentAssembly
import EnvelopingIsomorphism.Deformation.MixedGraphSourceDoubleCompletion

/-! The actual canonical elementary path identity is produced by the pure
mixed scalar boundary relation, with the genuine two-odd curvature correction
eliminated only by the native source MC equation. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarPath
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open CanonicalMixedTangentAssembly LaurentTaylorArityBounds

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

/-- The pure scalar mixed relation yields the actual canonical tangent/gauge
equation on arbitrary positive-t Laurent vector directions and native source MCs. -/
theorem tangentEquation_of_scalarMixedBoundary
    (h : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := k))
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ)
    (Y : VectorSeries (k := k) (d := d)) (hY : coeffV 0 Y = 0) :
    taylorDerivativeApply (CanonicalGraph.taylor k d π₀) b.val (actionDirection π₀ b.val Y) =
      applyBilinear LaurentConjugation.unaryCoefficientAction
        (tangentApply (CanonicalGraph.velocityTangent k d π₀) b.val Y)
        (single 0 (CanonicalGraph.targetBase k d π₀) + taylorApply (CanonicalGraph.taylor k d π₀) b.val) := by
  apply tangentEquation_of_homogeneous π₀ b.val b.property.1 Y hY
  intro N
  have hs := MixedGraphSourceDoubleCompletion.canonical_sourceProfile_double N (fullInput π₀ b.val) Y
  have ht := MixedGraphHomogeneous.canonical_source_eq_target h N (fullInput π₀ b.val) Y
    (CanonicalGraphMCAlgebra.source_full_square_zero π₀ hπ b)
  exact hs.symm.trans ht

/-- Literal `CanonicalGraph.PathIdentity`, with no additional cochain equation,
path ODE, correction cancellation, or all-placement completion premise. -/
theorem pathIdentity_of_scalarMixedBoundary
    (h : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := k))
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀)) :
    CanonicalGraph.PathIdentity k d π₀ hπ := by
  apply CanonicalGraphPathAlgebra.pathIdentity_of_tangentEquation π₀ hπ
  intro b Y hY
  exact tangentEquation_of_scalarMixedBoundary h π₀ hπ b Y hY

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarPath
