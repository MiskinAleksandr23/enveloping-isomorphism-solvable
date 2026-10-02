import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMCAlgebra
import EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphSummation
import EnvelopingIsomorphism.Deformation.GraphFixedArityPowerSeries

/-! The actual canonical graph MC identity follows from the pure scalar
boundary relation. Independent-input graph identities, both coefficient
completions, and the all-placement arity sum are all proved and consumed. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarMC
open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule
open LaurentTaylorArityBounds LaurentFullGraphEvaluation LaurentFullGraphSummation

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

/-- The actual full canonical graph product has zero insertion square on
every native source MC family, including arbitrary Laurent perturbations. -/
theorem full_square_zero
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ) :
    applyBilinear LaurentModule.insertBinarySeries
      (fullEvaluation (CanonicalTangentCoefficients.mcFamily k d) π₀ b.val b.property.1)
      (fullEvaluation (CanonicalTangentCoefficients.mcFamily k d) π₀ b.val b.property.1) = 0 := by
  rw [CanonicalGraphMCAlgebra.insertBinarySeries_eq_extendBilinear]
  apply fullEvaluation_square_zero_of_homogeneous
  intro N
  rw [← CanonicalGraphMCAlgebra.insertBinarySeries_eq_extendBilinear]
  exact GraphFixedArityPowerSeries.canonical_homogeneous_sum_zero h
    (fullInput π₀ b.val) (CanonicalGraphMCAlgebra.source_full_square_zero π₀ hπ b) N

/-- Literal `CanonicalGraph.MCIdentity`, produced from finite scalar graph
boundary relations with no extra multilinear, completion, or cochain premise. -/
theorem mcIdentity_of_scalarBoundary
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀)) :
    CanonicalGraph.MCIdentity k d π₀ hπ := by
  intro b
  exact CanonicalGraphMCAlgebra.target_MC_of_full_square_zero h π₀ hπ b
    (full_square_zero h π₀ hπ b)

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarMC
