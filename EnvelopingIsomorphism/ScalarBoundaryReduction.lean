import EnvelopingIsomorphism.Rees.GraphComparisonAssembly
import EnvelopingIsomorphism.Deformation.GraphBoundaryBase
import EnvelopingIsomorphism.Deformation.GraphBoundaryScalarExtension
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarMC
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphScalarPath

/-! The exact remaining scalar geometric obligations imply the original
solvable identification statement. Neither scalar relation is assumed as an axiom
or asserted to have been proved by this conditional reduction. -/

namespace EnvelopingIsomorphism

open Deformation Deformation.Gauge

theorem graphIdentities_of_scalar_boundary_relations
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℂ))
    (hmixed : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℂ)) :
    Rees.GraphComparisonAssembly.CanonicalGraphIdentities := by
  intro d π₀ hπ
  exact ⟨GraphBoundaryBase.canonical_starAssociative_of_baseMC hmain π₀ hπ,
    CanonicalGraphScalarMC.mcIdentity_of_scalarBoundary hmain π₀ hπ,
    CanonicalGraphScalarPath.pathIdentity_of_scalarMixedBoundary hmixed π₀ hπ⟩

universe u v w

/-- The original full-universe statement follows from the two precise scalar
graph boundary equations; no further algebraic or completion contract remains. -/
theorem statement_of_scalar_boundary_relations
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℂ))
    (hmixed : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℂ)) :
    Statement.{u, v, w} :=
  Rees.GraphComparisonAssembly.statement_of_graphIdentities
    (graphIdentities_of_scalar_boundary_relations hmain hmixed)

/-- The real geometric equations already suffice for the original statement
over every field of characteristic zero. -/
theorem statement_of_real_scalar_boundary_relations
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ))
    (hmixed : MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ)) :
    Statement.{u, v, w} :=
  statement_of_scalar_boundary_relations
    (GraphBoundaryScalarExtension.canonicalScalarBoundaryRelation_complex_of_real hmain)
    (GraphBoundaryScalarExtension.canonicalScalarMixedBoundaryRelation_complex_of_real hmixed)

end EnvelopingIsomorphism
