import EnvelopingIsomorphism.ScalarBoundaryReductionWithCorrection
import EnvelopingIsomorphism.Deformation.SignedMixedPhysicalBoundaryNormalization

/-! The geometrically computed mixed correction sign is compatible with
the original identification statement: its actual MC evaluation vanishes. -/
namespace EnvelopingIsomorphism
open Deformation
universe u v w

theorem statement_of_signed_real_scalar_boundary_relations
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ))
    (hmixed : SignedMixedPhysicalBoundaryNormalization.SignedCanonicalScalarMixedBoundaryRelation (k := ℝ)) :
    Statement.{u,v,w} :=
  statement_of_real_scalar_boundary_relation_with_correction
    (fun _ Γ ↦ -MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := ℝ) Γ)
    hmain hmixed

end EnvelopingIsomorphism
