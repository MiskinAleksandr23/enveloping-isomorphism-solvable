import EnvelopingIsomorphism.ScalarBoundaryReduction
import EnvelopingIsomorphism.Deformation.Gauge.CorrectionIndependentGraphPath

/-! Identification depends on canonical star/velocity coefficients and a mixed
scalar identity with a curvature kernel. The kernel's sign does not affect
the MC path identity, since its actual curvature evaluation is zero there. -/
namespace EnvelopingIsomorphism
open Deformation Deformation.Gauge
open MixedGraphProfileCarrier MixedGraphCorrectionProfiles

theorem graphIdentities_of_scalar_boundary_relation_with_correction
    (u : (j : ℕ) → CorrectionGraph j → ℂ)
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℂ))
    (hmixed : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℂ))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℂ)) u) :
    Rees.GraphComparisonAssembly.CanonicalGraphIdentities := by
  intro d π₀ hπ
  exact ⟨GraphBoundaryBase.canonical_starAssociative_of_baseMC hmain π₀ hπ,
    CanonicalGraphScalarMC.mcIdentity_of_scalarBoundary hmain π₀ hπ,
    CorrectionIndependentGraphPath.pathIdentity_of_scalarMixedBoundary u hmixed π₀ hπ⟩

universe u v w
theorem statement_of_scalar_boundary_relation_with_correction
    (c : (j : ℕ) → CorrectionGraph j → ℂ)
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℂ))
    (hmixed : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℂ))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℂ)) c) :
    Statement.{u,v,w} :=
  Rees.GraphComparisonAssembly.statement_of_graphIdentities
    (graphIdentities_of_scalar_boundary_relation_with_correction c hmain hmixed)

theorem statement_of_real_scalar_boundary_relation_with_correction
    (c : (j : ℕ) → CorrectionGraph j → ℝ)
    (hmain : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ))
    (hmixed : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))
      (fun _ ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ)) c) :
    Statement.{u,v,w} := by
  apply statement_of_scalar_boundary_relation_with_correction
    (fun j Γ ↦ algebraMap ℝ ℂ (c j Γ))
    (GraphBoundaryScalarExtension.canonicalScalarBoundaryRelation_complex_of_real hmain)
  have hmap := GraphBoundaryScalarExtension.scalarMixedBoundaryRelation_map (algebraMap ℝ ℂ) hmixed
  have hw : (fun n Γ ↦ algebraMap ℝ ℂ
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) n Γ)) =
      GraphBoundaryProfiles.canonicalBinaryWeight (k := ℂ) := by
    funext n Γ
    exact GraphBoundaryScalarExtension.map_canonicalBinaryWeight n Γ
  have hv : (fun n Γ ↦ algebraMap ℝ ℂ
      (MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) (n := n) Γ)) =
      (fun n ↦ MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℂ) (n := n)) := by
    funext n Γ
    exact GraphBoundaryScalarExtension.map_canonicalVelocityWeight Γ
  rw [hw,hv] at hmap
  exact hmap

end EnvelopingIsomorphism
