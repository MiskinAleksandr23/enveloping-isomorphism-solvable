import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateOrbit
import EnvelopingIsomorphism.Deformation.MixedSourceCarrierIntegral
import EnvelopingIsomorphism.Deformation.MixedPairedOutgoingRelabelling

/-! The actual adjacent source-face integral equals its genuine physical
coefficient for every graph, including zero-density and noncanonical orbits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedSourceAdjacentIntegral
open scoped Classical BigOperators
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedPairedEdgeRelabelling
open MixedGraphActionSplits MixedSourcePhysicalCoefficient MixedGraphOutgoingPairNormalization
open TwoPointBinaryFaceAdmissibility MixedSourceTemplateOrbit TwoPointSplitFaceContraction

section General
variable {N : ℕ} {anchor a b : Fin (N+1)} {S : Finset (Fin (N+1))}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : anchor ∈ S → a = anchor)
  {q : Fin (N+1) → ℕ} (v : Fin (N+1))
  (hq : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v)
  (H : Graph q 2) (τ : (w : Fin (N+1)) → Equiv.Perm (Fin (q w)))

theorem normalized_ofProfile_permuteOutgoing :
    normalized ha hb hba hi (ofProfile v hq (H.permuteOutgoing τ)) =
      (∏ w, permutationSign (R := ℝ) (τ w)) * normalized ha hb hba hi (ofProfile v hq H) := by
  subst q
  exact MixedPairedOutgoingRelabelling.normalized_permuted ⟨v,H⟩ τ ha hb hba hi
end General

variable {n : ℕ} (v : Fin (n+1)) (H : Graph (Arity v) 2)
  {anchor a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v)
  (hba : b ≠ a) (hi : anchor ∈ cluster v → a = anchor)

theorem normalized_native :
    normalized ha hb hba hi (ofProfile (vertexSplitChild v 0) (actionSplitArity v) H) =
      TwoPointSplitFaceWeight.normalizedIntegral v H
        (MixedSourceFaceSign.sourceMajorOrder v ha hb hba hi) := by
  rw [MixedPairedTemplateCoordinates.normalized_ofProfile]
  unfold MixedPairedTemplateCoordinates.profileEdges
  rw [MixedPairedTemplateCoordinates.source_profileOrder]
  rfl

/-- Every adjacent source graph has precisely its original physical pair
coefficient. Both the integral and coefficient vanish off the actual split
support; on it, the outgoing signs agree exactly. -/
theorem normalized_eq_physicalCoefficient :
    normalized ha hb hba hi (ofProfile (vertexSplitChild v 0) (actionSplitArity v) H) =
      sourcePhysicalCoefficient
        (ofProfile (vertexSplitChild v 0) (actionSplitArity v) H) (sourceChildPair v) := by
  by_cases hD : Data v H
  · obtain ⟨c,E,τ,rfl⟩ := exists_template_outgoing v H hD
    rw [normalized_ofProfile_permuteOutgoing, physicalCoefficient_permuteOutgoing]
    apply congrArg ((GeneralGraphOutgoingAverage.sign τ) * ·)
    fin_cases c
    · change normalized ha hb hba hi (splitForward E.1 v E.2) =
        sourcePhysicalCoefficient (forwardDataGraph v E) (sourceChildPair v)
      rw [MixedSourceCarrierIntegral.normalized_forward, sourcePhysicalCoefficient_forward]
    · change normalized ha hb hba hi (splitBackward E.1 v 1 E.2) =
        sourcePhysicalCoefficient (backwardDataGraph v 1 E) (sourceChildPair v)
      rw [MixedSourceCarrierIntegral.normalized_backward, sourcePhysicalCoefficient_backward]
  · rw [physicalCoefficient_zero_of_not_data v H hD, normalized_native]
    exact normalizedIntegral_zero_of_not_data v H hD ha hb hba _

end EnvelopingIsomorphism.Deformation.MixedSourceAdjacentIntegral
