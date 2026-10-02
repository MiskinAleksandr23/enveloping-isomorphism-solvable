import EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionFaceSign
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization

/-! Actual correction carrier integrals with the derived minus sign before
the physical two-odd curvature coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierIntegral
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedPairedEdgeRelabelling
open MixedGraphCorrectionProfiles InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open BinaryVertexContraction MixedGraphInternalPairRelabelling MixedGraphOutgoingPairNormalization
variable {n : ℕ} (p : Placement n) {i a b : Fin (n+3)}
  (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val) (hba : b ≠ a)
  (hi : i ∈ cluster p.2.val → a = i)

theorem sourceMajorOrder_eq : MixedCorrectionCarrierCoordinates.sourceMajorOrder p ha hb hba hi =
    MixedCorrectionFaceSign.sourceMajorOrder p ha hb hba hi := by
  rw [MixedCorrectionCarrierCoordinates.sourceMajorOrder_eq]
  rfl

theorem normalized_template (Γ : QuotientGraph p) (c : Fin 2) (χ : SplitChoices p Γ) :
    normalized ha hb hba hi (ofProfile (expandedVector p) (splitArity p)
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)) =
      -(3 / 2 : ℝ) * placementSign p * MixedGraphPhysicalPairSums.rawCorrectionQuotientWeight ⟨p,Γ⟩ := by
  rw [MixedCorrectionCarrierCoordinates.normalized_template, sourceMajorOrder_eq,
    MixedCorrectionFaceSign.normalized_sourceMajor]

/-- The entire physical outgoing normalization is computed for the genuine
canonical split. The minus sign is the proved geometric correction sign. -/
theorem normalized_canonicalDataGraph (c : Fin 2) (D : CorrectionSplitData p) :
    normalized ha hb hba hi (Correction.canonicalDataGraph p c D) =
      -(3 / 2 : ℝ) * correctionPhysicalCoefficient (Correction.canonicalDataGraph p c D)
        (correctionChildPair p) := by
  rw [correctionPhysicalCoefficient_split]
  have h := normalized_template p ha hb hba hi D.1 c D.2
  simpa only [Correction.canonicalDataGraph, mul_assoc] using h

end EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierIntegral
