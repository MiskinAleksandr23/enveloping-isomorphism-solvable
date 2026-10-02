import EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierIntegral
import EnvelopingIsomorphism.Deformation.MixedCorrectionPhysicalSupport
import EnvelopingIsomorphism.Deformation.MixedPairedProfileOutgoing
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceZeroIntegral

/-! Unconditional actual correction face weight for every adjacent graph,
using genuine template-orbit reconstruction and discrete support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedCorrectionAdjacentIntegral
open Kontsevich KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier MixedPairedEdgeRelabelling MixedGraphCorrectionProfiles
open MixedGraphOutgoingPairNormalization MixedGraphInternalPairRelabelling
open TwoPointBinaryFaceAdmissibility TwoPointSplitFaceContraction
open scoped Classical
variable {n : ℕ} (p : Placement n)
  (H : Graph (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2.val) 2)
  {i a b : Fin (n+3)} (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val)
  (hba : b ≠ a) (hi : i ∈ cluster p.2.val → a = i)

theorem normalized_eq_splitIntegral :
    normalized ha hb hba hi (ofProfile (expandedVector p) (splitArity p) H) =
      TwoPointSplitFaceWeight.normalizedIntegral p.2.val H
        (MixedCorrectionCarrierCoordinates.sourceMajorOrder p ha hb hba hi) := by
  rw [MixedPairedTemplateCoordinates.normalized_ofProfile]
  rfl

/-- The actual geometric correction is minus three-halves of the physical
coefficient; this holds on all graphs, without a density witness or Data premise. -/
theorem normalized_eq_physicalCoefficient :
    normalized ha hb hba hi (ofProfile (expandedVector p) (splitArity p) H) =
      -(3 / 2 : ℝ) * correctionPhysicalCoefficient
        (ofProfile (expandedVector p) (splitArity p) H) (correctionChildPair p) := by
  by_cases hD : Data p.2.val H
  · obtain ⟨c,s,Γ,χ,he⟩ := BinaryTemplateOrbitReconstruction.exists_canonical_split
      p.2.val H hD (selectedArity p).symm
    let τ := BinaryTemplateOrbitReconstruction.senderSwap
      (q := twoOddArity p.1 p.2) p.2.val c s
    have hcarrier : ofProfile (expandedVector p) (splitArity p) (H.permuteOutgoing τ) =
        Correction.canonicalDataGraph p c ⟨Γ,χ⟩ :=
      congrArg (ofProfile (expandedVector p) (splitArity p)) he.symm
    have h := MixedCorrectionCarrierIntegral.normalized_canonicalDataGraph p ha hb hba hi c ⟨Γ,χ⟩
    rw [← hcarrier, MixedPairedProfileOutgoing.normalized_ofProfile_permuteOutgoing,
      MixedCorrectionPhysicalSupport.coefficient_permuteOutgoing] at h
    change GeneralGraphOutgoingAverage.sign τ * _ = _ at h
    have hs : GeneralGraphOutgoingAverage.sign τ ≠ 0 := by
      intro hz
      have hsq := GeneralGraphOutgoingAverage.sign_sq τ
      rw [hz, zero_mul] at hsq
      exact zero_ne_one hsq
    apply mul_left_cancel₀ hs
    calc
      _ = -(3 / 2 : ℝ) * (GeneralGraphOutgoingAverage.sign τ *
          correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) H)
            (correctionChildPair p)) := h
      _ = _ := by ring
  · rw [MixedCorrectionPhysicalSupport.coefficient_zero_of_not_data p H hD, mul_zero,
      normalized_eq_splitIntegral,
      TwoPointFaceZeroIntegral.normalizedIntegral_eq_zero_of_not_data p.2.val H ha hb hba _ hD]

end EnvelopingIsomorphism.Deformation.MixedCorrectionAdjacentIntegral
