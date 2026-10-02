import EnvelopingIsomorphism.Deformation.MixedPairedTemplateCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateIntegral

/-! Unconditional literal integrals for the three genuine mixed source
carrier splits, with their canonical graph edge orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedSourceCarrierIntegral
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedPairedEdgeRelabelling
open TwoPointBinaryFaceAdmissibility MixedGraphActionSplits
variable {n : ℕ} (Γ : Graph (fun _ : Fin (n+1) => 2) 2) (v : Fin (n+1))
  (χ : Γ.VertexSplitChoices v) {i a b : Fin (n+2)}
  (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a) (hi : i ∈ cluster v → a = i)

theorem normalized_template (c : Fin 3) :
    normalized ha hb hba hi
      (ofProfile (vertexSplitChild v 0) (actionSplitArity v)
        (Γ.vertexSplit (MixedTwoPointTemplateWeight.sourceTemplate c) v rfl χ)) =
      (if c = 1 then (-1 : ℝ) else 1) * GraphCanonicalBinaryWeights.rawBinaryWeight (n+1) Γ := by
  rw [MixedPairedTemplateCoordinates.normalized_sourceTemplate,
    MixedSourceTemplateIntegral.normalized_sourceMajor]

theorem normalized_forward :
    normalized ha hb hba hi (splitForward Γ v χ) = GraphCanonicalBinaryWeights.rawBinaryWeight (n+1) Γ := by
  simpa [splitForward, MixedTwoPointTemplateWeight.sourceTemplate] using
    normalized_template Γ v χ ha hb hba hi 0

theorem normalized_backward :
    normalized ha hb hba hi (splitBackward Γ v 1 χ) = -GraphCanonicalBinaryWeights.rawBinaryWeight (n+1) Γ := by
  simpa [splitBackward, MixedTwoPointTemplateWeight.sourceTemplate] using
    normalized_template Γ v χ ha hb hba hi 1

theorem normalized_backward_swap :
    normalized ha hb hba hi (splitBackward Γ v (Equiv.swap 0 1) χ) =
      GraphCanonicalBinaryWeights.rawBinaryWeight (n+1) Γ := by
  simpa [splitBackward, MixedTwoPointTemplateWeight.sourceTemplate] using
    normalized_template Γ v χ ha hb hba hi 2

end EnvelopingIsomorphism.Deformation.MixedSourceCarrierIntegral
