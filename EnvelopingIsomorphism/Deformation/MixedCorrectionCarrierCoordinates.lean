import EnvelopingIsomorphism.Deformation.MixedPairedTemplateCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionCanonicalOrder

/-! Literal mixed carrier coordinates for correction templates with their
retained exterior vector and canonical edge order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierCoordinates
open Kontsevich KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier MixedPairedEdgeRelabelling MixedPairedTemplateCoordinates
open MixedGraphCorrectionProfiles InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open SchoutenGraphContraction
open scoped Classical
variable {n : ℕ} (p : Placement n) {i a b : Fin (n+3)}
  (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val) (hba : b ≠ a)
  (hi : i ∈ cluster p.2.val → a = i)

include ha hb hba hi in
theorem nativeDegree_eq :
    shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2 =
      MixedCorrectionCanonicalOrder.dim (n := n) + 1 := by
  have h := MixedPairedEdgeRelabelling.nativeDegree_eq ha hb hba hi
  exact h.trans (by dsimp [MixedCorrectionCanonicalOrder.dim, GraphForms.dimension]; omega)

def sourceMajorOrder :
    Fin (shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2) ≃
      KontsevichGraph.General.Edge (MixedCorrectionCanonicalOrder.expandedArity p) :=
  profileOrder ha hb hba hi (expandedVector p) (splitArity p)

theorem sourceMajorOrder_eq : sourceMajorOrder p ha hb hba hi =
    (finCongr (nativeDegree_eq p ha hb hba hi)).trans (MixedCorrectionCanonicalOrder.splitOrder p) := by
  apply Equiv.ext
  intro j
  unfold sourceMajorOrder profileOrder GeometricWeights.canonicalOrder MixedCorrectionCanonicalOrder.splitOrder
  congr 1

variable (Γ : QuotientGraph p) (γ : Graph bivectorArity 3) (χ : SplitChoices p Γ)

theorem normalized_template :
    normalized ha hb hba hi (ofProfile (expandedVector p) (splitArity p)
      (Γ.vertexSplit γ p.2.val (selectedArity p).symm χ)) =
    TwoPointSplitFaceWeight.normalizedIntegral p.2.val
      (Γ.vertexSplit γ p.2.val (selectedArity p).symm χ) (sourceMajorOrder p ha hb hba hi) := by
  rw [normalized_ofProfile]
  rfl

theorem normalized_forward (c : Fin 3) :
    normalized ha hb hba hi (splitForward p Γ c χ) =
      TwoPointSplitFaceWeight.normalizedIntegral p.2.val
        (Γ.vertexSplit (bivectorForward (cyclicPermutation c)) p.2.val (selectedArity p).symm χ)
        (sourceMajorOrder p ha hb hba hi) :=
  normalized_template p ha hb hba hi Γ _ χ

theorem normalized_reverse (c : Fin 3) :
    normalized ha hb hba hi (splitReverse p Γ c χ) =
      TwoPointSplitFaceWeight.normalizedIntegral p.2.val
        (Γ.vertexSplit (bivectorReverse (cyclicPermutation c)) p.2.val (selectedArity p).symm χ)
        (sourceMajorOrder p ha hb hba hi) :=
  normalized_template p ha hb hba hi Γ _ χ

end EnvelopingIsomorphism.Deformation.MixedCorrectionCarrierCoordinates
