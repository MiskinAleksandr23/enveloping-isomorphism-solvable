import EnvelopingIsomorphism.Deformation.MixedPairedPhysicalPairWeight
import EnvelopingIsomorphism.Deformation.MixedSourceAdjacentIntegral
import EnvelopingIsomorphism.Deformation.MixedCorrectionAdjacentIntegral

/-! Unconditional mixed physical two-point coefficients in arbitrary labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedCoefficientMatching
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedGraphPairLabelCounting MixedGraphCorrectionProfiles
open GraphCurvatureLabelCounting MixedPairedEdgeRelabelling TwoPointBinaryFaceAdmissibility
open MixedPairedPhysicalPairWeight MixedGraphOutgoingPairNormalization
open scoped Classical

private theorem exists_ofProfile {N : ℕ} {q : Fin (N+1) → ℕ}
    (v : Fin (N+1)) (hq : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v)
    (H : VectorGraph N 2) (hv : H.vertex = v) :
    ∃ G : Graph q 2, H = ofProfile v hq G := by
  subst q
  rcases H with ⟨w,G⟩
  dsimp only [VectorGraph.vertex] at hv
  subst w
  exact ⟨G,rfl⟩

section Source
variable {n : ℕ} (H : VectorGraph (n+1) 2) (T : PhysicalPair n)
  {i a b : Fin (n+2)} (ha : a ∈ T.val) (hb : b ∈ T.val)
  (hba : b ≠ a) (hi : i ∈ T.val → a = i)

theorem normalized_source (hv : H.vertex ∈ T.val) :
    normalized ha hb hba hi H = sourcePhysicalCoefficient H T := by
  let D := sourceRepresentative H T hv
  rw [normalized_sourceRepresentative H T D ha hb hba hi,
    ← sourceCoefficient_representative H T D]
  obtain ⟨G,hG⟩ := exists_ofProfile (vertexSplitChild D.1 0)
    (MixedGraphActionSplits.actionSplitArity D.1)
    (internalGraphEquiv D.2.val.val.symm 2 H) (source_vertex H T D)
  rw [hG]
  have ht : (⟨cluster D.1,cluster_card D.1⟩ : PhysicalPair n) =
      MixedSourcePhysicalCoefficient.sourceChildPair D.1 := by
    apply Subtype.ext
    exact cluster_eq_childPair D.1
  rw [ht]
  exact MixedSourceAdjacentIntegral.normalized_eq_physicalCoefficient D.1 G _ _ _ _
end Source

section Correction
variable {n : ℕ} (H : VectorGraph (n+2) 2) (T : PhysicalPair (n+1))
  {i a b : Fin (n+3)} (ha : a ∈ T.val) (hb : b ∈ T.val)
  (hba : b ≠ a) (hi : i ∈ T.val → a = i)

theorem normalized_correction (hv : H.vertex ∉ T.val) :
    normalized ha hb hba hi H = -(3 / 2 : ℝ) * correctionPhysicalCoefficient H T := by
  let D := correctionRepresentative H T hv
  rw [normalized_correctionRepresentative H T D ha hb hba hi,
    ← correctionCoefficient_representative H T D]
  obtain ⟨G,hG⟩ := exists_ofProfile (expandedVector D.1) (splitArity D.1)
    (internalGraphEquiv D.2.val.val.symm 2 H) (correction_vertex H T D)
  rw [hG]
  have ht : (⟨cluster D.1.2.val,cluster_card D.1.2.val⟩ : PhysicalPair (n+1)) =
      correctionChildPair D.1 := by
    apply Subtype.ext
    exact cluster_eq_childPair D.1.2.val
  rw [ht]
  exact MixedCorrectionAdjacentIntegral.normalized_eq_physicalCoefficient D.1 G _ _ _ _

/-- Each physical pair has its source coefficient minus its correction
coefficient; membership of the vector selects the actual geometric case. -/
theorem normalized_eq_physicalCoefficient :
    normalized ha hb hba hi H = sourcePhysicalCoefficient H T -
      (3 / 2 : ℝ) * correctionPhysicalCoefficient H T := by
  by_cases hv : H.vertex ∈ T.val
  · rw [MixedPhysicalPairCoefficientRelabelling.correctionPhysicalCoefficient_zero_of_vector_mem H T hv,
      mul_zero, sub_zero]
    exact normalized_source H T ha hb hba hi hv
  · rw [MixedPhysicalPairCoefficientRelabelling.sourcePhysicalCoefficient_zero_of_vector_not_mem H T hv,
      zero_sub, ← neg_mul]
    exact normalized_correction H T ha hb hba hi hv
end Correction
end EnvelopingIsomorphism.Deformation.MixedPairedCoefficientMatching
