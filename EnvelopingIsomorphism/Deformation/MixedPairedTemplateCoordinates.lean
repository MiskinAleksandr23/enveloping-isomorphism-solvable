import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceFaceSign

/-! Exact profile casts and edge orders linking mixed carrier coordinates
to the genuine split-template face integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedTemplateCoordinates
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedPairedEdgeRelabelling
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open scoped Classical BigOperators

section General
variable {N : ℕ} {i a b : Fin (N+1)} {S : Finset (Fin (N+1))}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : i ∈ S → a = i)
  {q : Fin (N+1) → ℕ} (v : Fin (N+1))
  (hq : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v)

include hq in
theorem profileEdgeCount : ∑ j, q j = GraphForms.dimension N 1 := by
  rw [hq]
  exact Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 v

def profileOrder : Fin (shapeDegree a b S + coarseDegree i a S 2) ≃ KontsevichGraph.General.Edge q :=
  (finCongr (nativeDegree_eq ha hb hba hi)).trans (GeometricWeights.canonicalOrder (profileEdgeCount v hq))

def profileEdges (G : Graph q 2) : Fin (shapeDegree a b S + coarseDegree i a S 2) → Edge (N+1) 2 :=
  fun j => let e := profileOrder ha hb hba hi v hq j; (e.1,G.target e)

theorem nativeEdges_ofProfile (G : Graph q 2) :
    nativeEdges ha hb hba hi (ofProfile v hq G) = profileEdges ha hb hba hi v hq G := by
  subst q
  rfl

theorem normalized_ofProfile (G : Graph q 2) :
    normalized ha hb hba hi (ofProfile v hq G) =
      GeometricWeights.outgoingFactor q *
        (((2 * Real.pi) ^ (shapeDegree a b S + coarseDegree i a S 2))⁻¹ *
          TwoPointFaceRelabelling.integral (profileEdges ha hb hba hi v hq G)) := by
  unfold normalized normalization
  rw [nativeEdges_ofProfile]
  have hv : (ofProfile v hq G).vertex = v := rfl
  rw [hv, ← hq]
  have he := nativeDegree_eq ha hb hba hi
  rw [he, mul_assoc]
end General

section Source
variable {n : ℕ} (Γ : Graph (fun _ : Fin (n+1) => 2) 2) (v : Fin (n+1))
  (c : Fin 3) (χ : Γ.VertexSplitChoices v)
  {i a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v)
  (hba : b ≠ a) (hi : i ∈ cluster v → a = i)

theorem source_profileOrder :
    profileOrder ha hb hba hi (vertexSplitChild v 0) (MixedGraphActionSplits.actionSplitArity v) =
      MixedSourceFaceSign.sourceMajorOrder v ha hb hba hi := by
  apply Equiv.ext
  intro j
  unfold profileOrder GeometricWeights.canonicalOrder MixedSourceFaceSign.sourceMajorOrder
    MixedSourceCanonicalOrder.splitOrder
  congr 1

theorem normalized_sourceTemplate :
    normalized ha hb hba hi
      (ofProfile (vertexSplitChild v 0) (MixedGraphActionSplits.actionSplitArity v)
        (Γ.vertexSplit (MixedTwoPointTemplateWeight.sourceTemplate c) v rfl χ)) =
      TwoPointSplitFaceWeight.normalizedIntegral v
        (Γ.vertexSplit (MixedTwoPointTemplateWeight.sourceTemplate c) v rfl χ)
        (MixedSourceFaceSign.sourceMajorOrder v ha hb hba hi) := by
  rw [normalized_ofProfile]
  unfold profileEdges
  rw [source_profileOrder]
  rfl
end Source

end EnvelopingIsomorphism.Deformation.MixedPairedTemplateCoordinates
