import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphWeightedMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability

/-! Actual normalized real-face integral matched to the finite graft profile.
Every edge-order sign is explicit; the weights use the increasing external
chambers and the canonical vertex-major outgoing-slot order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphCanonicalFibreMatching
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphOrderedIntegrals
open BoundaryGraphWeightedMatching
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)} {q : Fin n → ℕ}

private theorem geometricWeight_eq_canonical {N M : ℕ} {p : Fin (N + 1) → ℕ}
    (G : Graph p M) (order : Fin (GraphForms.dimension N M) ≃ KontsevichGraph.General.Edge p)
    (hp : ∑ v, p v = GraphForms.dimension N M) :
    GeometricWeights.geometricWeight G order =
      (Equiv.Perm.sign (order.trans (GeometricWeights.canonicalOrder hp).symm) : ℝ) *
        GeometricWeights.canonicalWeight G hp := by
  have h := GeometricWeights.geometricWeight_permute G (GeometricWeights.canonicalOrder hp)
    (order.trans (GeometricWeights.canonicalOrder hp).symm)
  have he : (order.trans (GeometricWeights.canonicalOrder hp).symm).trans
      (GeometricWeights.canonicalOrder hp) = order := by
    apply Equiv.ext
    intro j
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he] at h
  exact h

variable (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)

include Γ order hcount in
theorem outerDegree : ∑ v, pulledOuterArity q (anchoredPartitionEquiv ha hi) v =
    GraphForms.dimension (coarseN i S) (outsideM l u + 1) := by
  have h := Fintype.card_congr (extractedOuterOrder Γ ha hi order hcount)
  simpa only [KontsevichGraph.General.Edge, Fintype.card_sigma, Fintype.card_fin] using h.symm

include Γ order hcount in
theorem innerDegree : ∑ v, pulledInnerArity q (anchoredPartitionEquiv ha hi) v =
    GraphForms.dimension (shapeN a S) (shapeM l u) := by
  have h := Fintype.card_congr (extractedInnerOrder Γ ha hi order hcount)
  simpa only [KontsevichGraph.General.Edge, Fintype.card_sigma, Fintype.card_fin] using h.symm

def outerRowPermutation : Equiv.Perm (Fin (coarseDegree i S l u)) :=
  (extractedOuterOrder Γ ha hi order hcount).trans
    (GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hcount)).symm

def innerRowPermutation : Equiv.Perm (Fin (shapeDegree a S l u)) :=
  (extractedInnerOrder Γ ha hi order hcount).trans
    (GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hcount)).symm

def outerCoefficient (G : Graph (pulledOuterArity q (anchoredPartitionEquiv ha hi)) (outsideM l u + 1)) : ℝ :=
  GeometricWeights.canonicalWeight G (outerDegree Γ ha hi order hcount)

def innerCoefficient (hlu : l < u)
    (G : Graph (pulledInnerArity q (anchoredPartitionEquiv ha hi)) ((shapeM l u - 1) + 1)) : ℝ :=
  GeometricWeights.canonicalWeight (G.reindex (Equiv.refl _) (innerBoundaryCast hlu).symm)
    (innerDegree Γ ha hi order hcount)

def fibreSign (hlu : l < u) : ℝ :=
  orderedFaceSign (graphEdges Γ order) hcount (le_of_lt hlu) *
    (outerRowPermutation Γ ha hi order hcount).sign *
    (innerRowPermutation Γ ha hi order hcount).sign

/-- The actual normalized face integral is the signed finite graft coefficient
at the explicitly reindexed original graph. Extraction, graph row matching,
ordered domain correspondence, Fubini, and all normalization factors are proved. -/
theorem normalized_integral_eq_signed_graftProfile_of_integrable (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)))
    (hshape : GeometricWeights.AbsolutelyIntegrable (GeometricWeights.orderedEdges
      (extractedShapeGraph Γ ha hi hlu (orderedGraph_innerClosed Γ ha hi hlu hn))
      (extractedInnerOrder Γ ha hi order hcount)))
    (hcoarse : GeometricWeights.AbsolutelyIntegrable (GeometricWeights.orderedEdges
      ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd)
      (extractedOuterOrder Γ ha hi order hcount))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
        orderedRealDensity (graphEdges Γ order) (le_of_lt hlu) z ∂volume.prod volume) =
      fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  rw [GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct _ _ _ _
    (orderedGraph_innerClosed Γ ha hi hlu hn) hd]
  rw [normalized_integral_eq_extracted_geometricWeights Γ ha hi hlu order hcount hn hd hshape hcoarse,
    geometricWeight_eq_canonical _ _ (outerDegree Γ ha hi order hcount),
    geometricWeight_eq_canonical _ _ (innerDegree Γ ha hi order hcount)]
  change _ = (orderedFaceSign (graphEdges Γ order) hcount (le_of_lt hlu) *
    (Equiv.Perm.sign ((extractedOuterOrder Γ ha hi order hcount).trans
      (GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hcount)).symm)) *
    (Equiv.Perm.sign ((extractedInnerOrder Γ ha hi order hcount).trans
      (GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hcount)).symm))) * _
  unfold outerCoefficient innerCoefficient extractedShapeGraph
  ring

/-- The anchored real-face fibre identity has no convergence premise:
absolute integrability of both actual smaller densities is already proved. -/
theorem normalized_integral_eq_signed_graftProfile (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)))
 :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
        orderedRealDensity (graphEdges Γ order) (le_of_lt hlu) z ∂volume.prod volume) =
      fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  exact normalized_integral_eq_signed_graftProfile_of_integrable Γ ha hi order hcount hlu hn hd
    (ForestGraphIntegrability.absolutelyIntegrable _) (ForestGraphIntegrability.absolutelyIntegrable _)

/-- A single nonzero point of the actual native face density supplies the
valence count and both admissibility properties. No graph matching or
integrability premise remains. -/
theorem normalized_integral_eq_signed_graftProfile_of_nonzero (hlu : l < u)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    let hcount := BoundaryGraphDimensionVanishing.internal_count_eq_of_nativeFaceDensity_ne_zero (graphEdges Γ order)
      (graphEdges_noLoops Γ order) y hy hne
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
        orderedRealDensity (graphEdges Γ order) (le_of_lt hlu) z ∂volume.prod volume) =
      fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  exact normalized_integral_eq_signed_graftProfile Γ ha hi order _ hlu
    (BoundaryGraphAdmissibility.graph_noOutgoing_of_nativeFaceDensity_ne_zero Γ order y hy hne)
    (orderedGraph_coarseDistinct Γ ha hi hlu
      (BoundaryGraphAdmissibility.graph_coarseTarget_injective_of_nativeFaceDensity_ne_zero Γ order y hy hne))

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphCanonicalFibreMatching
