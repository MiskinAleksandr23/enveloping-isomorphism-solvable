import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphExtractedOrders

/-! Exact weighted integral of an actual ordered real-boundary graph face.
The smaller graphs and their edge orders are extracted from the original graph;
no coefficient identity or external chamber invariance is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphWeightedMatching
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphOrderedIntegrals
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)} {q : Fin n → ℕ}

theorem outgoingFactor_partition (ha : a ∈ S) (hi : i ∉ S) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) =
      GeometricWeights.outgoingFactor (pulledOuterArity q (anchoredPartitionEquiv ha hi)) *
      GeometricWeights.outgoingFactor (pulledInnerArity q (anchoredPartitionEquiv ha hi)) := by
  calc
    _ = ∏ v, ((q (anchoredPartitionEquiv ha hi v)).factorial : ℝ)⁻¹ := by
      exact (Equiv.prod_comp (anchoredPartitionEquiv ha hi) (fun v ↦ ((q v).factorial : ℝ)⁻¹)).symm
    _ = _ := by rw [Fin.prod_univ_add]; rfl

variable (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)))

/-- Raw integral matching for the two actual extracted graphs and the exact
edge orders induced by the original graph. -/
theorem integral_eq_extracted_rawIntegrals
    (hshape : GeometricWeights.AbsolutelyIntegrable (GeometricWeights.orderedEdges
      (extractedShapeGraph Γ ha hi hlu (orderedGraph_innerClosed Γ ha hi hlu hn))
      (extractedInnerOrder Γ ha hi order hcount)))
    (hcoarse : GeometricWeights.AbsolutelyIntegrable (GeometricWeights.orderedEdges
      ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd)
      (extractedOuterOrder Γ ha hi order hcount))) :
    (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
      orderedRealDensity (graphEdges Γ order) (le_of_lt hlu) z ∂volume.prod volume) =
      orderedFaceSign (graphEdges Γ order) hcount (le_of_lt hlu) *
        (GeometricWeights.rawIntegral (GeometricWeights.orderedEdges
          (extractedShapeGraph Γ ha hi hlu (orderedGraph_innerClosed Γ ha hi hlu hn))
          (extractedInnerOrder Γ ha hi order hcount)) *
         GeometricWeights.rawIntegral (GeometricWeights.orderedEdges
          ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd)
          (extractedOuterOrder Γ ha hi order hcount))) := by
  simp only [extractedInner_orderedEdges Γ ha hi hlu order hcount _ hn,
    extractedOuter_orderedEdges Γ ha hi hlu order hcount hd] at hshape hcoarse ⊢
  exact integral_orderedRealDensity (graphEdges Γ order) hcount (fun j hj ↦ hn (order j) hj)
    ha hi (le_of_lt hlu) (graphEdges_noLoops Γ order) hshape hcoarse

/-- The actual face integral, normalized by the original outgoing factorials
and angle powers, equals the signed product of genuine geometric graph
weights. Vertex MC factorials and the global boundary orientation are separate. -/
theorem normalized_integral_eq_extracted_geometricWeights
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
      orderedFaceSign (graphEdges Γ order) hcount (le_of_lt hlu) *
        (GeometricWeights.geometricWeight
          ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd)
          (extractedOuterOrder Γ ha hi order hcount) *
         GeometricWeights.geometricWeight
          (extractedShapeGraph Γ ha hi hlu (orderedGraph_innerClosed Γ ha hi hlu hn))
          (extractedInnerOrder Γ ha hi order hcount)) := by
  rw [integral_eq_extracted_rawIntegrals Γ ha hi hlu order hcount hn hd hshape hcoarse,
    outgoingFactor_partition ha hi, pow_add, mul_inv_rev]
  unfold GeometricWeights.geometricWeight
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphWeightedMatching
