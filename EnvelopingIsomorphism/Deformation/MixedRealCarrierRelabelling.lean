import EnvelopingIsomorphism.Deformation.MixedRealPhysicalCarrierRelabelling

/-! The physical carrier is the original retained-vector graph under its
actual anchored source permutation and the proved cardinality cast. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedRealCarrierRelabelling
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphAveraging MixedGraphBlockRelabelling MixedRealGraftPhysicalCoefficient
open MixedRealPhysicalCarrierRelabelling MixedGraphLabelledClusterCounting
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open scoped Classical

theorem vectorGraph_eq_internal_cast {n N m : ℕ} {G : VectorGraph n m} {D : VectorGraph N m}
    (h : n = N) (e : Fin (n+1) ≃ Fin (N+1)) (F : SlotRelabelling G.graph D.graph)
    (he : F.vertices = e) (hv : D.vertex = e G.vertex) :
    D = internalGraphEquiv ((finCongr (congrArg (·+1) h)).symm.trans e) m (castVertices h G) := by
  subst N
  exact vectorGraph_eq_internal e F he hv

section Actual
variable {N : ℕ} {i a : Fin (N+1)} {S : Finset (Fin (N+1))} {l u : Fin 3}
variable (ha : a ∈ S) (hi : i ∉ S)

include ha hi in
theorem outputSize : N = coarseN i S + (shapeN a S+1) := by
  have h := Fintype.card_congr (anchoredPartitionEquiv ha hi)
  simp only [Fintype.card_fin] at h
  omega

include ha hi in
theorem inputSize : N = shapeN a S + (coarseN i S+1) := by
  have h := outputSize ha hi
  omega

def outputVertices : Fin (N+1) ≃ Fin (coarseN i S+(shapeN a S+1)+1) :=
  (anchoredPartitionEquiv ha hi).symm.trans (outputVertexEquiv (coarseN i S) (shapeN a S+1))

def inputVertices : Fin (N+1) ≃ Fin (shapeN a S+(coarseN i S+1)+1) :=
  (anchoredPartitionEquiv ha hi).symm.trans (inputVertexEquiv (shapeN a S) (coarseN i S+1))

def outputPermutation : Equiv.Perm (Fin (coarseN i S+(shapeN a S+1)+1)) :=
  (finCongr (congrArg (·+1) (outputSize ha hi))).symm.trans (outputVertices ha hi)

def inputPermutation : Equiv.Perm (Fin (shapeN a S+(coarseN i S+1)+1)) :=
  (finCongr (congrArg (·+1) (inputSize ha hi))).symm.trans (inputVertices ha hi)

theorem outputVertices_mem_binaryBlock (v : Fin (N+1)) :
    outputVertices ha hi v ∈ binaryBlock (coarseN i S) (shapeN a S+1) ↔ v ∈ S := by
  by_cases hv : v ∈ S
  · simp only [outputVertices, Equiv.trans_apply, partition_symm_inside ha hi _ hv,
      outputVertexEquiv_inner]
    simp [binaryBlock, hv]
  · simp only [outputVertices, Equiv.trans_apply, partition_symm_outside ha hi _ hv,
      outputVertexEquiv_outer]
    simp [binaryBlock_not_vector, hv]

theorem inputVertices_mem_binaryBlock (v : Fin (N+1)) :
    inputVertices ha hi v ∈ binaryBlock (shapeN a S) (coarseN i S+1) ↔ v ∉ S := by
  by_cases hv : v ∈ S
  · simp only [inputVertices, Equiv.trans_apply, partition_symm_inside ha hi _ hv,
      inputVertexEquiv_inner]
    simp [binaryBlock_not_vector, hv]
  · simp only [inputVertices, Equiv.trans_apply, partition_symm_outside ha hi _ hv,
      inputVertexEquiv_outer]
    simp [binaryBlock, hv]

theorem outputPermutation_mem_binaryBlock (v : Fin (coarseN i S+(shapeN a S+1)+1)) :
    outputPermutation ha hi v ∈ binaryBlock (coarseN i S) (shapeN a S+1) ↔
      (finCongr (congrArg (·+1) (outputSize ha hi))).symm v ∈ S :=
  outputVertices_mem_binaryBlock ha hi _

theorem inputPermutation_mem_binaryBlock (v : Fin (shapeN a S+(coarseN i S+1)+1)) :
    inputPermutation ha hi v ∈ binaryBlock (shapeN a S) (coarseN i S+1) ↔
      (finCongr (congrArg (·+1) (inputSize ha hi))).symm v ∉ S :=
  inputVertices_mem_binaryBlock ha hi _

variable (H : VectorGraph N 2)

theorem outputPhysicalCarrier_eq_internal (hv : H.vertex ∉ S) (hlt : l < u) (hs : shapeM l u = 2) :
    outputPhysicalCarrier H ha hi hv hlt hs =
      internalGraphEquiv (outputPermutation ha hi) 2 (castVertices (outputSize ha hi) H) := by
  apply vectorGraph_eq_internal_cast (outputSize ha hi) (outputVertices ha hi)
    (outputRelabelling H ha hi hv hlt hs) (outputRelabelling_vertices H ha hi hv hlt hs)
  change vectorEmbedding _ _ (outputVectorIndex H hi hv) = outputVertices ha hi H.vertex
  simp only [outputVertices, Equiv.trans_apply, partition_symm_outside ha hi _ hv,
    outputVertexEquiv_outer]
  rfl

theorem inputPhysicalCarrier_eq_internal (hv : H.vertex ∈ S) (hlt : l < u) (hs : shapeM l u = 1) :
    inputPhysicalCarrier H ha hi hv hlt hs =
      internalGraphEquiv (inputPermutation ha hi) 2 (castVertices (inputSize ha hi) H) := by
  apply vectorGraph_eq_internal_cast (inputSize ha hi) (inputVertices ha hi)
    (inputRelabelling H ha hi hv hlt hs) (inputRelabelling_vertices H ha hi hv hlt hs)
  change vectorEmbedding _ _ (inputVectorIndex H ha hv) = inputVertices ha hi H.vertex
  simp only [inputVertices, Equiv.trans_apply, partition_symm_inside ha hi _ hv,
    inputVertexEquiv_inner]
  rfl

end Actual
end EnvelopingIsomorphism.Deformation.MixedRealCarrierRelabelling
