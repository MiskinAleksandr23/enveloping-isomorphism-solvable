import EnvelopingIsomorphism.Deformation.MixedRealCarrierRelabelling
import EnvelopingIsomorphism.Deformation.MixedRealPhysicalSubsetCoefficients
import EnvelopingIsomorphism.Deformation.MixedRealPhysicalIndex

/-! Each normalized physical real face equals its individual coefficient at
the original binary subset; the complementary input faces have negative sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealPhysicalCoefficientMatching
open Kontsevich MixedGraphProfileCarrier MixedGraphTargetProfiles MixedGraphAveraging
open MixedGraphBlockRelabelling MixedGraphLabelledClusterCounting GraphLabelledClusterCounting
open MixedRealGraftPhysicalCoefficient MixedRealCarrierRelabelling
open MixedRealPhysicalClusterCoefficients MixedRealPhysicalSubsetCoefficients
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
open MixedRealPhysicalFaces MixedRealPhysicalIndex
open scoped Classical

section Cluster
variable {N : ℕ} {i a : Fin (N+1)} {S : Finset (Fin (N+1))}
variable (ha : a ∈ S) (hi : i ∉ S)

def outputCluster : Clusters (binaryBlock (coarseN i S) (shapeN a S+1)) :=
  movedCluster _ (outputPermutation ha hi).symm

def inputCluster : Clusters (binaryBlock (shapeN a S) (coarseN i S+1)) :=
  movedCluster _ (inputPermutation ha hi).symm

theorem outputCluster_mem (v : Fin (coarseN i S+(shapeN a S+1)+1)) :
    v ∈ (outputCluster ha hi).val ↔ (finCongr (congrArg (·+1) (outputSize ha hi))).symm v ∈ S := by
  have hm := (movedCluster_eq_iff _ _ (outputCluster ha hi)).mp rfl (outputPermutation ha hi v)
  rw [Equiv.symm_apply_apply] at hm
  exact hm.trans (outputPermutation_mem_binaryBlock ha hi v)

theorem inputCluster_mem (v : Fin (shapeN a S+(coarseN i S+1)+1)) :
    v ∈ (inputCluster ha hi).val ↔ (finCongr (congrArg (·+1) (inputSize ha hi))).symm v ∈ Sᶜ := by
  have hm := (movedCluster_eq_iff _ _ (inputCluster ha hi)).mp rfl (inputPermutation ha hi v)
  rw [Equiv.symm_apply_apply] at hm
  exact hm.trans ((inputPermutation_mem_binaryBlock ha hi v).trans (Finset.mem_compl).symm)

theorem outputCluster_map :
    (outputCluster ha hi).val.map (finCongr (congrArg (·+1) (outputSize ha hi).symm)).toEmbedding = S := by
  apply Finset.ext
  intro v
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (outputCluster_mem ha hi w).mp hw
  · intro hv
    refine ⟨finCongr (congrArg (·+1) (outputSize ha hi)) v,?_,?_⟩
    · exact (outputCluster_mem ha hi _).mpr (by simpa using hv)
    · rfl

theorem inputCluster_map :
    (inputCluster ha hi).val.map (finCongr (congrArg (·+1) (inputSize ha hi).symm)).toEmbedding = Sᶜ := by
  apply Finset.ext
  intro v
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (inputCluster_mem ha hi w).mp hw
  · intro hv
    refine ⟨finCongr (congrArg (·+1) (inputSize ha hi)) v,?_,?_⟩
    · exact (inputCluster_mem ha hi _).mpr (by simpa using hv)
    · rfl

end Cluster

variable {N : ℕ} (H : VectorGraph N 2) (K : Key N H.vertex)

theorem normalized_physicalValue_eq_outputCoefficient (hv : H.vertex ∉ K.S) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H K = outputCoefficient H K.S := by
  rw [normalized_physicalValue_eq_outputProfile H K hv,
    outputPhysicalCarrier_eq_internal,
    outputCoefficient_eq_of_count (outputSize K.inside_mem K.outside_not_mem).symm H
      (outputCluster K.inside_mem K.outside_not_mem) K.S (outputCluster_map _ _),
    outputCluster,
    rawOutputClusterCoefficient_eq _ _
      ⟨(outputPermutation K.inside_mem K.outside_not_mem).symm,
        (movedCluster_eq_iff _ _ _).mp rfl⟩,
    internalGraphEquiv_symm_apply]
  rfl

theorem normalized_physicalValue_eq_neg_inputCoefficient (hv : H.vertex ∈ K.S) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H K =
      -inputCoefficient (physicalInputSlot K.block_lt (inputShapeM H K hv)) H K.Sᶜ := by
  rw [normalized_physicalValue_eq_neg_inputProfile H K hv,
    inputPhysicalCarrier_eq_internal,
    inputCoefficient_eq_of_count _ (inputSize K.inside_mem K.outside_not_mem).symm H
      (inputCluster K.inside_mem K.outside_not_mem) K.Sᶜ (inputCluster_map _ _),
    inputCluster,
    rawInputClusterCoefficient_eq _ _ _
      ⟨(inputPermutation K.inside_mem K.outside_not_mem).symm,
        (movedCluster_eq_iff _ _ _).mp rfl⟩,
    internalGraphEquiv_symm_apply]
  rfl

theorem normalized_outputKey (T : BinarySubset H.vertex) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H (outputKey T) = outputCoefficient H T.val :=
  normalized_physicalValue_eq_outputCoefficient H (outputKey T) T.property.2

theorem normalized_inputKey (T : BinarySubset H.vertex) (r : Fin 2) :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H (inputKey T r) = -inputCoefficient r H T.val := by
  have hv : H.vertex ∈ (inputKey T r).S := Finset.mem_compl.mpr T.property.2
  rw [normalized_physicalValue_eq_neg_inputCoefficient H (inputKey T r) hv]
  have hr : physicalInputSlot (inputKey T r).block_lt (inputShapeM H (inputKey T r) hv) = r := by
    apply Fin.ext
    rfl
  rw [hr]
  change -inputCoefficient r H T.valᶜᶜ = _
  rw [compl_compl]

end EnvelopingIsomorphism.Deformation.MixedRealPhysicalCoefficientMatching
