import EnvelopingIsomorphism.Deformation.MainRealUnconditionalWeight
import EnvelopingIsomorphism.Deformation.GraphBinaryPhysicalSubsetIndex

/-! Unconditional proper-real scalar matching. The full original forest
sum has been reassembled and its actual ordered graph integral evaluated;
only the separately classified pure-boundary and infinity endpoints remain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealGeometricMatching
open Kontsevich MainScalarBoundaryAssembly MainRealPhysicalFaces MainRealPhysicalIndex
open MainRealGraftPhysicalCoefficient GraphBinaryPhysicalSubsetIndex
open scoped Classical BigOperators
variable {n : ℕ} (H : UniformBinaryGraphs.BinaryGraph (n+2) 3)

theorem physicalCluster_map (K : Key n) :
    (physicalCluster K.inside_mem K.outside_not_mem).val.map
      (finCongr (anchoredCount K.inside_mem K.outside_not_mem)).toEmbedding = K.S := by
  ext v
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (physicalCluster_mem K.inside_mem K.outside_not_mem w).mp hw
  · intro hv
    refine ⟨(finCongr (anchoredCount K.inside_mem K.outside_not_mem)).symm v,?_,?_⟩
    · rw [physicalCluster_mem,Equiv.apply_symm_apply]
      exact hv
    · exact Equiv.apply_symm_apply _ _

theorem normalized_physicalValue_eq_coefficient (K : Key n) :
    MainPairedGeometricMatching.normalization n * physicalValue H K =
      (-1 : ℝ)^(slot K).val * coefficient H (slot K) K.S := by
  rw [MainRealUnconditionalWeight.normalized_physicalValue_eq_rawCluster]
  rw [coefficient_eq_of_count (anchoredCount K.inside_mem K.outside_not_mem) H (slot K)
    (physicalCluster K.inside_mem K.outside_not_mem) K.S (physicalCluster_map K)]

variable {H} (P : MainPartition H)

/-- Complete numerical matching of the proper-real original Stokes sum to
the actual signed raw graph coefficients, each physical subset once. -/
theorem normalization_mul_nativeKind_properReal :
    MainPairedGeometricMatching.normalization n * nativeKindBoundary P .properReal =
      ∑ S : ProperSubset n, (coefficient H 0 S.val - coefficient H 1 S.val) := by
  rw [nativeKind_properReal_eq_subsets,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [mul_add,normalized_physicalValue_eq_coefficient,normalized_physicalValue_eq_coefficient]
  simp [slot,key,sub_eq_add_neg]

/-- The actual associator sum now differs from the fully matched proper-real
sum only by the empty-subset and full-subset terms. -/
theorem realClusterSum_eq_endpoints_add_properReal :
    realClusterSum H =
      (coefficient H 0 ∅ - coefficient H 1 ∅) +
      (coefficient H 0 Finset.univ - coefficient H 1 Finset.univ) +
      MainPairedGeometricMatching.normalization n * nativeKindBoundary P .properReal := by
  rw [realClusterSum_eq_subsets,sum_subsets_eq_endpoints,normalization_mul_nativeKind_properReal]

end EnvelopingIsomorphism.Deformation.MainRealGeometricMatching
