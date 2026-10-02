import EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting
import EnvelopingIsomorphism.Deformation.MixedGraphGraftFibres
import EnvelopingIsomorphism.Deformation.MixedGraphAveraging

/-! Label counting for the mixed target boundary, including the retained vector.
A physical binary cluster containing that vector has zero coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphLabelledClusterCounting
open scoped BigOperators Classical
open MixedGraphProfileCarrier MixedGraphTargetProfiles MixedGraphAveraging
open GraphLabelledClusterCounting
variable {a b n : ℕ}

/-- The actual binary graft block in the common mixed vertex order. -/
def binaryBlock (a b : ℕ) : Finset (Fin ((a + b) + 1)) :=
  Finset.univ.map (binaryEmbedding a b)

@[simp] theorem card_binaryBlock (a b : ℕ) : (binaryBlock a b).card = b := by
  simp [binaryBlock]

theorem binaryBlock_not_vector (i : Fin (a + 1)) :
    vectorEmbedding a b i ∉ binaryBlock a b := by
  simp only [binaryBlock, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
  exact fun j => binaryEmbedding_ne_vector j i

theorem inverse_internalGraphEquiv_vertex (σ : Equiv.Perm (Fin (n + 1)))
    (H : VectorGraph n 2) :
    ((internalGraphEquiv σ 2).symm H).vertex = σ.symm H.vertex := by
  apply σ.injective
  rw [Equiv.apply_symm_apply]
  exact (internalGraphEquiv_vertex σ ((internalGraphEquiv σ 2).symm H)).symm.trans
    (congrArg VectorGraph.vertex ((internalGraphEquiv σ 2).apply_symm_apply H))

variable {k : Type*} [Field k]

/-- Exact mixed internal averaging over physical clusters and their full
label fibres. No graph-weight invariance is assumed in this reindexing. -/
theorem internalAverage_eq_clusterFibers (S : Finset (Fin (n + 1)))
    (c : VectorGraph n 2 → k) (H : VectorGraph n 2) :
    internalAverage c H = ((n + 1).factorial : k)⁻¹ *
      ∑ T : Clusters S, ∑ σ : ClusterFiber S T.val,
        c ((internalGraphEquiv σ.val 2).symm H) := by
  rw [internalAverage_apply, sum_permutations_eq_sum_clusterFibers S]
  congr 2
  funext T
  congr 1
  ext σ
  simp

/-- A binary-side cluster cannot contain the actual retained vector. -/
theorem vector_outside_of_moved_binaryBlock_mem
    (σ : Equiv.Perm (Fin ((a + b) + 1))) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∈ (movedCluster (binaryBlock a b) σ).val) :
    ((internalGraphEquiv σ 2).symm H).vertex ∉ Set.range (vectorEmbedding a b) := by
  rw [inverse_internalGraphEquiv_vertex]
  have hm : σ.symm H.vertex ∈ binaryBlock a b := by
    simpa only [movedCluster, Finset.mem_map_equiv] using h
  rintro ⟨i, hi⟩
  rw [← hi] at hm
  exact binaryBlock_not_vector i hm

/-- All output-graft terms on a forbidden physical binary cluster vanish. -/
theorem outputProfile_relabel_eq_zero_of_vector_mem
    (w : VectorGraph a 1 → k) (v : UniformBinaryGraphs.BinaryGraph b 2 → k)
    (σ : Equiv.Perm (Fin ((a + b) + 1))) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∈ (movedCluster (binaryBlock a b) σ).val) :
    outputProfile w v ((internalGraphEquiv σ 2).symm H) = 0 :=
  outputProfile_eq_zero_of_vector_outside w v _
    (vector_outside_of_moved_binaryBlock_mem σ H h)

/-- Both binary input slots obey the same retained-vector cluster restriction. -/
theorem inputProfile_relabel_eq_zero_of_vector_mem (r : Fin 2)
    (w : VectorGraph a 1 → k) (v : UniformBinaryGraphs.BinaryGraph b 2 → k)
    (σ : Equiv.Perm (Fin ((a + b) + 1))) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∈ (movedCluster (binaryBlock a b) σ).val) :
    inputProfile r w v ((internalGraphEquiv σ 2).symm H) = 0 :=
  inputProfile_eq_zero_of_vector_outside r w v _
    (vector_outside_of_moved_binaryBlock_mem σ H h)

/-- The entire signed target action vanishes on the same forbidden cluster. -/
theorem actionProfile_relabel_eq_zero_of_vector_mem
    (w : VectorGraph a 1 → k) (v : UniformBinaryGraphs.BinaryGraph b 2 → k)
    (σ : Equiv.Perm (Fin ((a + b) + 1))) (H : VectorGraph (a + b) 2)
    (h : H.vertex ∈ (movedCluster (binaryBlock a b) σ).val) :
    actionProfile w v ((internalGraphEquiv σ 2).symm H) = 0 := by
  simp only [actionProfile, Pi.sub_apply,
    outputProfile_relabel_eq_zero_of_vector_mem w v σ H h,
    inputProfile_relabel_eq_zero_of_vector_mem 0 w v σ H h,
    inputProfile_relabel_eq_zero_of_vector_mem 1 w v σ H h, sub_self]

/-- Exact physical-cluster expansion of a mixed target block. The retained
vector exclusion is proved from the graph support, including the endpoint
cases a=0 or b=0; the remaining label fibre is kept explicit. -/
theorem internalAverage_actionProfile_eq_allowedClusters
    (w : VectorGraph a 1 → k) (v : UniformBinaryGraphs.BinaryGraph b 2 → k)
    (H : VectorGraph (a + b) 2) :
    internalAverage (actionProfile w v) H = ((a + b + 1).factorial : k)⁻¹ *
      ∑ T : Clusters (binaryBlock a b), if H.vertex ∈ T.val then 0 else
        ∑ σ : ClusterFiber (binaryBlock a b) T.val,
          actionProfile w v ((internalGraphEquiv σ.val 2).symm H) := by
  rw [internalAverage_eq_clusterFibers (binaryBlock a b)]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  by_cases ht : H.vertex ∈ T.val
  · rw [if_pos ht]
    apply Finset.sum_eq_zero
    intro σ _
    apply actionProfile_relabel_eq_zero_of_vector_mem w v σ.val H
    have he := (movedCluster_eq_iff (binaryBlock a b) σ.val T).mpr σ.property
    rwa [he]
  · rw [if_neg ht]

variable [CharZero k]

/-- The mixed MC factorials count a+1 velocity vertices and b binary vertices. -/
theorem sum_normalized_permutations_binaryBlock
    (f : Clusters (binaryBlock a b) → k) :
    (∑ σ : Equiv.Perm (Fin ((a + b) + 1)),
      (b.factorial : k)⁻¹ * ((a + 1).factorial : k)⁻¹ *
        f (movedCluster (binaryBlock a b) σ)) =
      ∑ T : Clusters (binaryBlock a b), f T := by
  have hc : (a + b + 1) - b = a + 1 := by omega
  simpa only [card_binaryBlock, Fintype.card_fin, hc] using
    sum_normalized_permutations_eq_cluster_sum (binaryBlock a b) f

end EnvelopingIsomorphism.Deformation.MixedGraphLabelledClusterCounting
