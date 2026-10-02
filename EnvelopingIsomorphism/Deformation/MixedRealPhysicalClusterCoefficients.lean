import EnvelopingIsomorphism.Deformation.MixedGraphClusterSums

/-! Output and input contributions of one physical binary subset, with
independence from every choice of genuine internal labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealPhysicalClusterCoefficients
open MixedGraphProfileCarrier MixedGraphTargetProfiles MixedGraphAveraging
open MixedGraphBlockRelabelling MixedGraphLabelledClusterCounting MixedGraphClusterSums
open GraphLabelledClusterCounting GraphCanonicalBinaryWeights UniformBinaryGraphs
open scoped Classical
variable {a b : ℕ}

private theorem profile_same_cluster (c : VectorGraph (a+b) 2 → ℝ)
    (hc : ∀ p q G, c (internalGraphEquiv (blockPerm p q) 2 G) = c G)
    (H : VectorGraph (a+b) 2) (T : Clusters (binaryBlock a b))
    (σ τ : ClusterFiber (binaryBlock a b) T.val) :
    c ((internalGraphEquiv σ.val 2).symm H) = c ((internalGraphEquiv τ.val 2).symm H) := by
  have hp : ∀ x, (τ.val.trans σ.val.symm) x ∈ binaryBlock a b ↔ x ∈ binaryBlock a b := by
    intro x
    have hs := σ.property (σ.val.symm (τ.val x))
    simp only [Equiv.apply_symm_apply] at hs
    exact hs.symm.trans (τ.property x)
  obtain ⟨p,q,hpq⟩ := exists_blockPerm_of_preserves (τ.val.trans σ.val.symm) hp
  simp only [internalGraphEquiv_symm_apply]
  have he : internalGraphEquiv (blockPerm p q) 2 (internalGraphEquiv τ.val.symm 2 H) =
      internalGraphEquiv σ.val.symm 2 H := by
    have heperm : τ.val.symm.trans (τ.val.trans σ.val.symm) = σ.val.symm := by
      apply Equiv.ext
      intro x
      simp
    rw [hpq, internalGraphEquiv_trans, heperm]
  rw [← he, hc]

def rawOutputClusterCoefficient (H : VectorGraph (a+b) 2) (T : Clusters (binaryBlock a b)) : ℝ :=
  outputProfile (rawVelocityWeight a) (rawBinaryWeight b)
    ((internalGraphEquiv (clusterRepresentative (binaryBlock a b) T).val 2).symm H)

def rawInputClusterCoefficient (r : Fin 2) (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) : ℝ :=
  inputProfile r (rawVelocityWeight a) (rawBinaryWeight b)
    ((internalGraphEquiv (clusterRepresentative (binaryBlock a b) T).val 2).symm H)

theorem rawOutputClusterCoefficient_eq (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (σ : ClusterFiber (binaryBlock a b) T.val) :
    rawOutputClusterCoefficient H T =
      outputProfile (rawVelocityWeight a) (rawBinaryWeight b) ((internalGraphEquiv σ.val 2).symm H) := by
  apply profile_same_cluster _ _ H T (clusterRepresentative _ T) σ
  intro p q G
  exact outputProfile_blockPerm _ _ (rawVelocityWeight_internalGraphEquiv a)
    (rawBinaryWeight_permuteInternal b) p q G

theorem rawInputClusterCoefficient_eq (r : Fin 2) (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (σ : ClusterFiber (binaryBlock a b) T.val) :
    rawInputClusterCoefficient r H T =
      inputProfile r (rawVelocityWeight a) (rawBinaryWeight b) ((internalGraphEquiv σ.val 2).symm H) := by
  apply profile_same_cluster _ _ H T (clusterRepresentative _ T) σ
  intro p q G
  exact inputProfile_blockPerm r _ _ (rawVelocityWeight_internalGraphEquiv a)
    (rawBinaryWeight_permuteInternal b) p q G

theorem rawActionClusterCoefficient_eq (H : VectorGraph (a+b) 2) (T : Clusters (binaryBlock a b)) :
    rawActionClusterCoefficient H T = rawOutputClusterCoefficient H T -
      rawInputClusterCoefficient 0 H T - rawInputClusterCoefficient 1 H T := rfl

theorem rawOutputClusterCoefficient_eq_zero_of_vector_mem (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (h : H.vertex ∈ T.val) : rawOutputClusterCoefficient H T = 0 := by
  apply outputProfile_relabel_eq_zero_of_vector_mem
  have he := (movedCluster_eq_iff (binaryBlock a b)
    (clusterRepresentative (binaryBlock a b) T).val T).mpr (clusterRepresentative _ T).property
  rwa [he]

theorem rawInputClusterCoefficient_eq_zero_of_vector_mem (r : Fin 2) (H : VectorGraph (a+b) 2)
    (T : Clusters (binaryBlock a b)) (h : H.vertex ∈ T.val) : rawInputClusterCoefficient r H T = 0 := by
  apply inputProfile_relabel_eq_zero_of_vector_mem
  have he := (movedCluster_eq_iff (binaryBlock a b)
    (clusterRepresentative (binaryBlock a b) T).val T).mpr (clusterRepresentative _ T).property
  rwa [he]

end EnvelopingIsomorphism.Deformation.MixedRealPhysicalClusterCoefficients
