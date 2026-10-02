import EnvelopingIsomorphism.Deformation.GraphBinaryClusterSums
import EnvelopingIsomorphism.Deformation.GeneralGraphReindexing

/-! The physical subset coefficient from finite associator assembly equals
the literal native graft profile in any chosen physical cluster labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryClusterNativeMatching
open scoped Classical
open KontsevichGraph.General UniformBinaryGraphs GraphWeightedInsertion
open GraphLabelledClusterCounting GraphBinaryClusterSums GraphBinaryGraftFibres
open GraphCanonicalBinaryWeights
variable {a b : ℕ}

/-- Pulling the graph back to its ordered graft labels is the actual inverse
internal permutation after the uniform arity transport. -/
theorem cast_reindexForGraft_eq_permuteInternal (H : BinaryGraph (a+b) 3)
    (σ : Equiv.Perm (Fin (a+b))) :
    castGraph graftArity_two (H.reindexForGraft (o := 1) (l := 1) σ (Equiv.refl _)) =
      H.permuteInternal σ.symm := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  rw [castGraph_target, Graph.reindexForGraft, Graph.castProfileEquiv_target,
    Graph.reindex_target]
  rfl

/-- Representative labels in the subset sum can be replaced by the concrete
labels of an actual geometric face, without an invariance premise. -/
theorem rawClusterCoefficient_eq_native_graftProfile
    (r : Fin 2) (H : BinaryGraph (a+b) 3) (T : Clusters (innerBlock a b))
    (σ : Equiv.Perm (Fin (a+b))) (hσ : ∀ v, σ v ∈ T.val ↔ v ∈ innerBlock a b) :
    rawClusterCoefficient r H T =
      GraphGeneralWeightedGraft.graftProfile r (rawBinaryWeight a) (rawBinaryWeight b)
        (H.reindexForGraft (o := 1) (l := 1) σ (Equiv.refl _)) := by
  unfold rawClusterCoefficient
  rw [← graftProfile_eq_extractedCoefficient]
  rw [graftProfile_same_cluster r (rawBinaryWeight a) (rawBinaryWeight b)
    (rawBinaryWeight_permuteInternal a) (rawBinaryWeight_permuteInternal b) H T
    (clusterRepresentative (innerBlock a b) T) ⟨σ,hσ⟩]
  rw [← cast_reindexForGraft_eq_permuteInternal, graftProfile_eq_native]

/-- The same graph identity allows the geometric cluster's vertex count to
be propositionally equal to the source count rather than definitionally equal. -/
theorem cast_reindexForGraft_eq_cast_permuteInternal {N : ℕ} (h : a+b = N)
    (H : BinaryGraph N 3) (e : Fin (a+b) ≃ Fin N) :
    castGraph graftArity_two (H.reindexForGraft (o := 1) (l := 1) e (Equiv.refl _)) =
      (GraphAssociatorProfiles.castVertices h.symm H).permuteInternal
        (e.trans (finCongr h).symm).symm := by
  cases h
  simpa [GraphAssociatorProfiles.castVertices] using cast_reindexForGraft_eq_permuteInternal H e

/-- Count casts do not obstruct the actual face-labelled native graft
coefficient; in particular anchored geometric partitions can be used. -/
theorem rawClusterCoefficient_eq_native_graftProfile_of_count {N : ℕ} (h : a+b = N)
    (r : Fin 2) (H : BinaryGraph N 3) (T : Clusters (innerBlock a b))
    (e : Fin (a+b) ≃ Fin N)
    (he : ∀ v, (e.trans (finCongr h).symm) v ∈ T.val ↔ v ∈ innerBlock a b) :
    rawClusterCoefficient r (GraphAssociatorProfiles.castVertices h.symm H) T =
      GraphGeneralWeightedGraft.graftProfile r (rawBinaryWeight a) (rawBinaryWeight b)
        (H.reindexForGraft (o := 1) (l := 1) e (Equiv.refl _)) := by
  cases h
  exact rawClusterCoefficient_eq_native_graftProfile r H T e (by simpa using he)

end EnvelopingIsomorphism.Deformation.GraphBinaryClusterNativeMatching
