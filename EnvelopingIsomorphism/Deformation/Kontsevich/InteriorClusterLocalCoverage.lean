import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterOriginalCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterLocalCompact
import EnvelopingIsomorphism.Deformation.Kontsevich.LocallyCompactEmbeddingRange
import EnvelopingIsomorphism.Deformation.Kontsevich.DenseOpenCoverage

/-!
# Actual local image coverage at a simple single-cluster boundary point

The normalized slice is locally compact by its explicit finite coordinate
constraints and is topologically embedded in the actual compactification.
Every nearby original configuration has the proved normalized reconstruction.
Density promotes this to coverage of an ambient open neighborhood in the
compact closure. Image openness is a conclusion, not an input assumption.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

namespace NormalizedInteriorClusterSlice

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

theorem isLocallyClosed_range_insertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    IsLocallyClosed (Set.range (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m)) :=
  isLocallyClosed_range_of_isEmbedding (isEmbedding_insertion ha hb hba)

theorem insertion_eq_boundaryPoint_of_scale_zero (x : NormalizedInteriorClusterSlice i m S a b)
    (hr : x.val.scale = 0) : x.insertion = x.val.datum.toInteriorCollisionData.boundaryPoint := by
  apply Subtype.ext
  change x.val.datum.toInteriorCollisionData.resolvedCoordinates x.val.scale =
    x.val.datum.toInteriorCollisionData.resolvedCoordinates 0
  rw [hr]

/-- Every normalized simple-cluster face point has an actual ambient open neighborhood
contained in the slice image, with all original configurations reconstructed explicitly. -/
theorem exists_open_neighborhood_in_image (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hr : x.val.scale = 0) :
    ∃ V : Set (Compactification i m), IsOpen V ∧ x.insertion ∈ V ∧
      V ⊆ clusterOriginalCoverageRegion i m S a ∩
        Set.range (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m) := by
  have hanchor : i ∈ S → a = i := fun hi => x.anchor_eq_global_of_mem ha hi
  have hxU : x.insertion ∈ clusterOriginalCoverageRegion i m S a := by
    rw [x.insertion_eq_boundaryPoint_of_scale_zero hr]
    exact boundaryPoint_mem_clusterOriginalCoverageRegion x.val.datum ha
  exact exists_open_subset_of_dense_coverage
    (denseRange_compactificationEmbedding i)
    (isOpen_clusterOriginalCoverageRegion i m S a)
    (isLocallyClosed_range_insertion ha hb hba)
    (original_coverage_in_clusterRegion ha hb hba hanchor) hxU ⟨x, rfl⟩

/-- A simple single-cluster boundary point is interior to the actual normalized chart image. -/
theorem mem_interior_range_insertion (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hr : x.val.scale = 0) :
    x.insertion ∈ interior (Set.range
      (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m)) := by
  obtain ⟨V, hV, hxV, hsub⟩ := x.exists_open_neighborhood_in_image ha hb hba hr
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds hxV)
    (fun z hz => (hsub hz).2))

end NormalizedInteriorClusterSlice

end EnvelopingIsomorphism.Deformation.Kontsevich
