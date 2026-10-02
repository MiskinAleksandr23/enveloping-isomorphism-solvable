import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterOriginalCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterLocalCompact
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterEmbedding
import EnvelopingIsomorphism.Deformation.Kontsevich.LocallyCompactEmbeddingRange
import EnvelopingIsomorphism.Deformation.Kontsevich.DenseOpenCoverage

/-!
# Actual local image coverage at a simple single-cluster boundary point

The normalized domain is locally compact by its explicit finite coordinate
constraints and is topologically embedded in the actual compactification.
Every nearby original configuration has the proved normalized reconstruction.
Density promotes this to coverage of an ambient open neighborhood in the
compact closure. Image openness is a conclusion, not an input assumption.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

namespace BoundaryClusterDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem isLocallyClosed_range_insertion :
    IsLocallyClosed (Set.range (insertion : BoundaryClusterDomain i a m S l u → Compactification i m)) :=
  isLocallyClosed_range_of_isEmbedding isEmbedding_insertion

theorem insertion_eq_boundaryPoint_of_scale_zero (x : BoundaryClusterDomain i a m S l u)
    (hr : x.scale = 0) : x.insertion = x.datum.boundaryPoint := by
  apply Subtype.ext
  change x.datum.resolvedCoordinates x.scale =
    x.datum.resolvedCoordinates 0
  rw [hr]

/-- Every finite real-cluster face point has an actual ambient open neighborhood
contained in the domain image, with all original configurations reconstructed explicitly. -/
theorem exists_open_neighborhood_in_image (x : BoundaryClusterDomain i a m S l u)
    (hr : x.scale = 0) :
    ∃ V : Set (Compactification i m), IsOpen V ∧ x.insertion ∈ V ∧
      V ⊆ boundaryClusterOriginalCoverageRegion i a m S l u ∩
        Set.range (insertion : BoundaryClusterDomain i a m S l u → Compactification i m) := by
  have hxU : x.insertion ∈ boundaryClusterOriginalCoverageRegion i a m S l u := by
    rw [x.insertion_eq_boundaryPoint_of_scale_zero hr]
    exact boundaryPoint_mem_boundaryClusterOriginalCoverageRegion x.datum
  exact exists_open_subset_of_dense_coverage
    (denseRange_compactificationEmbedding i)
    (isOpen_boundaryClusterOriginalCoverageRegion i a m S l u)
    isLocallyClosed_range_insertion
    (original_coverage_in_boundaryClusterRegion x.datum.anchor_mem x.datum.normalized_not_mem x.datum.block_order) hxU ⟨x, rfl⟩

/-- A simple single-cluster boundary point is interior to the actual real-cluster chart image. -/
theorem mem_interior_range_insertion (x : BoundaryClusterDomain i a m S l u)
    (hr : x.scale = 0) :
    x.insertion ∈ interior (Set.range
      (insertion : BoundaryClusterDomain i a m S l u → Compactification i m)) := by
  obtain ⟨V, hV, hxV, hsub⟩ := x.exists_open_neighborhood_in_image hr
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds hxV)
    (fun z hz => (hsub hz).2))

end BoundaryClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
