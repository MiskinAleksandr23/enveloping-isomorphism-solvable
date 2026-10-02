import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterOriginalCoverage
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterLocalCompact
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterEmbedding
import EnvelopingIsomorphism.Deformation.Kontsevich.LocallyCompactEmbeddingRange
import EnvelopingIsomorphism.Deformation.Kontsevich.DenseOpenCoverage

/-! Actual local image coverage at a simple pure external-cluster face.
Explicit reconstruction covers the original configurations in a proved open
positional region. Local compactness and the proved embedding make the image
locally closed. Density then supplies an ambient open neighborhood in the image. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain

open Configuration Set Topology

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

theorem isLocallyClosed_range_insertion :
    IsLocallyClosed (Set.range (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m)) :=
  isLocallyClosed_range_of_isEmbedding isEmbedding_insertion

theorem insertion_eq_boundaryPoint_of_scale_zero (x : PureBoundaryClusterDomain i m l u a b)
    (hr : x.scale = 0) : x.insertion = x.datum.boundaryPoint := by
  apply Subtype.ext
  change x.datum.resolvedCoordinates x.scale = x.datum.resolvedCoordinates 0
  rw [hr]

/-- Every simple pure boundary-cluster point has an actual ambient open
neighborhood contained in the image of its genuine parameter insertion. -/
theorem exists_open_neighborhood_in_image (x : PureBoundaryClusterDomain i m l u a b)
    (hr : x.scale = 0) :
    ∃ V : Set (Compactification i m), IsOpen V ∧ x.insertion ∈ V ∧
      V ⊆ pureBoundaryClusterOriginalCoverageRegion i m l u a ∩
        Set.range (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m) := by
  have hxU : x.insertion ∈ pureBoundaryClusterOriginalCoverageRegion i m l u a := by
    rw [x.insertion_eq_boundaryPoint_of_scale_zero hr]
    exact boundaryPoint_mem_pureBoundaryClusterOriginalCoverageRegion x.datum
  exact exists_open_subset_of_dense_coverage
    (denseRange_compactificationEmbedding i)
    (isOpen_pureBoundaryClusterOriginalCoverageRegion i m l u a)
    isLocallyClosed_range_insertion
    (original_coverage_in_pureBoundaryClusterRegion x.datum.left_endpoint
      x.datum.right_endpoint x.datum.endpoint_lt) hxU ⟨x, rfl⟩

theorem mem_interior_range_insertion (x : PureBoundaryClusterDomain i m l u a b)
    (hr : x.scale = 0) :
    x.insertion ∈ interior (Set.range
      (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m)) := by
  obtain ⟨V, hV, hxV, hsub⟩ := x.exists_open_neighborhood_in_image hr
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds hxV)
    (fun z hz => (hsub hz).2))

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain
