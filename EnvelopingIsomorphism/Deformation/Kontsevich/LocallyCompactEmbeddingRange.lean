import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Separation.Hausdorff

/-! A locally compact subspace of a Hausdorff space is locally closed.
The proof uses actual compact neighborhoods and the embedding's induced topology. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Filter Set
open scoped Topology

theorem isLocallyClosed_range_of_isEmbedding {X Y : Type*}
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsEmbedding f) : IsLocallyClosed (Set.range f) := by
  apply ((isLocallyClosed_tfae (Set.range f)).out 0 3).mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  rw [hf.isInducing.nhds_eq_comap x] at hKx
  obtain ⟨V, hV, hVK⟩ := Filter.mem_comap.mp hKx
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
  have hsub : W ∩ Set.range f ⊆ f '' K := by
    rintro _ ⟨hyW, y, rfl⟩
    exact ⟨y, hVK (hWV hyW), rfl⟩
  have hclosed : IsClosed (f '' K) := (hKc.image hf.continuous).isClosed
  refine ⟨W, hxW, hW, ?_⟩
  exact (hW.inter_closure.trans (closure_minimal hsub hclosed)).trans (Set.image_subset_range f K)

end EnvelopingIsomorphism.Deformation.Kontsevich
