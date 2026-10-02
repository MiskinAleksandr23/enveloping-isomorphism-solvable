import Mathlib.Topology.LocallyClosed

/-! Promote actual coverage of a dense family to local coverage of the ambient
space, when the candidate image has already been proved locally closed. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Set

variable {X : Type*} [TopologicalSpace X]

/-- An open set whose dense part lies in a closed set lies entirely in that closed set. -/
theorem open_subset_closed_of_dense {D U F : Set X} (hD : Dense D)
    (hU : IsOpen U) (hF : IsClosed F) (hcover : U ∩ D ⊆ F) : U ⊆ F := by
  intro x hx
  by_contra hn
  obtain ⟨y, hy⟩ := hD.inter_open_nonempty (U ∩ Fᶜ) (hU.inter hF.isOpen_compl)
    ⟨x, hx, hn⟩
  exact hy.1.2 (hcover ⟨hy.1.1, hy.2⟩)

/-- No compactification equations are assumed: density and actual local
closedness promote proved original-configuration coverage to a neighborhood. -/
theorem exists_open_subset_of_dense_coverage {D U S : Set X} (hD : Dense D)
    (hU : IsOpen U) (hS : IsLocallyClosed S) (hcover : U ∩ D ⊆ S)
    {x : X} (hxU : x ∈ U) (hxS : x ∈ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∩ S := by
  obtain ⟨O, F, hO, hF, rfl⟩ := hS
  have hUF : U ⊆ F := open_subset_closed_of_dense hD hU hF
    (fun y hy ↦ (hcover hy).2)
  refine ⟨U ∩ O, hU.inter hO, ⟨hxU, hxS.1⟩, ?_⟩
  intro y hy
  exact ⟨hy.1, hy.2, hUF hy.1⟩

theorem mem_interior_of_dense_coverage {D U S : Set X} (hD : Dense D)
    (hU : IsOpen U) (hS : IsLocallyClosed S) (hcover : U ∩ D ⊆ S)
    {x : X} (hxU : x ∈ U) (hxS : x ∈ S) : x ∈ interior S := by
  obtain ⟨V, hV, hxV, hVS⟩ := exists_open_subset_of_dense_coverage hD hU hS hcover hxU hxS
  exact (hV.subset_interior_iff.mpr (fun y hy ↦ (hVS hy).2)) hxV

end EnvelopingIsomorphism.Deformation.Kontsevich
