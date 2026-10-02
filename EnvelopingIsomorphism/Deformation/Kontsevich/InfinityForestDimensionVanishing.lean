import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceForms

/-! Native infinity faces with too many outside real vertices vanish in
the actual localized graph integral. This module treats nonempty blocks;
the empty-block coordinate construction is separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestDimensionVanishing
open Configuration ForestRadialFaceClassification ForestRadialFaceLocalization
open InfinityForestSimpleCluster (lower upper)
open ForestGlobalGraphStokes BoxStokes MeasureTheory
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ m-1)

include ho in
theorem exists_outside : ∃ q : Fin m, q ∉ boundaryClusterBlock (lower x o) (upper x o) := by
  obtain ⟨q,hq⟩ := ForestRadialClusterLabels.infinity_outside_boundary 0 x (representative 0 x o)
    ((kind_representative 0 x o).trans ho)
  refine ⟨q,?_⟩
  intro hq'
  exact hq ((RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) q).mpr hq')

include ho hne hblock in
theorem nativeForm_eq_zero (edges : Fin r → ForestGraphTopForms.Edge (n+1) m)
    (z : source hdim x o) :
    RealForestFaceChangeVariables.nativeForm hdim x o edges z.val = 0 := by
  obtain ⟨q,hq⟩ := exists_outside x o ho
  have hle : (boundaryClusterBlock (lower x o) (upper x o)).card ≤ m-1 := by
    have hs : boundaryClusterBlock (lower x o) (upper x o) ⊆ Finset.univ.erase q := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun he ↦ hq (he ▸ hj),Finset.mem_univ _⟩
    simpa using Finset.card_le_card hs
  have hshape : GraphForms.dimension (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1)))
      (InfinityBoundaryGraphFactorization.shapeM (lower x o) (upper x o)) < r := by
    have hc : InfinityBoundaryGraphFactorization.shapeM (lower x o) (upper x o) =
        (boundaryClusterBlock (lower x o) (upper x o)).card := Fintype.card_coe _
    simp only [GraphForms.dimension, InfinityBoundaryGraphFactorization.shapeN,
      card_boundaryAnchoredInfinityFreeInterior, hc]
    dsimp [GraphForms.dimension] at hdim
    omega
  have hz := InfinityBoundaryGraphFactorization.graphForm_face_eq_zero_of_shape_dimension_lt
    (a := (0 : Fin (n+1))) hq (fun j ↦ ((edges j).source,(edges j).target)) hshape
    (InfinityForestSimpleCoordinates.coordinates hdim x o q z.val)
    (InfinityForestSimpleCoordinates.coordinates_mem_source hdim x o q ho hq hne z)
  rw [RealForestFaceChangeVariables.nativeForm,
    InfinityForestFaceForms.graphForm_eq_simple hdim x o q ho hq hne z]
  ext V
  exact congrArg (fun ω ↦ ω (fun j ↦
    (fderiv ℝ (InfinityForestSimpleCoordinates.coordinates hdim x o q) z.val) (V j))) hz

include ho hne hblock in
theorem nativeDensity_eq_zero
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ edges hloop κ) (z : source hdim x o) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ z.val = 0 :=
  EmptyRealForestFaceVanishing.local_density_eq_zero_of_nativeForm_eq_zero hdim x o z
    ρ edges hloop κ hmatch (nativeForm_eq_zero hdim x o ho hne hblock _ z)

include ho hne hblock in
theorem contribution_eq_zero
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ edges hloop κ) :
    contribution hdim x (localForm hdim x ρ edges hloop κ) o = 0 := by
  rw [contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  have hz : (∫ w in source hdim x o,
      facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 w (standardBasis r)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro w hw
    exact nativeDensity_eq_zero hdim x o ho hne hblock ρ edges hloop κ hmatch ⟨w,hw⟩
  rw [hz,smul_zero]

include ho in
theorem exists_unique_outside_of_block_card
    (hc : (boundaryClusterBlock (lower x o) (upper x o)).card = m-1) :
    ∃ q : Fin m, q ∉ boundaryClusterBlock (lower x o) (upper x o) ∧
      ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o) := by
  obtain ⟨q,hq⟩ := exists_outside x o ho
  have hs : boundaryClusterBlock (lower x o) (upper x o) ⊆ Finset.univ.erase q := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun he ↦ hq (he ▸ hj),Finset.mem_univ _⟩
  have he : boundaryClusterBlock (lower x o) (upper x o) = Finset.univ.erase q :=
    Finset.eq_of_subset_of_card_le hs (by simpa [hc])
  refine ⟨q,hq,?_⟩
  intro j hj
  rw [he]
  exact Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestDimensionVanishing
