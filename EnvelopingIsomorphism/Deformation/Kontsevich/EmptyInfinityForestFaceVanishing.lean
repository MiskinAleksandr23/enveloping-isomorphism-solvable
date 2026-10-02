import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing

/-! Empty-boundary infinity strata have vanishing actual native graph forms
and localized contributions whenever there are at least two external labels.
No graph valence or nonzero-density assumption is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceVanishing
open Configuration ForestRadialFaceClassification ForestRadialFaceLocalization
open ForestGlobalGraphStokes BoxStokes MeasureTheory
open EmptyInfinityForestSimpleCluster
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (RealForestCoarsePositions.node x o).val)
  (hm : 2 ≤ m)

include ho hempty hm in
theorem nativeForm_eq_zero (edges : Fin r → ForestGraphTopForms.Edge (n+1) m)
    (z : source hdim x o) :
    RealForestFaceChangeVariables.nativeForm hdim x o edges z.val = 0 := by
  let q : Fin m := ⟨0,by omega⟩
  let s := slot hdim x o ho hempty z
  have hq : q ∉ boundaryClusterBlock s s := by simp [boundaryClusterBlock_self]
  have hshape : GraphForms.dimension (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1)))
      (InfinityBoundaryGraphFactorization.shapeM s s) < r := by
    have hc : InfinityBoundaryGraphFactorization.shapeM s s =
        (boundaryClusterBlock s s).card := Fintype.card_coe _
    simp only [GraphForms.dimension, InfinityBoundaryGraphFactorization.shapeN,
      card_boundaryAnchoredInfinityFreeInterior, hc, boundaryClusterBlock_self, Finset.card_empty]
    dsimp [GraphForms.dimension] at hdim
    omega
  have hz := InfinityBoundaryGraphFactorization.graphForm_face_eq_zero_of_shape_dimension_lt
    (a := (0 : Fin (n+1))) hq (fun j ↦ ((edges j).source,(edges j).target)) hshape
    (InfinityForestSimpleCoordinates.coordinates hdim x o q z.val)
    (coordinates_mem_source hdim x o ho hempty q z)
  rw [RealForestFaceChangeVariables.nativeForm,
    EmptyInfinityForestFaceForms.graphForm_eq_simple hdim x o ho hempty q z]
  ext V
  exact congrArg (fun ω ↦ ω (fun j ↦
    (fderiv ℝ (InfinityForestSimpleCoordinates.coordinates hdim x o q) z.val) (V j))) hz

include ho hempty hm in
theorem nativeDensity_eq_zero
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ edges hloop κ) (z : source hdim x o) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ z.val = 0 :=
  EmptyRealForestFaceVanishing.local_density_eq_zero_of_nativeForm_eq_zero hdim x o z
    ρ edges hloop κ hmatch (nativeForm_eq_zero hdim x o ho hempty hm _ z)

include ho hempty hm in
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
    exact nativeDensity_eq_zero hdim x o ho hempty hm ρ edges hloop κ hmatch ⟨w,hw⟩
  rw [hz,smul_zero]

omit hempty in
include ho hm in
theorem contribution_eq_zero_of_block_empty
    (hblock : boundaryClusterBlock (InfinityForestSimpleCluster.lower x o)
      (InfinityForestSimpleCluster.upper x o) = ∅)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ edges hloop κ) :
    contribution hdim x (localForm hdim x ρ edges hloop κ) o = 0 := by
  apply contribution_eq_zero hdim x o ho _ hm ρ edges hloop κ hmatch
  intro j hj
  have h := (RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) j).mp hj
  rw [hblock] at h
  exact Finset.notMem_empty j h

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceVanishing
