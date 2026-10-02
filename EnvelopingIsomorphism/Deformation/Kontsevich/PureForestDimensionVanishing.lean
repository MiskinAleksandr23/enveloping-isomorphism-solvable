import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceForms

/-! Pure real blocks other than two labels give zero actual native graph
forms and zero original localized radial contributions in every graph arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestDimensionVanishing
open Configuration ForestRadialFaceClassification ForestRadialFaceLocalization
open PureForestSimpleCluster (lower upper)
open ForestGlobalGraphStokes BoxStokes MeasureTheory
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (ho : kind 0 x o = .pureBoundary)
  (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ 2)

include ho hblock in
theorem nativeForm_eq_zero (edges : Fin r → ForestGraphTopForms.Edge (n+1) m)
    (z : source hdim x o) :
    RealForestFaceChangeVariables.nativeForm hdim x o edges z.val = 0 := by
  obtain ⟨a,b,hl,hu,hab⟩ := PureForestSimpleCluster.exists_endpoints x o ho
  have hlarge : 3 ≤ (boundaryClusterBlock (lower x o) (upper x o)).card := by
    have hc := ForestRadialClusterLabels.pureBoundary_block_card 0 x (representative 0 x o)
      ((kind_representative 0 x o).trans ho)
    change 1 < (boundaryClusterBlock (lower x o) (upper x o)).card at hc
    omega
  have hd : n * 2 + m - 1 = r := by
    dsimp [GraphForms.dimension] at hdim
    omega
  have hz : PureBoundaryClusterForms.faceGraphForm (boundaryClusterBlock (lower x o) (upper x o)) a b
      (fun j ↦ ⟨(edges j).source,(edges j).target⟩) (PureForestSimpleCoordinates.coordinates hdim x o a b z.val) = 0 := by
    subst r
    exact PureBoundaryClusterForms.faceGraphForm_fullDegree_eq_zero_of_card_ge_three _ a b hlarge _ _
  rw [RealForestFaceChangeVariables.nativeForm,
    PureForestFaceForms.graphForm_eq_simple hdim x o a b ho hl hu hab z, hz]
  ext V
  rfl

include ho hblock in
theorem nativeDensity_eq_zero
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ edges hloop κ) (z : source hdim x o) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ z.val = 0 :=
  EmptyRealForestFaceVanishing.local_density_eq_zero_of_nativeForm_eq_zero hdim x o z
    ρ edges hloop κ hmatch (nativeForm_eq_zero hdim x o ho hblock _ z)

include ho hblock in
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
    exact nativeDensity_eq_zero hdim x o ho hblock ρ edges hloop κ hmatch ⟨w,hw⟩
  rw [hz,smul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestDimensionVanishing
