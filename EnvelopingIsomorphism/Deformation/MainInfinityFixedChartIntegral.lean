import EnvelopingIsomorphism.Deformation.MainInfinityFixedChartImage
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestExtractionDeterminant
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestWeightedSignedChange

/-! Whole original infinity-orbit integration, retaining the physical outside
anchor sign and extending by the actual original cutoff to the full face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegral
open Kontsevich Configuration ForestRadialFaceClassification
open InfinityForestSimpleCluster (lower upper)
open InfinityForestSimpleCoordinates InfinityForestFaceChangeVariables
open MainInfinityFixedChartImage OrientedFormChangeVariables
open Set MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

def simpleRegion : Set (Coord r) := {y |
  (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
    ((simpleCoordinates hdim x o q ho hq hne hall).symm y)).OpenConditions (lower x o) (upper x o)}

theorem measurableSet_simpleRegion : MeasurableSet (simpleRegion hdim x o q ho hq hne hall) :=
  ((BoundaryAnchoredInfinityFreeCoordinates.isOpen_openConditions (a := (0 : Fin (n+1))) (o := q)
    (lower x o) (upper x o)).preimage
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding.continuous.comp
        (simpleCoordinates hdim x o q ho hq hne hall).symm.continuous)).measurableSet

def simplePoint (y : simpleRegion hdim x o q ho hq hne hall) : Compactification (0 : Fin (n+1)) m :=
  (BoundaryAnchoredInfinityFreeCoordinates.faceDomain
    ((simpleCoordinates hdim x o q ho hq hne hall).symm y.val) y.property).toDomain.insertion

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)

def simpleCutoff (y : Coord r) : ℝ :=
  if hy : y ∈ simpleRegion hdim x o q ho hq hne hall then
    CompactDRAmbientPartition.cutoff 0 ρ (simplePoint hdim x o q ho hq hne hall ⟨y,hy⟩) else 0

theorem nativeCutoff_eq (z : ForestRadialFaceLocalization.source hdim x o) :
    ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val =
      CompactDRAmbientPartition.cutoff 0 ρ (PairedForestSimpleOverlap.facePoint hdim x o z) :=
  ChartCutoffSupport.zeroPullback_source _ _ z.property.2

theorem map_mem_simpleRegion (z : ForestRadialFaceLocalization.source hdim x o) :
    map hdim x o q ho hq hne hall z.val ∈ simpleRegion hdim x o q ho hq hne hall := by
  change (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
    ((simpleCoordinates hdim x o q ho hq hne hall).symm ((simpleCoordinates hdim x o q ho hq hne hall)
      (coordinates hdim x o q z.val)))).OpenConditions _ _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact coordinates_mem_source hdim x o q ho hq hne z

theorem simpleCutoff_map (z : ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o q ho hq hne hall ρ (map hdim x o q ho hq hne hall z.val) =
      ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val := by
  rw [simpleCutoff, dif_pos (map_mem_simpleRegion hdim x o q ho hq hne hall z), nativeCutoff_eq]
  congr 1
  unfold simplePoint map
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact facePoint_coordinates hdim x o q ho hq hne z

variable (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)

include hρ in
theorem simpleCutoff_eq_zero_off_image (y : Coord r)
    (hy : y ∉ map hdim x o q ho hq hne hall '' ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o q ho hq hne hall ρ y = 0 := by
  by_contra hn
  have hs : y ∈ simpleRegion hdim x o q ho hq hne hall := by
    by_contra hs
    exact hn (by simp only [simpleCutoff, dif_neg hs])
  have hw : CompactDRAmbientPartition.cutoff 0 ρ (simplePoint hdim x o q ho hq hne hall ⟨y,hs⟩) ≠ 0 := by
    simpa only [simpleCutoff, dif_pos hs] using hn
  have ht := ForestChartOrientation.smallChart_target_subset 0 x (hρ (subset_tsupport _ hw))
  obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o q ho hq hne
    ((simpleCoordinates hdim x o q ho hq hne hall).symm y) hs ht
  apply hy
  refine ⟨z.val,z.property,?_⟩
  rw [map,hz,ContinuousLinearEquiv.apply_symm_apply]

include hρ in
theorem integral_image_eq_integral_simpleRegion (f : Coord r → ℝ) :
    (∫ y in map hdim x o q ho hq hne hall '' ForestRadialFaceLocalization.source hdim x o,
      simpleCutoff hdim x o q ho hq hne hall ρ y * f y) =
    ∫ y in simpleRegion hdim x o q ho hq hne hall,
      simpleCutoff hdim x o q ho hq hne hall ρ y * f y := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_simpleRegion hdim x o q ho hq hne hall)
  · rintro y ⟨z,hz,rfl⟩
    exact map_mem_simpleRegion hdim x o q ho hq hne hall ⟨z,hz⟩
  · intro y hy
    rw [simpleCutoff_eq_zero_off_image hdim x o q ho hq hne hall ρ hρ y hy.2,zero_mul]

include hρ in
theorem signed_integral_eq_full_weighted_integral
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (ε * (-((-1 : ℝ) ^ (axis hdim x o).val))) *
      (∫ z in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density (nativeForm hdim x o edges) z) =
    (BoundaryAnchoredInfinityData.referenceSign (lower x o) q * (-1 : ℝ)^q.val) *
      (∫ y in simpleRegion hdim x o q ho hq hne hall,
        simpleCutoff hdim x o q ho hq hne hall ρ y * density (simpleForm hdim x o q ho hq hne hall edges) y) := by
  rw [← integral_image_eq_integral_simpleRegion hdim x o q ho hq hne hall ρ hρ,
    ← integral_const_mul, ← integral_const_mul,
    integral_image_source hdim x o q ho hq hne hall
      _ (ForestRadialFaceLocalization.measurableSet_source hdim x o) (fun _ h ↦ h)]
  apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
  intro z hz
  dsimp only
  rw [simpleCutoff_map hdim x o q ho hq hne hall ρ ⟨z,hz⟩]
  by_cases hzero : ForestFaceCutoffIntegrability.cutoff hdim x o ρ z = 0
  · simp only [hzero,zero_mul,mul_zero]
  · have hn := hzero
    rw [nativeCutoff_eq hdim x o ρ ⟨z,hz⟩] at hn
    have hsmall := PairedForestOverlapJacobian.smallFace_of_point_mem_smallChart hdim x o ⟨z,hz⟩
      (hρ (subset_tsupport _ hn))
    have hsign := InfinityForestPhysicalExtraction.native_face_orientation_slot
      hdim x o q ho hq hne hall ⟨z,hz⟩ hsmall ε hε
    rw [native_density_eq_jacobian hdim x o q ho hq hne hall ⟨z,hz⟩]
    linear_combination (ForestFaceCutoffIntegrability.cutoff hdim x o ρ z *
      density (simpleForm hdim x o q ho hq hne hall edges) (map hdim x o q ho hq hne hall z)) * hsign

include hρ in
theorem oriented_contribution_eq_full_weighted_integral
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * ForestRadialFaceClassification.contribution hdim x
      (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ) o =
    (BoundaryAnchoredInfinityData.referenceSign (lower x o) q * (-1 : ℝ)^q.val) *
      (∫ y in simpleRegion hdim x o q ho hq hne hall,
        simpleCutoff hdim x o q ho hq hne hall ρ y * density
          (simpleForm hdim x o q ho hq hne hall
            (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) y) := by
  rw [ForestRadialFaceLocalization.contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  simp only [smul_eq_mul, ← mul_assoc]
  have he :
      (∫ z in ForestRadialFaceLocalization.source hdim x o,
        facePullback (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ)
          (axis hdim x o) 0 z (standardBasis r)) =
      ∫ z in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density
          (nativeForm hdim x o (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) z := by
    apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
    intro z hz
    exact ForestFaceCutoffIntegrability.local_density_eq hdim x o ρ edges hloop κ hmatch z hz
  rw [he]
  exact signed_integral_eq_full_weighted_integral hdim x o q ho hq hne hall ρ hρ ε hε _

end EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegral
