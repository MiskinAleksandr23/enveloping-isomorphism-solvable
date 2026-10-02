import EnvelopingIsomorphism.Deformation.MainPureFixedChartImage
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestExtractionDeterminant

/-! Original pure-face cutoffs extend from the actual chart image to the
whole physical face, with the derived outward slot orientation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPureFixedChartIntegral
open Kontsevich Configuration ForestRadialFaceClassification
open PureForestSimpleCluster (lower upper)
open PureForestSimpleCoordinates PureForestFaceChangeVariables
open MainPureFixedChartImage OrientedFormChangeVariables
open Set MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
    (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
    (a b : Fin m) (ho : kind 0 x o = .pureBoundary)
    (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
    (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)

def simpleRegion : Set (Coord r) :=
  (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm ⁻¹'
    PureBoundaryGraphDomain.nativeDomain (n := n) (l := lower x o) (u := upper x o) a b

theorem measurableSet_simpleRegion :
    MeasurableSet (simpleRegion hdim x o a b ho hl hu hab hcard) := by
  unfold simpleRegion
  rw [PureBoundaryGraphDomain.nativeDomain_eq_preimage
    (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o))
    (PureForestSimpleCluster.left_mem x o a b hl hu hab)
    (PureForestSimpleCluster.right_mem x o a b hl hu hab) hab hcard hl hu]
  exact ((GraphForms.isOpen_admissibleSet _ _).preimage
    ((PureBoundaryGraphQuotient.twoPointCoordinates
      (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) a b
      (PureForestSimpleCluster.left_mem x o a b hl hu hab)
      (PureForestSimpleCluster.right_mem x o a b hl hu hab) hab.ne hcard).continuous.comp
        (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm.continuous)).measurableSet

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)

def simpleCutoff (y : Coord r) : ℝ :=
  ρ (CompactDRCoordinates.realCoordinates (n+1) m
    (PureBoundaryFaceDR.ambient (lower x o) (upper x o) a b
      ((simpleCoordinates hdim x o a b ho hl hu hab hcard).symm y)))

theorem nativeCutoff_eq (z : ForestRadialFaceLocalization.source hdim x o) :
    ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val =
      CompactDRAmbientPartition.cutoff 0 ρ (PairedForestSimpleOverlap.facePoint hdim x o z) :=
  ChartCutoffSupport.zeroPullback_source _ _ z.property.2

theorem map_mem_simpleRegion (z : ForestRadialFaceLocalization.source hdim x o) :
    map hdim x o a b ho hl hu hab hcard z.val ∈
      simpleRegion hdim x o a b ho hl hu hab hcard := by
  change (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm
    ((simpleCoordinates hdim x o a b ho hl hu hab hcard) (coordinates hdim x o a b z.val)) ∈
      PureBoundaryGraphDomain.nativeDomain (n := n) (l := lower x o) (u := upper x o) a b
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact coordinates_mem_nativeDomain hdim x o a b ho hl hu hab z

theorem simpleCutoff_map (z : ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o a b ho hl hu hab hcard ρ
      (map hdim x o a b ho hl hu hab hcard z.val) =
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val := by
  rw [simpleCutoff, map, ContinuousLinearEquiv.symm_apply_apply,
    coordinates_eq_datum hdim x o a b ho hl hu hab z, PureBoundaryFaceDR.ambient_data,
    nativeCutoff_eq]
  change CompactDRAmbientPartition.cutoff 0 ρ
    (PureForestSimpleCluster.domain hdim x o ho a b hl hu hab z).insertion = _
  rw [PureForestResolvedCoordinates.insertion_eq_native]
  rfl

variable (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆
    (ForestChartOrientation.smallChart 0 x).target)

include hρ in
theorem simpleCutoff_eq_zero_off_image (y : Coord r)
    (hs : y ∈ simpleRegion hdim x o a b ho hl hu hab hcard)
    (hy : y ∉ map hdim x o a b ho hl hu hab hcard '' ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o a b ho hl hu hab hcard ρ y = 0 := by
  by_contra hn
  obtain ⟨D,hd⟩ := hs
  change (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) =
    (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm y at hd
  have hw : CompactDRAmbientPartition.cutoff 0 ρ D.boundaryPoint ≠ 0 := by
    simpa only [simpleCutoff, ← hd, PureBoundaryFaceDR.ambient_data,
      CompactDRAmbientPartition.cutoff, CompactDRCoordinates.embedding,
      compactProjectDR] using hn
  have ht := ForestChartOrientation.smallChart_target_subset 0 x (hρ (subset_tsupport _ hw))
  obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o a b ho hl hu hab D ht
  apply hy
  refine ⟨z.val,z.property,?_⟩
  rw [map,hz,hd,ContinuousLinearEquiv.apply_symm_apply]

include hρ in
theorem integral_image_eq_integral_simpleRegion (f : Coord r → ℝ) :
    (∫ y in map hdim x o a b ho hl hu hab hcard '' ForestRadialFaceLocalization.source hdim x o,
      simpleCutoff hdim x o a b ho hl hu hab hcard ρ y * f y) =
    ∫ y in simpleRegion hdim x o a b ho hl hu hab hcard,
      simpleCutoff hdim x o a b ho hl hu hab hcard ρ y * f y := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_simpleRegion hdim x o a b ho hl hu hab hcard)
  · rintro y ⟨z,hz,rfl⟩
    exact map_mem_simpleRegion hdim x o a b ho hl hu hab hcard ⟨z,hz⟩
  · intro y hy
    rw [simpleCutoff_eq_zero_off_image hdim x o a b ho hl hu hab hcard ρ hρ y hy.1 hy.2,
      zero_mul]

include hρ in
theorem signed_integral_eq_full_weighted_integral
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (ε * (-((-1 : ℝ) ^ (axis hdim x o).val))) *
      (∫ z in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density (nativeForm hdim x o edges) z) =
    (-1 : ℝ)^a.val * (∫ y in simpleRegion hdim x o a b ho hl hu hab hcard,
      simpleCutoff hdim x o a b ho hl hu hab hcard ρ y *
        density (simpleForm hdim x o a b ho hl hu hab hcard edges) y) := by
  rw [← integral_image_eq_integral_simpleRegion hdim x o a b ho hl hu hab hcard ρ hρ,
    ← integral_const_mul, ← integral_const_mul,
    integral_image_source hdim x o a b ho hl hu hab hcard
      _ (ForestRadialFaceLocalization.measurableSet_source hdim x o) (fun _ h ↦ h)]
  apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
  intro z hz
  dsimp only
  rw [simpleCutoff_map hdim x o a b ho hl hu hab hcard ρ ⟨z,hz⟩]
  by_cases hzero : ForestFaceCutoffIntegrability.cutoff hdim x o ρ z = 0
  · simp only [hzero,zero_mul,mul_zero]
  · have hn := hzero
    rw [nativeCutoff_eq hdim x o ρ ⟨z,hz⟩] at hn
    have hsmall := PairedForestOverlapJacobian.smallFace_of_point_mem_smallChart hdim x o ⟨z,hz⟩
      (hρ (subset_tsupport _ hn))
    have hsign := PureForestCoorientation.native_face_orientation_slot
      hdim x o a b ho hl hu hab hcard ⟨z,hz⟩ hsmall ε hε
    rw [native_density_eq_jacobian hdim x o a b ho hl hu hab hcard ⟨z,hz⟩]
    linear_combination (ForestFaceCutoffIntegrability.cutoff hdim x o ρ z *
      density (simpleForm hdim x o a b ho hl hu hab hcard edges)
        (map hdim x o a b ho hl hu hab hcard z)) * hsign

include hρ in
theorem oriented_contribution_eq_full_weighted_integral
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ) o =
      (-1 : ℝ)^a.val * (∫ y in simpleRegion hdim x o a b ho hl hu hab hcard,
        simpleCutoff hdim x o a b ho hl hu hab hcard ρ y * density
          (simpleForm hdim x o a b ho hl hu hab hcard
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
  exact signed_integral_eq_full_weighted_integral hdim x o a b ho hl hu hab hcard ρ hρ ε hε _

end EnvelopingIsomorphism.Deformation.MainPureFixedChartIntegral
