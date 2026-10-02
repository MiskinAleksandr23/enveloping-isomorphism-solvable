import EnvelopingIsomorphism.Deformation.MainRealFixedChartImage
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestExplicitTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestWeightedSignedChange

/-! A whole native proper-real orbit transports to the entire physical simple
face with the same original cutoff. Reverse coverage proves zero weight off
the image; the original support certificate supplies coorientation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealFixedChartIntegral
open Kontsevich Configuration ForestRadialFaceClassification
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestSimpleCoordinates RealForestFaceChangeVariables
open MainRealFixedChartImage OrientedFormChangeVariables
open Set MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (a b : Fin (n+1)) (ho : kind 0 x o = .properReal)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)

def simpleRegion : Set (Coord r) := {y |
  (BoundaryClusterFreeCoordinates.faceEmbedding ((simpleCoordinates hdim x o a b ha hb).symm y)).OpenConditions
    (lower x o) (upper x o)}

theorem measurableSet_simpleRegion : MeasurableSet (simpleRegion hdim x o a b ha hb) :=
  ((BoundaryClusterFreeCoordinates.isOpen_openConditions (i := b) (a := a) (S := labelsSet x o)
    (lower x o) (upper x o)).preimage
      (BoundaryClusterFreeCoordinates.faceEmbedding.continuous.comp
        (simpleCoordinates hdim x o a b ha hb).symm.continuous)).measurableSet

def simplePoint (y : simpleRegion hdim x o a b ha hb) : Compactification (0 : Fin (n+1)) m :=
  anchorHomeomorph b 0
    (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o)
      ((simpleCoordinates hdim x o a b ha hb).symm y.val) y.property).datum.boundaryPoint

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)

def simpleCutoff (y : Coord r) : ℝ :=
  if hy : y ∈ simpleRegion hdim x o a b ha hb then
    CompactDRAmbientPartition.cutoff 0 ρ (simplePoint hdim x o a b ha hb ⟨y,hy⟩) else 0

theorem nativeCutoff_eq (z : ForestRadialFaceLocalization.source hdim x o) :
    ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val =
      CompactDRAmbientPartition.cutoff 0 ρ (PairedForestSimpleOverlap.facePoint hdim x o z) :=
  ChartCutoffSupport.zeroPullback_source _ _ z.property.2

include ho hne in
theorem map_mem_simpleRegion (z : ForestRadialFaceLocalization.source hdim x o) :
    map hdim x o a b ha hb z.val ∈ simpleRegion hdim x o a b ha hb := by
  change (BoundaryClusterFreeCoordinates.faceEmbedding
    ((simpleCoordinates hdim x o a b ha hb).symm ((simpleCoordinates hdim x o a b ha hb)
      (coordinates hdim x o a b z.val)))).OpenConditions _ _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact coordinates_mem_source hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne z

include ho hne in
theorem simpleCutoff_map (z : ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o a b ha hb ρ (map hdim x o a b ha hb z.val) =
      ForestFaceCutoffIntegrability.cutoff hdim x o ρ z.val := by
  rw [simpleCutoff, dif_pos (map_mem_simpleRegion hdim x o a b ho ha hb hne z), nativeCutoff_eq]
  congr 1
  unfold simplePoint map
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact facePoint_coordinates hdim x o a b ho ha hb hne z

variable (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)

include ho hne hρ in
theorem simpleCutoff_eq_zero_off_image (y : Coord r)
    (hy : y ∉ map hdim x o a b ha hb '' ForestRadialFaceLocalization.source hdim x o) :
    simpleCutoff hdim x o a b ha hb ρ y = 0 := by
  by_contra hn
  have hs : y ∈ simpleRegion hdim x o a b ha hb := by
    by_contra hs
    exact hn (by simp only [simpleCutoff, dif_neg hs])
  have hw : CompactDRAmbientPartition.cutoff 0 ρ (simplePoint hdim x o a b ha hb ⟨y,hs⟩) ≠ 0 := by
    simpa only [simpleCutoff, dif_pos hs] using hn
  have ht := ForestChartOrientation.smallChart_target_subset 0 x (hρ (subset_tsupport _ hw))
  obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o a b ho ha hb hne
    ((simpleCoordinates hdim x o a b ha hb).symm y) hs ht
  apply hy
  refine ⟨z.val,z.property,?_⟩
  rw [map,hz,ContinuousLinearEquiv.apply_symm_apply]

include ho hne hρ in
/-- Weighted extension from the actual chart image to the whole physical
simple domain needs no integrability assumption: the integrand is zero off
the image by actual reverse coverage and the original support bound. -/
theorem integral_image_eq_integral_simpleRegion (f : Coord r → ℝ) :
    (∫ y in map hdim x o a b ha hb '' ForestRadialFaceLocalization.source hdim x o,
      simpleCutoff hdim x o a b ha hb ρ y * f y) =
    ∫ y in simpleRegion hdim x o a b ha hb, simpleCutoff hdim x o a b ha hb ρ y * f y := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_simpleRegion hdim x o a b ha hb)
  · rintro y ⟨z,hz,rfl⟩
    exact map_mem_simpleRegion hdim x o a b ho ha hb hne ⟨z,hz⟩
  · intro y hy
    rw [simpleCutoff_eq_zero_off_image hdim x o a b ho ha hb hne ρ hρ y hy.2,zero_mul]

include ho hne hρ in
/-- The complete original native orbit, with its actual outward sign,
equals the full physical simple-face integral with the same original weight.
Neither a matching identity nor a support-region orientation is supplied. -/
theorem signed_integral_eq_full_weighted_integral
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (ε * (-((-1 : ℝ) ^ (axis hdim x o).val))) *
      (∫ z in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density (nativeForm hdim x o edges) z) =
    -((-1 : ℝ)^r) *
      (∫ y in simpleRegion hdim x o a b ha hb,
        simpleCutoff hdim x o a b ha hb ρ y * density (simpleForm hdim x o a b ha hb edges) y) := by
  rw [← integral_image_eq_integral_simpleRegion hdim x o a b ho ha hb hne ρ hρ,
    ← integral_const_mul, ← integral_const_mul,
    integral_image_source hdim x o a b ha hb (RealForestCoarsePositions.properReal_isFixed x o ho) hne
      _ (ForestRadialFaceLocalization.measurableSet_source hdim x o) (fun _ h => h)]
  apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
  intro z hz
  dsimp only
  rw [simpleCutoff_map hdim x o a b ho ha hb hne ρ ⟨z,hz⟩]
  by_cases hzero : ForestFaceCutoffIntegrability.cutoff hdim x o ρ z = 0
  · simp only [hzero,zero_mul,mul_zero]
  · have hn := hzero
    rw [nativeCutoff_eq hdim x o ρ ⟨z,hz⟩] at hn
    have hsmall := PairedForestOverlapJacobian.smallFace_of_point_mem_smallChart hdim x o ⟨z,hz⟩
      (hρ (subset_tsupport _ hn))
    have hsign := RealForestExplicitTransfer.native_face_orientation hdim x o a b ha hb
      (RealForestCoarsePositions.properReal_isFixed x o ho) ⟨z,hz⟩ hsmall ε hε
    rw [native_density_eq_jacobian hdim x o a b ha hb
      (RealForestCoarsePositions.properReal_isFixed x o ho) hne ⟨z,hz⟩]
    linear_combination (ForestFaceCutoffIntegrability.cutoff hdim x o ρ z *
      density (simpleForm hdim x o a b ha hb edges) (map hdim x o a b ha hb z)) * hsign

include ho hne hρ in
/-- Direct endpoint for the literal compact Stokes contribution. The
localizer and graph are those of the original chart's local form. -/
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
    -((-1 : ℝ)^r) *
      (∫ y in simpleRegion hdim x o a b ha hb,
        simpleCutoff hdim x o a b ha hb ρ y * density
          (simpleForm hdim x o a b ha hb
            (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) y) := by
  rw [ForestRadialFaceLocalization.contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  simp only [smul_eq_mul, ← mul_assoc]
  have he :
      (∫ z in ForestRadialFaceLocalization.source hdim x o,
        facePullback (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ)
          (axis hdim x o) 0 z (standardBasis r)) =
      ∫ z in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density
          (nativeForm hdim x o (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) z := by
    apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
    intro z hz
    exact ForestFaceCutoffIntegrability.local_density_eq hdim x o ρ edges hloop κ hmatch z hz
  rw [he]
  exact signed_integral_eq_full_weighted_integral hdim x o a b ho ha hb hne ρ hρ ε hε _

end EnvelopingIsomorphism.Deformation.MainRealFixedChartIntegral
