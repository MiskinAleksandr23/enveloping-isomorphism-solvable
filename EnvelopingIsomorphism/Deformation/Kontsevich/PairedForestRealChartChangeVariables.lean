import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCommonRealDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestPeriodicDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestChartVolume
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductSign

/-! Signed graph-form change of variables through the actual canonically
marked, integer-translated real chart. All auxiliary volume and density
factors are proved, and the outward face sign is the computed -1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealChartChangeVariables
open Configuration InteriorGraphFaceCoordinates PairedForestSimpleCluster PairedForestSmoothProduct
open PairedForestProductChart SimpleFaceNativeAtlas SimpleProductPhaseIdentification SimpleFaceChartPoint
open PairedForestCommonRealDensity PairedForestProductGraphDensity PairedForestOverlapJacobian
open MeasureTheory Set BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  {a b : Fin (n+1)} {T : Finset (Fin (n+1))}
  (ha : a ∈ T) (hb : b ∈ T) (hba : b ≠ a) (hg : (0 : Fin (n+1)) ∈ T → a = 0)
  (c : ChartIndex hdim a b T)

def targetRealHomeomorph : Product c.center c.orbit c.paired ≃ₜ RealProductCoordinates 0 a b T m :=
  (targetHomeomorph hdim c).trans InteriorGraphFaceCoordinates.toProduct.symm.toHomeomorph

theorem volume_preserving_targetRealHomeomorph : MeasurePreserving (targetRealHomeomorph hdim c) :=
  (MeasurePreserving.symm InteriorGraphFaceCoordinates.toProduct.toHomeomorph.toMeasurableEquiv
    PairedForestChartVolume.volume_preserving_toProduct).comp
    (PairedForestChartVolume.volume_preserving_targetHomeomorph hdim c)

theorem realChart_image_eq (s : Set (Coord r)) :
    realChart hdim c '' s = targetRealHomeomorph hdim c ''
      (localChart hdim c.center c.orbit c.paired c.point '' s) := by
  rw [image_image]
  rfl

/-- The actual target coefficient including the original ambient cutoff. -/
def weightedDensity (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (es : Fin r → GraphForms.Edge n m) (y : RealProductCoordinates 0 a b T m) : ℝ :=
  ρ (CompactDRCoordinates.realCoordinates (n+1) m (InteriorFaceDRCoordinates.ambient (InteriorGraphFaceCoordinates.toProduct y))) *
    realFaceDensity (PairedForestCommonRealDensity.edges hdim ha hb hba hg es) y

theorem weightedDensity_targetRealHomeomorph
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (es : Fin r → GraphForms.Edge n m)
    (hne : ∀ q, (es q).target ≠ Sum.inl (es q).source)
    (p : Product c.center c.orbit c.paired) (hp : (toAngular p).toFree.OpenConditions) :
    weightedDensity hdim ha hb hba hg ρ es (targetRealHomeomorph hdim c p) =
      productCutoff c.center c.orbit c.paired ρ p * productDensity hdim c.center c.orbit c.paired es p := by
  have hD : InteriorFaceDRCoordinates.ambient (shift c.turn p) = InteriorFaceDRCoordinates.ambient p :=
    PairedForestCanonicalProductCoverage.ambient_turn (anchor_mem c.center c.orbit c.paired)
      (reference_mem c.center c.orbit c.paired) (anchor_global c.center c.orbit c.paired) c.turn p hp
  unfold weightedDensity
  change ρ (CompactDRCoordinates.realCoordinates (n+1) m
    (InteriorFaceDRCoordinates.ambient (InteriorGraphFaceCoordinates.toProduct
      (InteriorGraphFaceCoordinates.toProduct.symm (shift c.turn (nativeEquiv hdim c p)))))) *
    realFaceDensity _ (InteriorGraphFaceCoordinates.toProduct.symm (shift c.turn (nativeEquiv hdim c p))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ← nativeEquiv_shift,
    ambient_nativeEquiv, hD, ← productDensity_eq_common hdim ha hb hba hg c,
    PairedForestPeriodicDensity.productDensity_shift hdim c.center c.orbit c.paired es hne p hp]
  rfl

theorem measurableSet_localChart_image (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim c.center c.orbit c.paired c.point).source) :
    MeasurableSet (localChart hdim c.center c.orbit c.paired c.point '' s) := by
  let e := localChart hdim c.center c.orbit c.paired c.point
  have hm := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr
    (hs.preimage measurable_subtype_coe)
  have he : (e.source.restrict e) '' (Subtype.val ⁻¹' s) = e '' s := by
    ext y
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.val,hw,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w,hsub hw⟩,hw,rfl⟩
  rwa [he] at hm

/-- Literal signed native graph integral equals minus the same graph integral
in common real coordinates. No periodicity, orientation or CV identity is
supplied as a premise. -/
theorem signed_integral_realChart_image
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (es : Fin r → GraphForms.Edge n m)
    (hne : ∀ q, (es q).target ≠ Sum.inl (es q).source)
    (κ : ForestOrthantRealization.Ambient 0 c.center → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement c.center ρ es hne κ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 c.center).target)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim c.center,
      ε * OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim c.center) y =
        |OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim c.center) y|)
    (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (localChart hdim c.center c.orbit c.paired c.point).source) :
    (ε * -((-1 : ℝ) ^ (ForestRadialFaceClassification.axis hdim c.center c.orbit).val)) *
      (∫ w in s, NativePairedFaceIntegration.nativeDensity hdim c.center c.orbit ρ es hne κ w) =
      -(∫ y in realChart hdim c '' s, weightedDensity hdim ha hb hba hg ρ es y) := by
  rw [PairedForestIntrinsicReassembly.signed_integral_eq hdim c.center c.orbit c.paired
    ρ es hne κ hmatch hρ ε hε c.point s hs hsub,
    PairedForestProductSign.productFaceSign_eq_neg_one, neg_one_mul]
  congr 1
  rw [realChart_image_eq,
    (volume_preserving_targetRealHomeomorph hdim c).setIntegral_image_emb
      (targetRealHomeomorph hdim c).toMeasurableEquiv.measurableEmbedding]
  apply setIntegral_congr_fun (measurableSet_localChart_image hdim c s hs hsub)
  rintro p ⟨w,hw,rfl⟩
  exact (weightedDensity_targetRealHomeomorph hdim ha hb hba hg c ρ es hne _
    (PairedForestProductOverlap.toProduct_openConditions hdim c.center c.orbit c.paired
      (phase hdim c.center c.orbit c.paired c.point)
      ⟨w,localChart_source_subset hdim c.center c.orbit c.paired c.point (hsub hw)⟩)).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealChartChangeVariables
