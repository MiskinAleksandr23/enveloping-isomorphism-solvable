import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSignedChange

/-! Signed paired-face change of variables for the original ambient forest
cutoffs. Their actual support certificate discharges the small-chart condition;
no derivatives of the cutoffs are needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open BoxStokes OrientedFormChangeVariables ForestRadialFaceClassification
open ForestOrthantRealization ForestRadialFaceDRInverse
open Set MeasureTheory
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

/-- The same ambient cutoff, evaluated on the genuine full simple-face DR array. -/
def productCutoff (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (p : Product x o ho) : ℝ :=
  ρ (CompactDRCoordinates.realCoordinates (n + 1) m (InteriorFaceDRCoordinates.ambient p))

theorem productCutoff_toProduct (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (u : Circle) (z : PairedForestSmoothProduct.Source hdim x o) :
    productCutoff x o ho ρ (toProduct hdim x o ho u z.val) =
      CompactDRAmbientPartition.cutoff 0 ρ (point hdim x o z) := by
  unfold productCutoff
  rw [PairedForestProductOverlap.ambient_toProduct hdim x o ho u z,
    ForestRadialFaceImmersion.forward_data hdim x o z]
  rfl

theorem smallFace_of_point_mem_smallChart (z : PairedForestSmoothProduct.Source hdim x o)
    (hz : point hdim x o z ∈ (ForestChartOrientation.smallChart 0 x).target) : SmallFace hdim x o z := by
  have h := hz.2
  change includeOrthant 0 x ((ForestOrthantCharts.chart 0 x).symm (point hdim x o z)) ∈
    Metric.ball (ForestChartOrientation.center 0 x) (ForestChartOrientation.radius 0 x) at h
  have hm : model hdim x o z ∈ (ForestOrthantCharts.chart 0 x).source := z.property.2
  rw [point, (ForestOrthantCharts.chart 0 x).left_inv hm] at h
  change includeOrthant 0 x (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val)) ∈ _ at h
  rw [ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x _
    (ForestRadialFaceLocalization.faceAmbient_nonneg hdim x o z.val z.property.1)] at h
  exact h

/-- Nonzero weight forces the actual source point into the oriented small chart. -/
theorem smallFace_of_productCutoff_ne_zero (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (u : Circle) (z : PairedForestSmoothProduct.Source hdim x o)
    (hn : productCutoff x o ho ρ (toProduct hdim x o ho u z.val) ≠ 0) : SmallFace hdim x o z := by
  rw [productCutoff_toProduct hdim x o ho ρ u z] at hn
  exact smallFace_of_point_mem_smallChart hdim x o z (hρ (subset_tsupport _ hn))

/-- The actual supported weight removes the need for any assumed geometric
restriction on the integration subset beyond the already built local chart. -/
theorem signed_integral_weighted_image (z : PairedForestSmoothProduct.Source hdim x o)
    (s : Set (Coord r)) (hs : MeasurableSet s) (hsub : s ⊆ (localChart hdim x o ho z).source)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (g : Product x o ho → ℝ) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      (∫ w in s, PairedForestCartesianChange.jacobian hdim x o ho z w *
        (productCutoff x o ho ρ (localChart hdim x o ho z w) * g (localChart hdim x o ho z w))) =
      productFaceSign hdim x o ho * (∫ p in localChart hdim x o ho z '' s, productCutoff x o ho ρ p * g p) := by
  rw [PairedForestCartesianChange.integral_image hdim x o ho z s hs hsub,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun hs
  intro w hw
  dsimp only
  by_cases hzweight : productCutoff x o ho ρ (localChart hdim x o ho z w) = 0
  · simp only [hzweight, zero_mul, mul_zero]
  · have hsmall := smallFace_of_productCutoff_ne_zero hdim x o ho ρ hρ (phase hdim x o ho z)
      ⟨w, localChart_source_subset hdim x o ho z (hsub hw)⟩ hzweight
    rw [← mul_assoc, cartesian_face_orientation hdim x o ho z (hsub hw) hsmall ε hε]
    ring

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
