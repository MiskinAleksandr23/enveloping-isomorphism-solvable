import EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegral

/-! Actual full-face weighted L1 follows from the original compact Stokes
form, signed change of variables and zero weight outside the native image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegrability
open Kontsevich Configuration ForestRadialFaceClassification
open InfinityForestSimpleCluster (lower upper)
open InfinityForestFaceChangeVariables OrientedFormChangeVariables MainInfinityFixedChartIntegral
open Set MeasureTheory BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))
  (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)

include hρ in
theorem integrableOn_full_weighted_density
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ)
    (hcont : Continuous (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ))
    (hcompact : HasCompactSupport (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ))
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    IntegrableOn (fun y ↦ simpleCutoff hdim x o q ho hq hne hall ρ y * density
      (simpleForm hdim x o q ho hq hne hall
        (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) y)
      (simpleRegion hdim x o q ho hq hne hall) := by
  let es := fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)
  let c : ℝ := BoundaryAnchoredInfinityData.referenceSign (lower x o) q * (-1 : ℝ)^q.val
  have hc : c ≠ 0 := mul_ne_zero (BoundaryAnchoredInfinityData.referenceSign_ne_zero _ _)
    (pow_ne_zero _ (by norm_num))
  have hi := ForestFaceCutoffIntegrability.integrableOn_cutoff_graphDensity
    hdim x o ρ edges hloop κ hmatch hcont hcompact
  have himg : IntegrableOn (fun y ↦ c * (simpleCutoff hdim x o q ho hq hne hall ρ y *
      density (simpleForm hdim x o q ho hq hne hall es) y))
      (map hdim x o q ho hq hne hall '' ForestRadialFaceLocalization.source hdim x o) := by
    apply (integrableOn_image_source_iff hdim x o q ho hq hne hall _
      (ForestRadialFaceLocalization.measurableSet_source hdim x o) (Subset.refl _) _).mpr
    apply IntegrableOn.congr_fun (hi.const_mul (ε * -((-1 : ℝ)^(axis hdim x o).val))) _
      (ForestRadialFaceLocalization.measurableSet_source hdim x o)
    intro z hz
    dsimp only
    rw [simpleCutoff_map hdim x o q ho hq hne hall ρ ⟨z,hz⟩]
    change (ε * -((-1 : ℝ)^(axis hdim x o).val)) *
      (ForestFaceCutoffIntegrability.cutoff hdim x o ρ z * density (nativeForm hdim x o es) z) = _
    by_cases hzero : ForestFaceCutoffIntegrability.cutoff hdim x o ρ z = 0
    · simp only [hzero,zero_mul,mul_zero]
    · have hn := hzero
      rw [nativeCutoff_eq hdim x o ρ ⟨z,hz⟩] at hn
      have hsmall := PairedForestOverlapJacobian.smallFace_of_point_mem_smallChart hdim x o ⟨z,hz⟩
        (hρ (subset_tsupport _ hn))
      have hsign := InfinityForestPhysicalExtraction.native_face_orientation_slot
        hdim x o q ho hq hne hall ⟨z,hz⟩ hsmall ε hε
      rw [native_density_eq_jacobian hdim x o q ho hq hne hall ⟨z,hz⟩]
      dsimp only [c]
      linear_combination (ForestFaceCutoffIntegrability.cutoff hdim x o ρ z *
        density (simpleForm hdim x o q ho hq hne hall es) (map hdim x o q ho hq hne hall z)) * hsign
  have hplain := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp himg
  apply IntegrableOn.of_forall_sdiff_eq_zero hplain (measurableSet_simpleRegion hdim x o q ho hq hne hall)
  intro y hy
  rw [simpleCutoff_eq_zero_off_image hdim x o q ho hq hne hall ρ hρ y hy.2,zero_mul]

end EnvelopingIsomorphism.Deformation.MainInfinityFixedChartIntegrability
