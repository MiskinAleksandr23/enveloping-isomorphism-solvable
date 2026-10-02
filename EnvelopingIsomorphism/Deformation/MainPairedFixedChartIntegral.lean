import EnvelopingIsomorphism.Deformation.MainPairedFixedChartSources
import EnvelopingIsomorphism.Deformation.MainPairedSupportOrbit
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealChartChangeVariables

/-! Exact integral reassembly inside an original finite Stokes chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPairedFixedChartIntegral
open Kontsevich Configuration InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
open SimpleFaceNativeAtlas MainPairedFixedChartCover MainPairedFixedChartSources
open MainScalarBoundaryAssembly UniformBinaryGraphs Set MeasureTheory
open scoped Classical
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H) (j : P.charts)
  (T : Finset (Fin (n+2))) (hT : 1 < T.card)

def density : RealSpace T → ℝ :=
  realFaceDensity (PairedForestCommonRealDensity.edges (main_dimension n)
    (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) (mainEdges H))

theorem weightedDensity_eq (y : RealSpace T) (hy : y ∈ Face T) :
    PairedForestRealChartChangeVariables.weightedDensity (main_dimension n)
      (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T)
      (P.partition j) (mainEdges H) y = faceWeight P j T hT y * density (H := H) T hT y := by
  unfold PairedForestRealChartChangeVariables.weightedDensity
  rw [faceWeight, weight_eq P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) j y hy]
  unfold CompactDRAmbientPartition.cutoff CompactDRCoordinates.embedding
  rw [InteriorFaceDRCoordinates.ambient_eq_boundaryPoint (anchorMem T hT) (referenceMem T hT)
    (anchorGlobal T) (toProduct y)
    (openConditions_toAngular (anchorMem T hT) (referenceNe T hT) (toProduct y) hy.1.2 hy.2)]
  rfl

theorem signed_integral_nativePiece (c : Index P j T hT) :
    (P.orientation j * -((-1 : ℝ) ^
      (ForestRadialFaceClassification.axis (main_dimension n) j.val c.val.orbit).val)) *
      (∫ w in nativePiece P j T hT c,
        NativePairedFaceIntegration.nativeDensity (main_dimension n) j.val c.val.orbit
          (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) w) =
      -(∫ y in piece P j T hT c, faceWeight P j T hT y * density (H := H) T hT y) := by
  have hs : nativePiece P j T hT c ⊆
      (localChart (main_dimension n) j.val c.val.orbit c.val.paired c.val.point).source := by
    intro w hw
    exact (realChart_source (main_dimension n) c.val.toIndex) ▸ hw.1
  have he := PairedForestRealChartChangeVariables.signed_integral_realChart_image (main_dimension n)
    (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) c.val.toIndex
    (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)
    (P.support j) (P.orientation j) (P.orientation_jacobian j)
    (nativePiece P j T hT c) (measurableSet_nativePiece P j T hT c) hs
  dsimp only [FixedIndex.toIndex] at he
  have him := MainPairedFixedChartSources.image_nativePiece P j T hT c
  dsimp only [FixedIndex.toIndex] at him
  rw [he, him]
  congr 1
  apply setIntegral_congr_fun (measurableSet_piece P j T hT c)
  intro y hy
  have hhalf : y ∈ FaceHalf T := hy.1.1.1
  exact weightedDensity_eq P j T hT y
    ⟨⟨⟨hhalf.1.1.1,hhalf.1.1.2.le⟩,hhalf.1.2⟩,hhalf.2⟩

theorem integrable_weighted :
    IntegrableOn (fun y ↦ faceWeight P j T hT y * density (H := H) T hT y) (Face T) := by
  have hi := PairedForestCommonRealDensity.integrable_common (main_dimension n)
    (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T)
    (mainEdges H) (mainEdges_noLoops H)
  exact hi.bdd_mul (measurable_weight P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ by
      rw [faceWeight, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg P.partition
        (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) j y)]
      exact weight_le_one P.partition (anchorMem T hT) (referenceMem T hT)
        (referenceNe T hT) (anchorGlobal T) j y)

theorem all_index_orbit_eq (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired)
    (hlabels : S j.val o ho = T) (c : Index P j T hT) : c.val.orbit = o :=
  MainPairedSupportOrbit.paired_orbit_eq_of_mask j.val _ _ c.val.paired ho
    (c.val.labels.trans hlabels.symm)

/-- One fixed native orbit has the full weighted real-face integral: the
support-dependent countable chart cover has multiplicity exactly one. -/
theorem orbitValue_eq_neg_integral (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired)
    (hlabels : S j.val o ho = T) :
    MainClassifiedFaceAssembly.orbitValue P j o =
      -(∫ y in Face T, faceWeight P j T hT y * density (H := H) T hT y) := by
  have hn := hasSum_signed_nativePiece P j T hT o ho hlabels
  have he (c : OrbitIndex P j T hT o) :
      (P.orientation j * -((-1 : ℝ) ^ (ForestRadialFaceClassification.axis (main_dimension n) j.val o).val)) *
        (∫ w in nativePiece P j T hT c.val,
          NativePairedFaceIntegration.nativeDensity (main_dimension n) j.val o
            (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) w) =
      -(∫ y in piece P j T hT c.val, faceWeight P j T hT y * density (H := H) T hT y) := by
    simpa only [c.property] using signed_integral_nativePiece P j T hT c.val
  simp_rw [he] at hn
  let e : OrbitIndex P j T hT o ≃ Index P j T hT :=
    Equiv.subtypeUnivEquiv (all_index_orbit_eq P j T hT o ho hlabels)
  have hn'' : HasSum (fun c : Index P j T hT ↦
      -(∫ y in piece P j T hT c, faceWeight P j T hT y * density (H := H) T hT y))
      (MainClassifiedFaceAssembly.orbitValue P j o) := e.hasSum_iff.mp hn
  have hi := MainPairedFixedChartCover.hasSum_integral_piece P j T hT
    (fun y ↦ faceWeight P j T hT y * density (H := H) T hT y)
    ((integrable_weighted P j T hT).mono_set fun y hy ↦
      ⟨⟨⟨hy.1.1.1.1,hy.1.1.1.2.le⟩,hy.1.1.2⟩,hy.1.2⟩)
  rw [integral_weighted_eq_support]
  exact hn''.unique hi.neg

/-- Summing the paired orbits with this mask in one original chart accounts
for the whole weighted face, including charts whose weight vanishes there. -/
theorem sum_orbitValue_eq_neg_integral :
    (∑ o : ForestRadialFaceClassification.Orbit 0 j.val,
      if ho : ForestRadialFaceClassification.kind 0 j.val o = .paired then
        if S j.val o ho = T then MainClassifiedFaceAssembly.orbitValue P j o else 0
      else 0) =
      -(∫ y in Face T, faceWeight P j T hT y * density (H := H) T hT y) := by
  by_cases hex : ∃ (o : ForestRadialFaceClassification.Orbit 0 j.val)
      (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired), S j.val o ho = T
  · obtain ⟨o,ho,hlabels⟩ := hex
    rw [Finset.sum_eq_single o]
    · simpa only [dif_pos ho, if_pos hlabels] using orbitValue_eq_neg_integral P j T hT o ho hlabels
    · intro p _ hpo
      split_ifs with hp hSp
      · exact False.elim (hpo (MainPairedSupportOrbit.paired_orbit_eq_of_mask j.val p o hp ho
          (hSp.trans hlabels.symm)))
      · rfl
      · rfl
    · simp
  · have hw : ∀ y ∈ Face T, faceWeight P j T hT y = 0 := by
      intro y hy
      by_contra hne
      obtain ⟨c,hc⟩ := exists_target_of_weight_ne_zero P j T hT y hy hne
      exact hex ⟨c.orbit,c.paired,c.labels⟩
    have hz : (∫ y in Face T, faceWeight P j T hT y * density (H := H) T hT y) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      rw [hw y hy,zero_mul]
    rw [hz,neg_zero]
    apply Finset.sum_eq_zero
    intro o _
    split_ifs with ho hlabels
    · exact False.elim (hex ⟨o,ho,hlabels⟩)
    · rfl
    · rfl

end EnvelopingIsomorphism.Deformation.MainPairedFixedChartIntegral
