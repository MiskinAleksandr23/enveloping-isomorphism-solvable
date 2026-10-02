import EnvelopingIsomorphism.Deformation.MixedPairedCoreCover
import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceChartPoint
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDomainConverse

/-! Pulling the disjoint half-open target pieces back into the original
finite Stokes chart. The physical-point uniqueness proves no repeated count
inside a native radial orbit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MixedPairedCoreSources
open Kontsevich Configuration InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalMarks
open SimpleProductPhaseIdentification SimpleFaceNativeAtlas SimpleFaceChartPoint Set MeasureTheory
open MixedPairedCoreData PairedForestAngleFundamentalDomain
open MixedPairedCoreCover
open scoped Classical
variable {n m r : ℕ} {hdim : GraphForms.dimension n m = r+1}
  {es : Fin r → GraphForms.Edge n m} (P : PairedData hdim es) (j : P.charts)
  (T : Finset (Fin (n+1))) (hT : 1<T.card)

def nativePiece (c : Index P j T hT) : Set (BoxStokes.Coord r) :=
  (realChart hdim c.val.toIndex).source ∩
    (realChart hdim c.val.toIndex) ⁻¹' piece P j T hT c

theorem nativePiece_subset_source (c : Index P j T hT) :
    nativePiece P j T hT c ⊆ ForestRadialFaceLocalization.source hdim j.val c.val.orbit := by
  intro w hw
  exact localChart_source_subset hdim j.val c.val.orbit c.val.paired c.val.point
    ((realChart_source hdim c.val.toIndex) ▸ hw.1)

theorem measurableSet_nativePiece (c : Index P j T hT) : MeasurableSet (nativePiece P j T hT c) := by
  let e := realChart hdim c.val.toIndex
  let f := e.source.piecewise e (fun _ ↦ 0)
  have hf : Measurable f := e.continuousOn.measurable_piecewise continuous_const.continuousOn e.open_source.measurableSet
  have he : nativePiece P j T hT c = e.source ∩ f ⁻¹' piece P j T hT c := by
    ext w
    change (w ∈ e.source ∧ e w ∈ piece P j T hT c) ↔ (w ∈ e.source ∧ f w ∈ piece P j T hT c)
    by_cases hw : w ∈ e.source
    · simp only [hw,true_and]
      rw [show f w = e w from piecewise_eq_of_mem _ _ _ hw]
    · simp only [hw,false_and]
  rw [he]
  exact e.open_source.measurableSet.inter ((measurableSet_piece P j T hT c).preimage hf)

theorem image_nativePiece (c : Index P j T hT) :
    realChart hdim c.val.toIndex '' nativePiece P j T hT c = piece P j T hT c := by
  apply subset_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact hw.2
  · intro y hy
    let e := realChart hdim c.val.toIndex
    have ht := piece_subset_target P j T hT c hy
    refine ⟨e.symm y,⟨e.map_target ht,?_⟩,e.right_inv ht⟩
    change e (e.symm y) ∈ piece P j T hT c
    rwa [e.right_inv ht]

/-- Different target pieces cannot count the same native parameter in one
orbit: physical equality and the half-open angular convention force their
real product points to agree. -/
theorem disjoint_nativePiece_of_orbit_eq (c d : Index P j T hT) (hcd : c ≠ d)
    (horbit : c.val.orbit = d.val.orbit) : Disjoint (nativePiece P j T hT c) (nativePiece P j T hT d) := by
  apply disjoint_left.mpr
  intro w hwc hwd
  let pc := realChart hdim c.val.toIndex w
  let pd := realChart hdim d.val.toIndex w
  have hcF : pc ∈ FaceHalf (m := m) T := hwc.2.1.1.1
  have hdF : pd ∈ FaceHalf (m := m) T := hwd.2.1.1.1
  have hc := realChart_boundaryPoint hdim c.val.toIndex
    (anchorMem T hT) (referenceMem T hT) (anchorGlobal T) hwc.1
  have hd := realChart_boundaryPoint hdim d.val.toIndex
    (anchorMem T hT) (referenceMem T hT) (anchorGlobal T) hwd.1
  have hp : PairedForestSimpleOverlap.facePoint hdim j.val c.val.orbit
      ⟨w,nativePiece_subset_source P j T hT c hwc⟩ =
      PairedForestSimpleOverlap.facePoint hdim j.val d.val.orbit
      ⟨w,nativePiece_subset_source P j T hT d hwd⟩ := by
    change ForestOrthantCharts.chart 0 j.val (ForestPositiveChartSmooth.ofAmbient 0 j.val
      (ForestRadialFaceClassification.faceAmbient hdim j.val c.val.orbit w)) =
      ForestOrthantCharts.chart 0 j.val (ForestPositiveChartSmooth.ofAmbient 0 j.val
      (ForestRadialFaceClassification.faceAmbient hdim j.val d.val.orbit w))
    rw [horbit]
  have he := eq_of_boundaryPoint_eq_of_angle_mem (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) (InteriorGraphFaceCoordinates.toProduct pc)
    (InteriorGraphFaceCoordinates.toProduct pd)
    (realChart_openConditions hdim c.val.toIndex hwc.1)
    (realChart_openConditions hdim d.val.toIndex hwd.1)
    hcF.1.1 hdF.1.1 (hc.trans (hp.trans hd.symm))
  have hpc : pc = pd := InteriorGraphFaceCoordinates.toProduct.injective he
  have hwd' : pc ∈ piece P j T hT d := by rw [hpc]; exact hwd.2
  exact disjoint_left.mp (pairwiseDisjoint_piece P j T hT hcd) hwc.2 hwd'

/-- Every supported native source point has an exact representative in the
half-open full face. -/
theorem exists_half_point_of_source
    (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired)
    (hlabels : S j.val o ho = T)
    (z : ForestRadialFaceLocalization.source hdim j.val o)
    (hcut : CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (PairedForestSimpleOverlap.facePoint hdim j.val o z) ≠ 0) :
    ∃ y : Face (m := m) T, y.val ∈ supportRegion P j T hT ∧
      InteriorFacePartitionReassembly.facePoint (anchorMem T hT) (referenceMem T hT)
        (referenceNe T hT) (anchorGlobal T) y =
        PairedForestSimpleOverlap.facePoint hdim j.val o z := by
  let c₀ : FixedIndex P j T := ⟨o,ho,z,hlabels,
    (anchor_eq_canonical _ _ _).trans (congrArg canonicalAnchor hlabels),
    (reference_eq_canonical _ _ _).trans (congrArg canonicalReference hlabels),0⟩
  let p := nativeEquiv hdim c₀.toIndex
    (localChart hdim j.val o ho z z.val)
  obtain ⟨k,hk,_⟩ := existsUnique_int_lift p
  let c : FixedIndex P j T := {c₀ with turn := k}
  let y := realChart hdim c.toIndex z.val
  have hz : z.val ∈ (realChart hdim c.toIndex).source := by
    rw [realChart_source]
    exact self_mem_localChart_source hdim j.val o ho z
  have hop := realChart_openConditions hdim c.toIndex hz
  have hsc := shape_coarse_of_openConditions_toAngular (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) (InteriorGraphFaceCoordinates.toProduct y) hop
  have hθ : y.1.1 ∈ Ico 0 (2 * Real.pi) := by
    change (InteriorGraphFaceCoordinates.toProduct y).1.1 ∈ Ico 0 (2 * Real.pi)
    rw [realChart_toProduct]
    exact hk
  have hy : y ∈ FaceHalf (m := m) T := ⟨⟨hθ,hsc.1⟩,hsc.2⟩
  have hyc : y ∈ Face (m := m) T := ⟨⟨⟨hθ.1,hθ.2.le⟩,hsc.1⟩,hsc.2⟩
  have he := realChart_point_eq hdim c.toIndex (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) hz ⟨y,hyc⟩ rfl
  refine ⟨⟨y,hyc⟩,⟨hy,?_⟩,he.symm⟩
  change faceWeight P j T hT y ≠ 0
  rw [faceWeight,weight_eq]
  · rwa [← he]
  · exact hyc

/-- The pulled-back target pieces cover every supported original source.
Orbit and parameter uniqueness are supplied by the native decoder. -/
theorem exists_nativePiece_of_supported_source
    (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired)
    (hlabels : S j.val o ho = T)
    (z : ForestRadialFaceLocalization.source hdim j.val o)
    (hcut : CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (PairedForestSimpleOverlap.facePoint hdim j.val o z) ≠ 0) :
    ∃ c : Index P j T hT, c.val.orbit = o ∧ z.val ∈ nativePiece P j T hT c := by
  obtain ⟨y,hy,hpoint⟩ := exists_half_point_of_source P j T hT o ho hlabels z hcut
  have hU : y.val ∈ ⋃ c : Index P j T hT, piece P j T hT c := by rwa [MixedPairedCoreCover.iUnion_piece]
  obtain ⟨c,hc⟩ := mem_iUnion.mp hU
  let e := realChart hdim c.val.toIndex
  have ht := piece_subset_target P j T hT c hc
  have hw := e.map_target ht
  let w : ForestRadialFaceLocalization.source hdim j.val c.val.orbit :=
    ⟨e.symm y.val,localChart_source_subset hdim j.val c.val.orbit c.val.paired c.val.point
      ((realChart_source hdim c.val.toIndex) ▸ hw)⟩
  have he : PairedForestSimpleOverlap.facePoint hdim j.val c.val.orbit w =
      PairedForestSimpleOverlap.facePoint hdim j.val o z :=
    (realChart_point_eq hdim c.val.toIndex (anchorMem T hT) (referenceMem T hT)
      (referenceNe T hT) (anchorGlobal T) hw y (e.right_inv ht)).trans hpoint
  have ho' : c.val.orbit = o := MainPairedChartTransfer.source_orbit_unique
    hdim j.val _ c.val.orbit o w z he rfl
  have hwz : w.val = z.val := by
    have hA := (MainPairedChartTransfer.decodedAmbient_eq_faceAmbient
      hdim j.val _ c.val.orbit w he).symm.trans
      (MainPairedChartTransfer.decodedAmbient_eq_faceAmbient hdim j.val _ o z rfl)
    change ForestRadialFaceClassification.faceAmbient hdim j.val c.val.orbit (e.symm y.val) =
      ForestRadialFaceClassification.faceAmbient hdim j.val o z.val at hA
    rw [ho'] at hA
    exact ForestRadialFaceReconstruction.faceAmbient_injective hdim j.val o hA
  refine ⟨c,ho',?_⟩
  have hwPiece : w.val ∈ nativePiece P j T hT c := ⟨hw,by change e (e.symm y.val) ∈ piece P j T hT c; rwa [e.right_inv ht]⟩
  rwa [hwz] at hwPiece

abbrev OrbitIndex (o : ForestRadialFaceClassification.Orbit 0 j.val) :=
  {c : Index P j T hT // c.val.orbit = o}

theorem nativePieces_subset_source (o : ForestRadialFaceClassification.Orbit 0 j.val) :
    (⋃ c : OrbitIndex P j T hT o, nativePiece P j T hT c.val) ⊆
      ForestRadialFaceLocalization.source hdim j.val o := by
  apply iUnion_subset
  intro c w hw
  have h := nativePiece_subset_source P j T hT c.val hw
  simpa only [c.property] using h

/-- Outside the native pieces the actual local graph density vanishes, because
any nonzero original cutoff supplies a covered source parameter. -/
theorem nativeDensity_zero_off_pieces
    (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired) (hlabels : S j.val o ho = T)
    (w : BoxStokes.Coord r)
    (hw : w ∈ ForestRadialFaceLocalization.source hdim j.val o)
    (hnot : w ∉ ⋃ c : OrbitIndex P j T hT o, nativePiece P j T hT c.val) :
    NativePairedFaceIntegration.nativeDensity hdim j.val o
      (P.partition j) es P.noLoops (P.localizer j) w = 0 := by
  have hc : CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (PairedForestSimpleOverlap.facePoint hdim j.val o ⟨w,hw⟩) = 0 := by
    by_contra hne
    obtain ⟨c,hco,hwc⟩ := exists_nativePiece_of_supported_source P j T hT o ho hlabels ⟨w,hw⟩ hne
    exact hnot (mem_iUnion.mpr ⟨⟨c,hco⟩,hwc⟩)
  unfold NativePairedFaceIntegration.nativeDensity
  rw [ForestFaceCutoffIntegrability.local_density_eq hdim j.val o
    (P.partition j) es P.noLoops (P.localizer j) (P.localization j) w hw]
  rw [ForestFaceCutoffIntegrability.cutoff, ChartCutoffSupport.zeroPullback_source _ _ hw.2]
  change CompactDRAmbientPartition.cutoff 0 (P.partition j)
    (PairedForestSimpleOverlap.facePoint hdim j.val o ⟨w,hw⟩) * _ = 0
  rw [hc,zero_mul]

/-- Exact original-orbit integral reassembly over the newly constructed
half-open target cover, now pulled back into the specified original chart.
Coverage, multiplicity and summability are all proved. -/
theorem hasSum_nativePiece
    (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired) (hlabels : S j.val o ho = T) :
    HasSum (fun c : OrbitIndex P j T hT o ↦ ∫ w in nativePiece P j T hT c.val,
      NativePairedFaceIntegration.nativeDensity hdim j.val o
        (P.partition j) es P.noLoops (P.localizer j) w)
      (∫ w in ForestRadialFaceLocalization.source hdim j.val o,
        NativePairedFaceIntegration.nativeDensity hdim j.val o
          (P.partition j) es P.noLoops (P.localizer j) w) := by
  have hdis : Pairwise (fun c d : OrbitIndex P j T hT o ↦
      Disjoint (nativePiece P j T hT c.val) (nativePiece P j T hT d.val)) := by
    intro c d hcd
    exact disjoint_nativePiece_of_orbit_eq P j T hT c.val d.val
      (fun h ↦ hcd (Subtype.ext h)) (c.property.trans d.property.symm)
  have hi := NativePairedFaceIntegration.integrableOn_nativeDensity hdim j.val o
    (P.partition j) es P.noLoops (P.localizer j) (P.regular j).1 (P.regular j).2
  have he : (∫ w in ForestRadialFaceLocalization.source hdim j.val o,
      NativePairedFaceIntegration.nativeDensity hdim j.val o
        (P.partition j) es P.noLoops (P.localizer j) w) =
      ∫ w in ⋃ c : OrbitIndex P j T hT o, nativePiece P j T hT c.val,
        NativePairedFaceIntegration.nativeDensity hdim j.val o
          (P.partition j) es P.noLoops (P.localizer j) w :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (ForestRadialFaceLocalization.measurableSet_source hdim j.val o)
      (nativePieces_subset_source P j T hT o)
      (fun w hw ↦ nativeDensity_zero_off_pieces P j T hT o ho hlabels w hw.1 hw.2)
  rw [he]
  exact hasSum_integral_iUnion (fun c ↦ measurableSet_nativePiece P j T hT c.val) hdis
    (hi.mono_set (nativePieces_subset_source P j T hT o))

/-- The signed sum is precisely the contribution in the original classified
Stokes relation, retaining its original chart orientation and lower-face sign. -/
theorem hasSum_signed_nativePiece
    (o : ForestRadialFaceClassification.Orbit 0 j.val)
    (ho : ForestRadialFaceClassification.kind 0 j.val o = .paired) (hlabels : S j.val o ho = T) :
    HasSum (fun c : OrbitIndex P j T hT o ↦
      (P.orientation j * -((-1 : ℝ) ^ (ForestRadialFaceClassification.axis hdim j.val o).val)) *
        ∫ w in nativePiece P j T hT c.val,
          NativePairedFaceIntegration.nativeDensity hdim j.val o
            (P.partition j) es P.noLoops (P.localizer j) w)
      (PairedData.orbitValue P j o) := by
  have h := (hasSum_nativePiece P j T hT o ho hlabels).mul_left
    (P.orientation j * -((-1 : ℝ) ^ (ForestRadialFaceClassification.axis hdim j.val o).val))
  rw [PairedData.orbitValue,
    ForestRadialFaceLocalization.contribution_eq_integral_source hdim j.val o
      (P.partition j) es P.noLoops (P.localizer j) (P.localization j)]
  simpa only [NativePairedFaceIntegration.nativeDensity,smul_eq_mul,mul_assoc] using h

end EnvelopingIsomorphism.Deformation.MixedPairedCoreSources
