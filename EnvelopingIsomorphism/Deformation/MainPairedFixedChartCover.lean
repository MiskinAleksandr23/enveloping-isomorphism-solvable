import EnvelopingIsomorphism.Deformation.MainSimplePairedChartTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestRealGraphDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFacePartitionReassembly
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestAngleFundamentalDomain

/-! A full weighted simple-face cover using only a specified original Stokes
chart. The arbitrary-center transfer theorem supplies the native sources;
there is no coverage hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainPairedFixedChartCover
open Kontsevich Configuration InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalMarks
open SimpleProductPhaseIdentification SimpleFaceNativeAtlas Set MeasureTheory
open MainScalarBoundaryAssembly UniformBinaryGraphs PairedForestAngleFundamentalDomain
open scoped Classical

section General
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m)
  {T : Finset (Fin (n+1))} (hT : 1 < T.card)

/-- Every simple point in THIS original chart has a translated native product
chart with this same center, its prescribed mask and its original labels. -/
theorem exists_region_fixed
    (p : ProductCoordinates 0 (canonicalAnchor T) (canonicalReference T) T m)
    (hp : (toAngular p).toFree.OpenConditions)
    (hq : (InteriorFaceDRCoordinates.datum
      (canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0 < T.card)))
      (canonicalReference_mem T hT)
      (show (0 : Fin (n+1)) ∈ T → canonicalAnchor T = 0 from fun h ↦ by simp [canonicalAnchor,h])
      p hp).toInteriorCollisionData.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ c : CanonicalIndex hdim T, c.center = x ∧ p ∈ region hdim c := by
  have ha := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0 < T.card))
  have hb := canonicalReference_mem T hT
  have hg : (0 : Fin (n+1)) ∈ T → canonicalAnchor T = 0 := fun h ↦ by simp [canonicalAnchor,h]
  let D := InteriorFaceDRCoordinates.datum ha hb hg p hp
  obtain ⟨o,ho,z,hS,hz⟩ := MainSimplePairedChartTransfer.hasPairedSource_of_mem_target x D hdim hT hq
  let c₀ : CanonicalIndex hdim T :=
    ⟨x,o,ho,z,hS,(anchor_eq_canonical _ _ _).trans (congrArg canonicalAnchor hS),
      (reference_eq_canonical _ _ _).trans (congrArg canonicalReference hS),0⟩
  let q := (nativeEquiv hdim c₀).symm p
  have hq' : (toAngular q).toFree.OpenConditions := by
    apply (nativeEquiv_openConditions hdim c₀ q).mp
    simpa only [q,ContinuousLinearEquiv.apply_symm_apply] using hp
  have he := nativeEquiv_boundaryPoint hdim c₀ ha hb hg q hq'
  simp only [q,ContinuousLinearEquiv.apply_symm_apply] at he
  have hn : (InteriorFaceDRCoordinates.datum (anchor_mem c₀.center c₀.orbit c₀.paired)
      (reference_mem c₀.center c₀.orbit c₀.paired) (anchor_global c₀.center c₀.orbit c₀.paired) q hq').toInteriorCollisionData.boundaryPoint =
      PairedForestSimpleOverlap.facePoint hdim c₀.center c₀.orbit c₀.point := he.symm.trans hz.symm
  obtain ⟨k,y,hy,heq⟩ := mem_shift_localChart_target hdim c₀.center c₀.orbit c₀.paired q hq' c₀.point hn
  let c : CanonicalIndex hdim T := {c₀ with turn := k}
  refine ⟨c,rfl,y,hy,?_⟩
  change shift k (nativeEquiv hdim c y) = p
  rw [← nativeEquiv_shift hdim c k y,heq]
  exact (nativeEquiv hdim c₀).apply_symm_apply p
end General

variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H) (j : P.charts)
  (T : Finset (Fin (n+2))) (hT : 1 < T.card)

include hT in
theorem anchorMem : canonicalAnchor T ∈ T := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0<T.card))
include hT in
theorem referenceMem : canonicalReference T ∈ T := canonicalReference_mem T hT
include hT in
theorem referenceNe : canonicalReference T ≠ canonicalAnchor T := canonicalReference_ne T hT
theorem anchorGlobal : (0 : Fin (n+2)) ∈ T → canonicalAnchor T = 0 := fun h ↦ by simp [canonicalAnchor,h]

abbrev RealSpace := RealProductCoordinates (0 : Fin (n+2)) (canonicalAnchor T) (canonicalReference T) T 3
abbrev Face := FaceRegion (0 : Fin (n+2)) (canonicalAnchor T) (canonicalReference T) T 3

def faceWeight : RealSpace T → ℝ :=
  weight P.partition (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) j

abbrev FaceHalf := FaceRegionIco (0 : Fin (n+2)) (canonicalAnchor T) (canonicalReference T) T 3

def supportRegion : Set (RealSpace T) := FaceHalf T ∩ {y | faceWeight P j T hT y ≠ 0}

structure FixedIndex where
  orbit : ForestRadialFaceClassification.Orbit 0 j.val
  paired : ForestRadialFaceClassification.kind 0 j.val orbit = .paired
  point : Source (main_dimension n) j.val orbit
  labels : S j.val orbit paired = T
  anchor_eq : anchor j.val orbit paired = canonicalAnchor T
  reference_eq : reference j.val orbit paired = canonicalReference T
  turn : ℤ

def FixedIndex.toIndex (c : FixedIndex P j T) : CanonicalIndex (main_dimension n) T :=
  ⟨j.val,c.orbit,c.paired,c.point,c.labels,c.anchor_eq,c.reference_eq,c.turn⟩

theorem exists_target_of_weight_ne_zero (y : RealSpace T) (hy : y ∈ Face T)
    (hw : faceWeight P j T hT y ≠ 0) :
    ∃ c : FixedIndex P j T, y ∈ (realChart (main_dimension n) c.toIndex).target := by
  have hp := openConditions_toAngular (anchorMem T hT) (referenceNe T hT) (toProduct y) hy.1.2 hy.2
  have hcut : CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (InteriorFacePartitionReassembly.facePoint (anchorMem T hT) (referenceMem T hT)
        (referenceNe T hT) (anchorGlobal T) ⟨y,hy⟩) ≠ 0 := by
    rwa [faceWeight,weight_eq] at hw
  have hq := MainPairedChartTransfer.mem_chart_of_cutoff_ne_zero P j _ hcut
  obtain ⟨c,hc,hpc⟩ := exists_region_fixed (main_dimension n) j.val hT (toProduct y) hp hq
  rcases c with ⟨center,o,ho,z,hS,ha,hb,k⟩
  dsimp only at hc
  subst center
  exact ⟨⟨o,ho,z,hS,ha,hb,k⟩, by rwa [realChart_target]⟩

theorem measurableSet_supportRegion : MeasurableSet (supportRegion P j T hT) :=
  measurableSet_faceRegionIco.inter ((measurable_weight P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) j) (MeasurableSet.compl (measurableSet_singleton (0 : ℝ))))

theorem exists_countable_fixed_cover : ∃ c : Set (FixedIndex P j T), c.Countable ∧
    supportRegion P j T hT ⊆ ⋃ z ∈ c, (realChart (main_dimension n) z.toIndex).target := by
  apply (HereditarilyLindelofSpace.isLindelof (supportRegion P j T hT)).elim_countable_subcover
    (fun z : FixedIndex P j T ↦ (realChart (main_dimension n) z.toIndex).target)
    (fun z ↦ (realChart (main_dimension n) z.toIndex).open_target)
  intro y hy
  obtain ⟨z,hz⟩ := exists_target_of_weight_ne_zero P j T hT y
    ⟨⟨⟨hy.1.1.1.1,hy.1.1.1.2.le⟩,hy.1.1.2⟩,hy.1.2⟩ hy.2
  exact mem_iUnion.mpr ⟨z,hz⟩

def centers := (exists_countable_fixed_cover P j T hT).choose
instance : Countable (centers P j T hT) := (exists_countable_fixed_cover P j T hT).choose_spec.1.to_subtype
instance : Encodable (centers P j T hT) := Encodable.ofCountable _
abbrev Index := centers P j T hT

def piece (c : Index P j T hT) : Set (RealSpace T) :=
  (supportRegion P j T hT ∩ (realChart (main_dimension n) c.val.toIndex).target) \
    ⋃ d : Index P j T hT, ⋃ (_ : Encodable.encode d < Encodable.encode c),
      (realChart (main_dimension n) d.val.toIndex).target

theorem piece_subset_target (c : Index P j T hT) :
    piece P j T hT c ⊆ (realChart (main_dimension n) c.val.toIndex).target := fun _ h ↦ h.1.2

theorem measurableSet_piece (c : Index P j T hT) : MeasurableSet (piece P j T hT c) :=
  ((measurableSet_supportRegion P j T hT).inter (realChart (main_dimension n) c.val.toIndex).open_target.measurableSet).diff
    (MeasurableSet.iUnion fun d ↦ MeasurableSet.iUnion fun _ ↦
      (realChart (main_dimension n) d.val.toIndex).open_target.measurableSet)

theorem pairwiseDisjoint_piece : Pairwise (fun c d : Index P j T hT ↦ Disjoint (piece P j T hT c) (piece P j T hT d)) := by
  intro c d hcd
  apply disjoint_left.mpr
  intro y hyc hyd
  have hc : Encodable.encode c ≠ Encodable.encode d := fun h ↦ hcd (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · exact hyd.2 (mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hlt,hyc.1.2⟩⟩)
  · exact hyc.2 (mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hgt,hyd.1.2⟩⟩)

theorem iUnion_piece : (⋃ c : Index P j T hT, piece P j T hT c) = supportRegion P j T hT := by
  apply subset_antisymm
  · exact iUnion_subset fun _ _ h ↦ h.1.1
  · intro y hy
    have hex : ∃ k : ℕ, ∃ c : Index P j T hT, Encodable.encode c = k ∧ y ∈ (realChart (main_dimension n) c.val.toIndex).target := by
      obtain ⟨c,hc,hyc⟩ := mem_iUnion₂.mp ((exists_countable_fixed_cover P j T hT).choose_spec.2 hy)
      exact ⟨_,⟨c,hc⟩,rfl,hyc⟩
    obtain ⟨c,hc,hyc⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨c,⟨hy,hyc⟩,?_⟩
    intro h
    obtain ⟨d,hd,hyd⟩ := mem_iUnion₂.mp h
    exact Nat.find_min hex (hc ▸ hd) ⟨d,rfl,hyd⟩

/-- Exact integration over the supported portion uses only charts centered at
j.val. Off that portion the original weight is zero, proved below. -/
theorem hasSum_integral_piece (f : RealSpace T → ℝ) (hf : IntegrableOn f (supportRegion P j T hT)) :
    HasSum (fun c : Index P j T hT ↦ ∫ y in piece P j T hT c, f y)
      (∫ y in supportRegion P j T hT, f y) := by
  have h := hasSum_integral_iUnion (measurableSet_piece P j T hT) (pairwiseDisjoint_piece P j T hT)
    (show IntegrableOn f (⋃ c : Index P j T hT, piece P j T hT c) from (iUnion_piece P j T hT).symm ▸ hf)
  simpa only [iUnion_piece] using h

/-- A weighted full-face integral is exactly its supported original-chart
integral. This is a proved support identity, not a geometric matching input. -/
theorem integral_weighted_eq_support (g : RealSpace T → ℝ) :
    (∫ y in Face T, faceWeight P j T hT y * g y) =
      ∫ y in supportRegion P j T hT, faceWeight P j T hT y * g y := by
  rw [← integral_faceRegionIco_eq]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_faceRegionIco inter_subset_left
  intro y hy
  have hw : faceWeight P j T hT y = 0 := by
    by_contra h
    exact hy.2 ⟨hy.1,h⟩
  rw [hw,zero_mul]

end EnvelopingIsomorphism.Deformation.MainPairedFixedChartCover
