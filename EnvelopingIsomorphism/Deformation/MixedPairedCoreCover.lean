import EnvelopingIsomorphism.Deformation.MixedPairedCoreData
import EnvelopingIsomorphism.Deformation.MainPairedFixedChartCover

/-! A graph-independent fixed original-chart cover, including mixed arities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MixedPairedCoreCover
open Kontsevich Configuration InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalMarks
open SimpleProductPhaseIdentification SimpleFaceNativeAtlas Set MeasureTheory PairedForestAngleFundamentalDomain
open MixedPairedCoreData
open scoped Classical

variable {n m r : ℕ} {hdim : GraphForms.dimension n m = r+1}
  {es : Fin r → GraphForms.Edge n m} (P : PairedData hdim es) (j : P.charts)
  (T : Finset (Fin (n+1))) (hT : 1 < T.card)

include hT in
theorem anchorMem : canonicalAnchor T ∈ T := canonicalAnchor_mem T (Finset.card_pos.mp (by omega : 0<T.card))
include hT in
theorem referenceMem : canonicalReference T ∈ T := canonicalReference_mem T hT
include hT in
theorem referenceNe : canonicalReference T ≠ canonicalAnchor T := canonicalReference_ne T hT
theorem anchorGlobal : (0 : Fin (n+1)) ∈ T → canonicalAnchor T = 0 := fun h ↦ by simp [canonicalAnchor,h]

abbrev RealSpace := RealProductCoordinates (0 : Fin (n+1)) (canonicalAnchor T) (canonicalReference T) T m
abbrev Face := FaceRegion (0 : Fin (n+1)) (canonicalAnchor T) (canonicalReference T) T m

def faceWeight : RealSpace (m := m) T → ℝ :=
  weight P.partition (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) j

abbrev FaceHalf := FaceRegionIco (0 : Fin (n+1)) (canonicalAnchor T) (canonicalReference T) T m

def supportRegion : Set (RealSpace (m := m) T) := FaceHalf (m := m) T ∩ {y | faceWeight P j T hT y ≠ 0}

structure FixedIndex where
  orbit : ForestRadialFaceClassification.Orbit 0 j.val
  paired : ForestRadialFaceClassification.kind 0 j.val orbit = .paired
  point : Source hdim j.val orbit
  labels : S j.val orbit paired = T
  anchor_eq : anchor j.val orbit paired = canonicalAnchor T
  reference_eq : reference j.val orbit paired = canonicalReference T
  turn : ℤ

def FixedIndex.toIndex (c : FixedIndex P j T) : CanonicalIndex hdim T :=
  ⟨j.val,c.orbit,c.paired,c.point,c.labels,c.anchor_eq,c.reference_eq,c.turn⟩

theorem exists_target_of_weight_ne_zero (y : RealSpace (m := m) T) (hy : y ∈ Face (m := m) T)
    (hw : faceWeight P j T hT y ≠ 0) :
    ∃ c : FixedIndex P j T, y ∈ (realChart hdim c.toIndex).target := by
  have hp := openConditions_toAngular (anchorMem T hT) (referenceNe T hT) (toProduct y) hy.1.2 hy.2
  have hcut : CompactDRAmbientPartition.cutoff 0 (P.partition j)
      (InteriorFacePartitionReassembly.facePoint (anchorMem T hT) (referenceMem T hT)
        (referenceNe T hT) (anchorGlobal T) ⟨y,hy⟩) ≠ 0 := by
    rwa [faceWeight,weight_eq] at hw
  have hq := MixedPairedCoreData.mem_chart_of_cutoff_ne_zero P j _ hcut
  obtain ⟨c,hc,hpc⟩ := MainPairedFixedChartCover.exists_region_fixed hdim j.val hT (toProduct y) hp hq
  rcases c with ⟨center,o,ho,z,hS,ha,hb,k⟩
  dsimp only at hc
  subst center
  exact ⟨⟨o,ho,z,hS,ha,hb,k⟩, by rwa [realChart_target]⟩

theorem measurableSet_supportRegion : MeasurableSet (supportRegion P j T hT) :=
  measurableSet_faceRegionIco.inter ((measurable_weight P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) j) (MeasurableSet.compl (measurableSet_singleton (0 : ℝ))))

theorem exists_countable_fixed_cover : ∃ c : Set (FixedIndex P j T), c.Countable ∧
    supportRegion P j T hT ⊆ ⋃ z ∈ c, (realChart hdim z.toIndex).target := by
  apply (HereditarilyLindelofSpace.isLindelof (supportRegion P j T hT)).elim_countable_subcover
    (fun z : FixedIndex P j T ↦ (realChart hdim z.toIndex).target)
    (fun z ↦ (realChart hdim z.toIndex).open_target)
  intro y hy
  obtain ⟨z,hz⟩ := exists_target_of_weight_ne_zero P j T hT y
    ⟨⟨⟨hy.1.1.1.1,hy.1.1.1.2.le⟩,hy.1.1.2⟩,hy.1.2⟩ hy.2
  exact mem_iUnion.mpr ⟨z,hz⟩

def centers := (exists_countable_fixed_cover P j T hT).choose
instance : Countable (centers P j T hT) := (exists_countable_fixed_cover P j T hT).choose_spec.1.to_subtype
instance : Encodable (centers P j T hT) := Encodable.ofCountable _
abbrev Index := centers P j T hT

def piece (c : Index P j T hT) : Set (RealSpace (m := m) T) :=
  (supportRegion P j T hT ∩ (realChart hdim c.val.toIndex).target) \
    ⋃ d : Index P j T hT, ⋃ (_ : Encodable.encode d < Encodable.encode c),
      (realChart hdim d.val.toIndex).target

theorem piece_subset_target (c : Index P j T hT) :
    piece P j T hT c ⊆ (realChart hdim c.val.toIndex).target := fun _ h ↦ h.1.2

theorem measurableSet_piece (c : Index P j T hT) : MeasurableSet (piece P j T hT c) :=
  ((measurableSet_supportRegion P j T hT).inter (realChart hdim c.val.toIndex).open_target.measurableSet).diff
    (MeasurableSet.iUnion fun d ↦ MeasurableSet.iUnion fun _ ↦
      (realChart hdim d.val.toIndex).open_target.measurableSet)

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
    have hex : ∃ k : ℕ, ∃ c : Index P j T hT, Encodable.encode c = k ∧ y ∈ (realChart hdim c.val.toIndex).target := by
      obtain ⟨c,hc,hyc⟩ := mem_iUnion₂.mp ((exists_countable_fixed_cover P j T hT).choose_spec.2 hy)
      exact ⟨_,⟨c,hc⟩,rfl,hyc⟩
    obtain ⟨c,hc,hyc⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨c,⟨hy,hyc⟩,?_⟩
    intro h
    obtain ⟨d,hd,hyd⟩ := mem_iUnion₂.mp h
    exact Nat.find_min hex (hc ▸ hd) ⟨d,rfl,hyd⟩

/-- Exact integration over the supported portion uses only charts centered at
j.val. Off that portion the original weight is zero, proved below. -/
theorem hasSum_integral_piece (f : RealSpace (m := m) T → ℝ) (hf : IntegrableOn f (supportRegion P j T hT)) :
    HasSum (fun c : Index P j T hT ↦ ∫ y in piece P j T hT c, f y)
      (∫ y in supportRegion P j T hT, f y) := by
  have h := hasSum_integral_iUnion (measurableSet_piece P j T hT) (pairwiseDisjoint_piece P j T hT)
    (show IntegrableOn f (⋃ c : Index P j T hT, piece P j T hT c) from (iUnion_piece P j T hT).symm ▸ hf)
  simpa only [iUnion_piece] using h

/-- A weighted full-face integral is exactly its supported original-chart
integral. This is a proved support identity, not a geometric matching input. -/
theorem integral_weighted_eq_support (g : RealSpace (m := m) T → ℝ) :
    (∫ y in Face (m := m) T, faceWeight P j T hT y * g y) =
      ∫ y in supportRegion P j T hT, faceWeight P j T hT y * g y := by
  rw [← integral_faceRegionIco_eq]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_faceRegionIco inter_subset_left
  intro y hy
  have hw : faceWeight P j T hT y = 0 := by
    by_contra h
    exact hy.2 ⟨hy.1,h⟩
  rw [hw,zero_mul]

end EnvelopingIsomorphism.Deformation.MixedPairedCoreCover
