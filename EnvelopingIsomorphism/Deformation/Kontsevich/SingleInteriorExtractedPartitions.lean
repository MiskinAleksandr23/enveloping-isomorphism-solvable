import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestThreePartitionCriterion
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedShapeRatios

/-! Actual extracted partitions inside a simple interior collision have no
large subparts. The proof uses the explicit nonzero velocity ratios retained
by the original compactification point, independently of the chosen sequence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions

open Configuration ExtractedForestParameters Filter Topology
open PairedForestReverseCoverageCriterion PairedForestThreePartitionCriterion
open SubsetNormalizedLimits (LargeSubset)
open scoped Classical

variable {n m : ℕ} {i : Fin n}

theorem boundaryPoint_ratio_pos_of_pairBases_zero (D : InteriorCollisionData i m)
    (t : DoubledTriple n m)
    (hp : D.pairBase ⟨(t.val.1, t.val.2.1), t.property.1⟩ = 0)
    (hq : D.pairBase ⟨(t.val.1, t.val.2.2), t.property.2⟩ = 0) :
    0 < (D.boundaryPoint.val.2.2 t : ℝ) := by
  change 0 < ((D.resolvedCoordinates 0).2.2 t : ℝ)
  simp only [InteriorCollisionData.resolvedCoordinates, hp, hq, and_self, if_true]
  apply div_pos
  · exact norm_pos_iff.mpr (D.pairVelocity_ne_zero_of_pairBase_eq_zero _ hp)
  · exact add_pos_of_pos_of_nonneg
      (norm_pos_iff.mpr (D.pairVelocity_ne_zero_of_pairBase_eq_zero _ hp)) (norm_nonneg _)

theorem boundaryPoint_ratio_pos_of_pairBase_ne_zero (D : InteriorCollisionData i m)
    (t : DoubledTriple n m)
    (hp : D.pairBase ⟨(t.val.1, t.val.2.1), t.property.1⟩ ≠ 0) :
    0 < (D.boundaryPoint.val.2.2 t : ℝ) := by
  change 0 < ((D.resolvedCoordinates 0).2.2 t : ℝ)
  simp only [InteriorCollisionData.resolvedCoordinates, hp, false_and, if_false,
    InteriorCollisionData.activeDifference, Complex.ofReal_zero, zero_mul, add_zero]
  exact div_pos (norm_pos_iff.mpr hp)
    (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hp) (norm_nonneg _))

theorem boundaryPoint_ratio_eq_zero_of_mixed (D : InteriorCollisionData i m)
    (t : DoubledTriple n m)
    (hp : D.pairBase ⟨(t.val.1, t.val.2.1), t.property.1⟩ = 0)
    (hq : D.pairBase ⟨(t.val.1, t.val.2.2), t.property.2⟩ ≠ 0) :
    (D.boundaryPoint.val.2.2 t : ℝ) = 0 := by
  change ((D.resolvedCoordinates 0).2.2 t : ℝ) = 0
  simp [InteriorCollisionData.resolvedCoordinates, hp, hq,
    InteriorCollisionData.activeDifference, normalizedNormRatio]

/-- On a subset whose base is nonconstant, the extracted shape has precisely
the base's equality relation. Stored zero/nonzero triple ratios force both
directions, so the arbitrary approximating sequence introduces no extra block. -/
theorem shapes_eq_iff_base (D : InteriorCollisionData i m)
    (A : LargeSubset (DoubledLabel n m))
    (hbase : ∃ u v : A.val, D.doubledBase u.val ≠ D.doubledBase v.val)
    (a b : A.val) :
    (extraction i D.boundaryPoint).shapes A a = (extraction i D.boundaryPoint).shapes A b ↔
      D.doubledBase a.val = D.doubledBase b.val := by
  let q := (extraction i D.boundaryPoint).shapes A
  by_cases hab : a.val = b.val
  · have he : a = b := Subtype.ext hab
    simp [he]
  constructor
  · intro he
    by_contra hb
    have hbasep : D.pairBase ⟨(a.val, b.val), hab⟩ ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    obtain ⟨u, v, huv⟩ := (extraction i D.boundaryPoint).shapes_nonconstant A
    have hc : ∃ c : A.val, q c ≠ q a := by
      by_cases hu : q u = q a
      · exact ⟨v, fun hv => huv (hu.trans hv.symm)⟩
      · exact ⟨u, hu⟩
    obtain ⟨c, hc⟩ := hc
    have hac : a.val ≠ c.val := fun h => hc (congrArg q (Subtype.ext h.symm))
    have hr := ExtractedShapeRatios.ratio_eq i D.boundaryPoint A a b c hab hac
      (fun h => hc h.2)
    have hp := boundaryPoint_ratio_pos_of_pairBase_ne_zero D
      ⟨(a.val, b.val, c.val), hab, hac⟩ hbasep
    rw [hr] at hp
    simp [normalizedNormRatio, he] at hp
  · intro he
    by_contra hb
    obtain ⟨u, v, huv⟩ := hbase
    have hc : ∃ c : A.val, D.doubledBase c.val ≠ D.doubledBase a.val := by
      by_cases hu : D.doubledBase u.val = D.doubledBase a.val
      · exact ⟨v, fun hv => huv (hu.trans hv.symm)⟩
      · exact ⟨u, hu⟩
    obtain ⟨c, hc⟩ := hc
    have hac : a.val ≠ c.val := fun h => hc (congrArg D.doubledBase h.symm)
    have hr := ExtractedShapeRatios.ratio_eq i D.boundaryPoint A a b c hab hac
      (fun h => hb h.1.symm)
    have hz := boundaryPoint_ratio_eq_zero_of_mixed D
      ⟨(a.val, b.val, c.val), hab, hac⟩ (sub_eq_zero.mpr he.symm) (sub_ne_zero.mpr hc)
    rw [hr] at hz
    have hp : 0 < (normalizedNormRatio (q b - q a) (q c - q a) : ℝ) :=
      div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hb)))
        (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hb))) (norm_nonneg _))
    exact hp.ne' hz

/-- No extra large child can lie inside any constant-base subset of a simple
first-order collision: every pair of distinct velocities is resolved. -/
theorem part_card_le_one_of_constant_base (D : InteriorCollisionData i m)
    (A : LargeSubset (DoubledLabel n m))
    (hbase : ∀ a b : A.val, D.doubledBase a.val = D.doubledBase b.val)
    (B : Finset (DoubledLabel n m))
    (hB : B ∈ ((extraction i D.boundaryPoint).partitions A.val).parts) : B.card ≤ 1 := by
  apply ExtractedShapeRatios.part_card_le_one_of_shapes_injective i D.boundaryPoint A _ B hB
  apply ExtractedShapeRatios.shapes_injective_of_ratios_pos
  intro a b c hab hac
  apply boundaryPoint_ratio_pos_of_pairBases_zero
  · exact sub_eq_zero.mpr (hbase b a)
  · exact sub_eq_zero.mpr (hbase c a)

/-- The actual root partition is the equality partition of the finite doubled
base. This identification is independent of every subsequence choice. -/
theorem mem_root_part_iff (D : InteriorCollisionData i m) (a b : DoubledLabel n m) :
    b ∈ ((extraction i D.boundaryPoint).partitions Finset.univ).part a ↔
      D.doubledBase a = D.doubledBase b := by
  let A : LargeSubset (DoubledLabel n m) := ⟨Finset.univ, root_large i D.boundaryPoint⟩
  have hbase : ∃ u v : A.val, D.doubledBase u.val ≠ D.doubledBase v.val := by
    refine ⟨⟨Sum.inl (Sum.inl i), Finset.mem_univ _⟩, ⟨Sum.inr i, Finset.mem_univ _⟩, ?_⟩
    intro h
    have hi := congrArg Complex.im h
    change (D.base i).im = -(D.base i).im at hi
    linarith [(D.base i).im_pos]
  change b ∈ (SubsetNormalizedLimits.partition (extraction i D.boundaryPoint).shapes Finset.univ).part a ↔ _
  have hR : 1 < (Finset.univ : Finset (DoubledLabel n m)).card := root_large i D.boundaryPoint
  rw [SubsetNormalizedLimits.partition, dif_pos hR,
    Finpartition.mem_part_ofSetSetoid_iff_rel]
  simp only [Finset.mem_univ, true_and]
  change SubsetNormalizedLimits.extendedShape (extraction i D.boundaryPoint).shapes A a =
    SubsetNormalizedLimits.extendedShape (extraction i D.boundaryPoint).shapes A b ↔ _
  have ha : a ∈ A.val := Finset.mem_univ _
  have hb : b ∈ A.val := Finset.mem_univ _
  simp only [SubsetNormalizedLimits.extendedShape, dif_pos ha, dif_pos hb]
  exact shapes_eq_iff_base D A hbase ⟨a, Finset.mem_univ _⟩ ⟨b, Finset.mem_univ _⟩

variable {N : ℕ} {S : Finset (Fin (N + 1))}
  (D : SingleInteriorCluster (0 : Fin (N + 1)) m S)

theorem clusterPairCollapses_iff_masks (p : DoubledPair (N + 1) m) :
    clusterPairCollapses S p ↔
      (p.val.1 ∈ upperMask S ∧ p.val.2 ∈ upperMask S) ∨
      (p.val.1 ∈ lowerMask S ∧ p.val.2 ∈ lowerMask S) := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp [clusterPairCollapses, upperMask, lowerMask, Finset.image_image,
      doubledReflection, Function.comp_def]

theorem base_eq_iff_masks (a b : DoubledLabel (N + 1) m) :
    D.toInteriorCollisionData.doubledBase a = D.toInteriorCollisionData.doubledBase b ↔
      a = b ∨ (a ∈ upperMask S ∧ b ∈ upperMask S) ∨
        (a ∈ lowerMask S ∧ b ∈ lowerMask S) := by
  by_cases hab : a = b
  · simp [hab]
  · have h := D.pairBase_eq_zero_iff_clusterPairCollapses ⟨(a, b), hab⟩
    rw [clusterPairCollapses_iff_masks] at h
    change (D.toInteriorCollisionData.doubledBase b - D.toInteriorCollisionData.doubledBase a = 0 ↔ _) at h
    rw [sub_eq_zero] at h
    simpa only [hab, false_or] using (eq_comm.trans h)

theorem masks_disjoint : Disjoint (upperMask (m := m) S) (lowerMask S) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  simp [upperMask, lowerMask, Finset.image_image, doubledReflection, Function.comp_def] at hb

theorem root_part_eq_upper {a : DoubledLabel (N + 1) m} (ha : a ∈ upperMask S) :
    ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part a =
      upperMask S := by
  ext b
  rw [mem_root_part_iff, base_eq_iff_masks]
  constructor
  · rintro (rfl | ⟨_, hb⟩ | ⟨ha', _⟩)
    · exact ha
    · exact hb
    · exact (Finset.disjoint_left.mp (masks_disjoint (m := m) (S := S)) ha ha').elim
  · intro hb
    exact Or.inr (Or.inl ⟨ha, hb⟩)

theorem root_part_eq_lower {a : DoubledLabel (N + 1) m} (ha : a ∈ lowerMask S) :
    ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part a =
      lowerMask S := by
  ext b
  rw [mem_root_part_iff, base_eq_iff_masks]
  constructor
  · rintro (rfl | ⟨ha', _⟩ | ⟨_, hb⟩)
    · exact ha
    · exact (Finset.disjoint_left.mp (masks_disjoint (m := m) (S := S)) ha' ha).elim
    · exact hb
  · intro hb
    exact Or.inr (Or.inr ⟨ha, hb⟩)

theorem upper_mem_root_parts : upperMask S ∈
    ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).parts := by
  obtain ⟨a, ha⟩ := D.cluster_nonempty
  rw [← root_part_eq_upper D (a := Sum.inl (Sum.inl a))
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  exact (((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part_mem).mpr
    (Finset.mem_univ _)

theorem lower_mem_root_parts : lowerMask S ∈
    ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).parts := by
  obtain ⟨a, ha⟩ := D.cluster_nonempty
  have ha' : (Sum.inr a : DoubledLabel (N + 1) m) ∈ lowerMask S := by
    simp [lowerMask, upperMask, Finset.image_image, doubledReflection, Function.comp_def, ha]
  rw [← root_part_eq_lower D ha']
  exact (((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part_mem).mpr
    (Finset.mem_univ _)

theorem large_root_part_eq_mask (B : Finset (DoubledLabel (N + 1) m))
    (hB : B ∈ ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).parts)
    (hlarge : 1 < B.card) : B = upperMask S ∨ B = lowerMask S := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
  have he := ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part_eq_of_mem hB ha
  have hmem : b ∈ ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part a :=
    he.symm ▸ hb
  rw [mem_root_part_iff, base_eq_iff_masks] at hmem
  rcases hmem with h | h | h
  · exact (hab h).elim
  · exact Or.inl (he.symm.trans (root_part_eq_upper D h.1))
  · exact Or.inr (he.symm.trans (root_part_eq_lower D h.1))

theorem upper_part_card_le_one (hS : 1 < S.card)
    (B : Finset (DoubledLabel (N + 1) m))
    (hB : B ∈ ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions
      (upperMask S)).parts) : B.card ≤ 1 := by
  apply part_card_le_one_of_constant_base D.toInteriorCollisionData
    ⟨upperMask S, by rwa [upperMask_card]⟩ _ B hB
  intro a b
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp a.property
  obtain ⟨k, hk, hf⟩ := Finset.mem_image.mp b.property
  rw [← he, ← hf]
  exact congrArg (fun z : UpperHalfPlane => (z : ℂ)) (D.base_eq_of_mem hj hk)

theorem lower_part_card_le_one (hS : 1 < S.card)
    (B : Finset (DoubledLabel (N + 1) m))
    (hB : B ∈ ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions
      (lowerMask S)).parts) : B.card ≤ 1 := by
  rw [lowerMask, (extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions_mirror] at hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  rw [Finset.card_image_of_injective _ doubledReflection_involutive.injective]
  exact upper_part_card_le_one D hS C hC

/-- All three required finite partitions are proved for every genuine simple
interior collision, with no coverage or extracted-hierarchy hypothesis. -/
theorem threePartitions (hS : 1 < S.card) :
    PartitionCriterion D.toInteriorCollisionData.boundaryPoint S :=
  ⟨upper_mem_root_parts D, lower_mem_root_parts D, large_root_part_eq_mask D,
    upper_part_card_le_one D hS, lower_part_card_le_one D hS⟩

/-- Reverse codimension-one coverage of the original simple face point by its
actual extracted forest, retaining its prescribed cluster mask literally. -/
theorem exists_source_with_mask {r : ℕ} (hdim : GraphForms.dimension N m = r + 1)
    (hS : 1 < S.card) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 D.toInteriorCollisionData.boundaryPoint)
      (ho : ForestRadialFaceClassification.kind 0 D.toInteriorCollisionData.boundaryPoint o = .paired)
      (z : ForestRadialFaceLocalization.source hdim D.toInteriorCollisionData.boundaryPoint o),
      PairedForestSimpleCluster.S D.toInteriorCollisionData.boundaryPoint o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim D.toInteriorCollisionData.boundaryPoint o z =
        D.toInteriorCollisionData.boundaryPoint :=
  (singleInteriorCluster_coverage_iff hdim S D hS).mpr (threePartitions D hS)

/-- The canonical simple product datum is covered with no extra assumptions. -/
theorem canonicalDatum_exists_source_with_mask {r : ℕ}
    (hdim : GraphForms.dimension N m = r + 1) {a b : Fin (N + 1)}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : (0 : Fin (N + 1)) ∈ S → a = 0)
    (y : InteriorFaceDRCoordinates.Product (i := 0) (a := a) (b := b) (S := S) (m := m))
    (hy : (InteriorGraphFaceCoordinates.toAngular y).toFree.OpenConditions) :
    let E := InteriorFaceDRCoordinates.datum ha hb hanchor y hy
    ∃ (o : ForestRadialFaceClassification.Orbit 0 E.toInteriorCollisionData.boundaryPoint)
      (ho : ForestRadialFaceClassification.kind 0 E.toInteriorCollisionData.boundaryPoint o = .paired)
      (z : ForestRadialFaceLocalization.source hdim E.toInteriorCollisionData.boundaryPoint o),
      PairedForestSimpleCluster.S E.toInteriorCollisionData.boundaryPoint o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim E.toInteriorCollisionData.boundaryPoint o z =
        E.toInteriorCollisionData.boundaryPoint := by
  apply exists_source_with_mask _ hdim
  exact Finset.one_lt_card.mpr ⟨b, hb, a, ha, hba⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions
