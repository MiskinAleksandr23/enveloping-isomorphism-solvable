import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestReverseCoverageCriterion
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedPartitionDepthTwo
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDRCoordinates

/-! Exact reverse coverage reduced to three actual extracted finite partitions.
In particular the final theorem applies to the canonical simple interior datum;
it does not assume that datum's extracted hierarchy has the desired shape. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestThreePartitionCriterion

open Configuration ExtractedForestParameters ExtractedForestFrames
open ReflectedRadiusCoordinates ForestRadialFaceClassification
open PairedForestReverseCoverageCriterion
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (S : Finset (Fin (n + 1)))

theorem upperMask_card : (upperMask (m := m) S).card = S.card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact Sum.inl.inj (Sum.inl.inj h)

theorem lowerMask_card : (lowerMask (m := m) S).card = S.card := by
  rw [lowerMask, Finset.card_image_of_injective _ doubledReflection_involutive.injective,
    upperMask_card]

theorem upperMask_ne_univ : upperMask (m := m) S ≠ Finset.univ := by
  intro he
  have h : (Sum.inr (0 : Fin (n + 1)) : DoubledLabel (n + 1) m) ∈ upperMask S :=
    he.symm ▸ Finset.mem_univ _
  simp [upperMask] at h

theorem lowerMask_ne_univ : lowerMask (m := m) S ≠ Finset.univ := by
  intro he
  have h : (Sum.inl (Sum.inl (0 : Fin (n + 1))) : DoubledLabel (n + 1) m) ∈ lowerMask S :=
    he.symm ▸ Finset.mem_univ _
  simp [lowerMask, upperMask, Finset.image_image, doubledReflection, Function.comp_def] at h

private theorem active_of_large (B : Finset (DoubledLabel (n + 1) m))
    (hB : B ∈ (extraction 0 x).clusters Finset.univ)
    (hBR : B ≠ Finset.univ) (hlarge : 1 < B.card) :
    Active (tree 0 x) (⟨B, hB⟩ : tree 0 x) := by
  refine ⟨fun h => hBR (congrArg Subtype.val h), ?_⟩
  intro hmax
  have hc := (ClusterPartitionTree.isMax_iff_card_eq_one
    (hR := ⟨Sum.inr (0 : Fin (n + 1)), Finset.mem_univ _⟩)
    (⟨B, hB⟩ : tree 0 x)).mp hmax
  change B.card = 1 at hc
  omega

/-- Only the root and the two prescribed mask partitions are inspected. -/
def PartitionCriterion : Prop :=
  PairedPartitionDepthTwo.ThreePartitions (extraction 0 x).partitions Finset.univ
    (upperMask S) (lowerMask S)

/-- The active-node criterion is equivalent to a test of just three finite
partitions; no radial chart or analytic assertion occurs on the right. -/
theorem active_labels_iff_threePartitions (hS : 1 < S.card) :
    (∃ u : ActiveNode (tree 0 x), u.val.val = upperMask S ∧
      ∀ v : ActiveNode (tree 0 x),
        v.val.val = upperMask S ∨ v.val.val = lowerMask S) ↔ PartitionCriterion x S := by
  have hU : 1 < (upperMask (m := m) S).card := by rwa [upperMask_card]
  have hUV : (upperMask (m := m) S).card = (lowerMask (m := m) S).card := by
    rw [upperMask_card, lowerMask_card]
  rw [PartitionCriterion, ← PairedPartitionDepthTwo.large_clusters_iff_threePartitions
    (extraction 0 x).partitions (extraction 0 x).partitions_proper Finset.univ
    (upperMask S) (lowerMask S) (root_large 0 x) hU hUV
    (upperMask_ne_univ S) (lowerMask_ne_univ S)]
  constructor
  · rintro ⟨u, hu, hall⟩
    have hupper : upperMask S ∈ (extraction 0 x).clusters Finset.univ := hu ▸ u.val.property
    have hlower : lowerMask S ∈ (extraction 0 x).clusters Finset.univ := by
      have hr := (reflection 0 x u.val).property
      change (reflection 0 x u.val).val ∈ (extraction 0 x).clusters Finset.univ at hr
      rw [reflection_label, hu] at hr
      exact hr
    refine ⟨hupper, hlower, ?_⟩
    intro B hB hBR hlarge
    exact hall ⟨⟨B, hB⟩, active_of_large x B hB hBR hlarge⟩
  · rintro ⟨hu, _, hall⟩
    let u : ActiveNode (tree 0 x) :=
      ⟨⟨upperMask S, hu⟩, active_of_large x _ hu (upperMask_ne_univ S) hU⟩
    refine ⟨u, rfl, ?_⟩
    intro v
    exact hall v.val.val v.val.property
      (fun he => v.property.1 (Subtype.ext he))
      (ExtractedForestIdentification.nonleaf_large 0 x v.val v.property.2)

/-- Literal strict-face coverage, retaining the original label mask, is
equivalent to the three finite partition tests. -/
theorem source_with_mask_iff_threePartitions (hS : 1 < S.card) :
    (∃ (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
      (z : ForestRadialFaceLocalization.source hdim x o),
      PairedForestSimpleCluster.S x o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = x) ↔ PartitionCriterion x S :=
  (source_with_mask_iff hdim x S).trans (active_labels_iff_threePartitions x S hS)

/-- Unconditional equivalence for a prescribed genuine simple interior face.
The unresolved analytic content is precisely the explicitly defined finite
partition property on the right, not an assumed coverage hypothesis. -/
theorem singleInteriorCluster_coverage_iff (D : SingleInteriorCluster (0 : Fin (n + 1)) m S)
    (hS : 1 < S.card) :
    (∃ (o : ForestRadialFaceClassification.Orbit 0 D.toInteriorCollisionData.boundaryPoint)
      (ho : kind 0 D.toInteriorCollisionData.boundaryPoint o = .paired)
      (z : ForestRadialFaceLocalization.source hdim D.toInteriorCollisionData.boundaryPoint o),
      PairedForestSimpleCluster.S D.toInteriorCollisionData.boundaryPoint o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim D.toInteriorCollisionData.boundaryPoint o z =
        D.toInteriorCollisionData.boundaryPoint) ↔
      PartitionCriterion D.toInteriorCollisionData.boundaryPoint S :=
  source_with_mask_iff_threePartitions hdim D.toInteriorCollisionData.boundaryPoint S hS

/-- The canonical coarse/planar product datum satisfies the same exact test;
its two marked cluster labels supply the required genuine-collision size. -/
theorem canonicalDatum_coverage_iff {a b : Fin (n + 1)}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : (0 : Fin (n + 1)) ∈ S → a = 0)
    (y : InteriorFaceDRCoordinates.Product (i := 0) (a := a) (b := b) (S := S) (m := m))
    (hy : (InteriorGraphFaceCoordinates.toAngular y).toFree.OpenConditions) :
    let D := InteriorFaceDRCoordinates.datum ha hb hanchor y hy
    (∃ (o : ForestRadialFaceClassification.Orbit 0 D.toInteriorCollisionData.boundaryPoint)
      (ho : kind 0 D.toInteriorCollisionData.boundaryPoint o = .paired)
      (z : ForestRadialFaceLocalization.source hdim D.toInteriorCollisionData.boundaryPoint o),
      PairedForestSimpleCluster.S D.toInteriorCollisionData.boundaryPoint o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim D.toInteriorCollisionData.boundaryPoint o z =
        D.toInteriorCollisionData.boundaryPoint) ↔
      PartitionCriterion D.toInteriorCollisionData.boundaryPoint S := by
  apply singleInteriorCluster_coverage_iff hdim S
  exact Finset.one_lt_card.mpr ⟨b, hb, a, ha, hba⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestThreePartitionCriterion
