import EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestResolvedRatioZero

/-! The zero triple-ratio pattern of a genuine simple face determines the
label set of every zero-radius node, even in a chart with another center. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceZeroNodeLabels

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestDirectionRatioCoordinates ReflectedRadiusCoordinates
open PairedForestReverseCoverageCriterion SingleInteriorExtractedPartitions
open scoped Classical

variable {n m : ℕ}

theorem boundaryPoint_ratio_zero_iff {i : Fin n} (D : InteriorCollisionData i m)
    (t : DoubledTriple n m) :
    (D.boundaryPoint.val.2.2 t : ℝ) = 0 ↔
      D.pairBase ⟨(t.val.1, t.val.2.1), t.property.1⟩ = 0 ∧
        D.pairBase ⟨(t.val.1, t.val.2.2), t.property.2⟩ ≠ 0 := by
  constructor
  · intro h
    have hp : D.pairBase ⟨(t.val.1, t.val.2.1), t.property.1⟩ = 0 := by
      by_contra hp
      exact (boundaryPoint_ratio_pos_of_pairBase_ne_zero D t hp).ne' h
    refine ⟨hp, ?_⟩
    intro hq
    exact (boundaryPoint_ratio_pos_of_pairBases_zero D t hp hq).ne' h
  · rintro ⟨hp, hq⟩
    exact boundaryPoint_ratio_eq_zero_of_mixed D t hp hq

variable {S : Finset (Fin (n + 1))}
  (D : SingleInteriorCluster (0 : Fin (n + 1)) m S)

/-- A proper large label set with vanishing internal/external ratios must be
one complete collision mask. This uses the explicit simple face ratios alone. -/
theorem label_eq_mask_of_cross_ratios
    (A : Finset (DoubledLabel (n + 1) m)) (hA : 1 < A.card) (hproper : A ≠ Finset.univ)
    (hzero : ∀ a ∈ A, ∀ b ∈ A, ∀ c, c ∉ A → ∀ (hab : a ≠ b) (hac : a ≠ c),
      (D.toInteriorCollisionData.boundaryPoint.val.2.2 ⟨(a, b, c), hab, hac⟩ : ℝ) = 0) :
    A = upperMask S ∨ A = lowerMask S := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hA
  have houtside : ∃ c, c ∉ A := by
    by_contra h
    apply hproper
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨c, hc⟩ := houtside
  have hpart : A = ((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part a := by
    ext d
    rw [mem_root_part_iff]
    constructor
    · intro hd
      by_cases had : a = d
      · rw [had]
      · have hac : a ≠ c := fun he => hc (he ▸ ha)
        have hz := (boundaryPoint_ratio_zero_iff D.toInteriorCollisionData _).mp
          (hzero a ha d hd c hc had hac)
        exact (sub_eq_zero.mp hz.1).symm
    · intro hd
      by_contra hdA
      have had : a ≠ d := fun he => hdA (he ▸ ha)
      have hz := (boundaryPoint_ratio_zero_iff D.toInteriorCollisionData _).mp
        (hzero a ha b hb d hdA hab had)
      exact hz.2 (sub_eq_zero.mpr hd.symm)
  apply large_root_part_eq_mask D A _ hA
  rw [hpart]
  exact (((extraction 0 D.toInteriorCollisionData.boundaryPoint).partitions Finset.univ).part_mem).mpr
    (Finset.mem_univ _)

variable (x : Compactification (0 : Fin (n + 1)) m)
  (p : Domain (tree 0 x) (canonicalLeaf 0 x))
  (hDR : doubledCoordinates (tree 0 x) (canonicalLeaf 0 x) p =
    projectDR D.toInteriorCollisionData.boundaryPoint.val)

include hDR

theorem ratioValue_eq_boundary (t : DoubledTriple (n + 1) m) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) p.val t =
      (D.toInteriorCollisionData.boundaryPoint.val.2.2 t : ℝ) :=
  congrArg (fun d : DRData (n + 1) m => (d.2 t : ℝ)) hDR

/-- Every active zero-radius node of any native forest encoding this simple
point carries the whole original mask or its reflection. The chart center is
arbitrary, and other radii need not be assumed positive. -/
theorem zero_node_label (v : ActiveNode (tree 0 x)) (hv : p.val.1 v.val = 0) :
    v.val.val = upperMask S ∨ v.val.val = lowerMask S := by
  apply label_eq_mask_of_cross_ratios D v.val.val
    (ExtractedForestIdentification.nonleaf_large 0 x v.val v.property.2)
    (fun he => v.property.1 (Subtype.ext he))
  intro a ha b hb c hc hab hac
  rw [← ratioValue_eq_boundary D x p hDR]
  exact ForestResolvedRatioZero.ratioValue_eq_zero_of_zero_ancestor
    (tree 0 x) (canonicalLeaf 0 x) p v.val hv a b c hab hac
    ((le_canonicalLeaf_iff 0 x v.val a).mpr ha)
    ((le_canonicalLeaf_iff 0 x v.val b).mpr hb)
    (fun h => hc ((le_canonicalLeaf_iff 0 x v.val c).mp h))

/-- The simple collision has an actual zero node carrying its upper mask in
every admissible native forest representation with the same full DR data. -/
theorem exists_zero_upper (hS : 1 < S.card) :
    ∃ v : ActiveNode (tree 0 x), v.val.val = upperMask S ∧ p.val.1 v.val = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hS
  let a' : DoubledLabel (n + 1) m := Sum.inl (Sum.inl a)
  let b' : DoubledLabel (n + 1) m := Sum.inl (Sum.inl b)
  let c' : DoubledLabel (n + 1) m := Sum.inr a
  have hab' : a' ≠ b' := fun h => hab (Sum.inl.inj (Sum.inl.inj h))
  have hac' : a' ≠ c' := by simp [a', c']
  let t : DoubledTriple (n + 1) m := ⟨(a', b', c'), hab', hac'⟩
  have hz : ratioValue (tree 0 x) (canonicalLeaf 0 x) p.val t = 0 := by
    rw [ratioValue_eq_boundary D x p hDR]
    apply boundaryPoint_ratio_eq_zero_of_mixed
    · exact (D.pairBase_eq_zero_iff_clusterPairCollapses _).mpr ⟨ha, hb⟩
    · exact (D.pairBase_eq_zero_iff_clusterPairCollapses _).not.mpr (by simp [clusterPairCollapses, t, a', c'])
  obtain ⟨v, hlow, hhigh, hv⟩ :=
    (ForestResolvedRatioZero.ratioValue_eq_zero_iff_exists_zero_between
      (tree 0 x) (canonicalLeaf 0 x) p t).mp hz
  have hactive : Active (tree 0 x) v := by
    refine ⟨fun he => ?_, ?_⟩
    · rw [he] at hlow
      exact (not_lt_bot hlow)
    · intro hmax
      have hpair := ForestLeafRadii.pairNode_nonleaf (tree 0 x) (canonicalLeaf 0 x)
        (canonicalLeaf_injective 0 x) (canonicalLeaf_isMax 0 x) (firstPair t)
      have he : v = pairNode (tree 0 x) (canonicalLeaf 0 x) (firstPair t) :=
        le_antisymm hhigh (hmax hhigh)
      exact hpair (he ▸ hmax)
  have hmem : a' ∈ v.val :=
    (le_canonicalLeaf_iff 0 x v a').mp (hhigh.trans inf_le_left)
  rcases zero_node_label D x p hDR ⟨v, hactive⟩ hv with hupper | hlower
  · exact ⟨⟨v, hactive⟩, hupper, hv⟩
  · rw [hlower] at hmem
    have hupper : a' ∈ upperMask S := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact (Finset.disjoint_left.mp (masks_disjoint (m := m) (S := S)) hupper hmem).elim

/-- No two different zero-radius nodes can be nested. -/
theorem zero_nodes_not_lt (u v : ActiveNode (tree 0 x))
    (hu : p.val.1 u.val = 0) (hv : p.val.1 v.val = 0) : ¬u.val < v.val := by
  intro hlt
  change v.val.val ⊂ u.val.val at hlt
  have hcard := Finset.card_lt_card hlt
  have huc : u.val.val.card = S.card := by
    rcases zero_node_label D x p hDR u hu with h | h <;>
      rw [h]
    · exact PairedForestThreePartitionCriterion.upperMask_card S
    · exact PairedForestThreePartitionCriterion.lowerMask_card S
  have hvc : v.val.val.card = S.card := by
    rcases zero_node_label D x p hDR v hv with h | h <;>
      rw [h]
    · exact PairedForestThreePartitionCriterion.upperMask_card S
    · exact PairedForestThreePartitionCriterion.lowerMask_card S
  omega

/-- All zero nodes belong to the reflection orbit of any upper-mask node. -/
theorem zero_node_orbit_eq (u : ActiveNode (tree 0 x)) (hu : u.val.val = upperMask S)
    (v : ActiveNode (tree 0 x)) (hv : p.val.1 v.val = 0) :
    orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) v =
      orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u := by
  apply (orbitClass_eq_iff _ _ _ v u).mpr
  rcases zero_node_label D x p hDR v hv with h | h
  · exact Or.inl (Subtype.ext (Subtype.ext (h.trans hu.symm)))
  · right
    apply Subtype.ext
    apply (reflection 0 x).injective
    change reflection 0 x (reflection 0 x v.val) = reflection 0 x u.val
    rw [reflection_reflection]
    apply Subtype.ext
    rw [ForestRadialFaceClassification.reflection_label, hu]
    exact h

/-- Positivity of every other orbit follows from nonnegativity and the
proved classification of zero nodes; it is not a transfer hypothesis. -/
theorem radius_pos_of_orbit_ne (u : ActiveNode (tree 0 x)) (hu : u.val.val = upperMask S)
    (v : ActiveNode (tree 0 x))
    (hne : orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) v ≠
      orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u) :
    0 < p.val.1 v.val := by
  have hz : p.val.1 v.val ≠ 0 := fun hv => hne (zero_node_orbit_eq D x p hDR u hu v hv)
  exact lt_of_le_of_ne (p.property.1 v.val) hz.symm

/-- The actual native radius pattern needed for transfer to a specified
chart: an upper zero node and strictly positive radii in every other orbit. -/
theorem exists_unique_zero_orbit (hS : 1 < S.card) :
    ∃ u : ActiveNode (tree 0 x), u.val.val = upperMask S ∧ p.val.1 u.val = 0 ∧
      ∀ v : ActiveNode (tree 0 x),
        orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) v ≠
          orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u →
        0 < p.val.1 v.val := by
  obtain ⟨u, hu, hz⟩ := exists_zero_upper D x p hDR hS
  exact ⟨u, hu, hz, radius_pos_of_orbit_ne D x p hDR u hu⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceZeroNodeLabels
