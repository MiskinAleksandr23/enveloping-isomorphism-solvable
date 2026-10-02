import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPartialPositiveDR

/-! Exact doubled collision masks and the external direction/ratio formulas
of a strict paired forest face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestResolvedCoordinates
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference AncestorScaleRatios ComplexConjugate
open BoxStokes PairedForestCoarsePositions PairedForestSimpleCluster
open ForestDirectionRatioCoordinates
open scoped Classical UpperHalfPlane

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem mem_node_upper_iff (j : Fin (n + 1)) :
    Sum.inl (Sum.inl j) ∈ (node x o ho).val ↔ j ∈ S x o ho :=
  (mem_interiorLabels 0 x _ j).symm

/-- The simple interior pair mask is exactly the zero common-scale mask of
the native forest. -/
theorem pairCollapses_iff_le (e : DoubledPair (n + 1) m) :
    clusterPairCollapses (S x o ho) e ↔
      node x o ho ≤ pairNode (tree 0 x) (canonicalLeaf 0 x) e ∨
        reflection 0 x (node x o ho) ≤ pairNode (tree 0 x) (canonicalLeaf 0 x) e := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [clusterPairCollapses, pairNode, le_inf_iff, le_canonicalLeaf_iff,
      mem_reflection_iff, doubledReflection, mem_node_upper_iff,
      node_not_mirror, node_not_boundary, false_and, and_false, or_false, false_or]

theorem scale_pair_zero_iff (e : DoubledPair (n + 1) m) :
    scale (PairedForestCoarsePositions.parameters hdim x o z).1
      (pairNode (tree 0 x) (canonicalLeaf 0 x) e) = 0 ↔ clusterPairCollapses (S x o ho) e :=
  (scale_zero_iff hdim x o ho z _).trans (pairCollapses_iff_le x o ho e).symm

theorem scale_pair_pos (e : DoubledPair (n + 1) m) (he : ¬clusterPairCollapses (S x o ho) e) :
    0 < scale (PairedForestCoarsePositions.parameters hdim x o z).1
      (pairNode (tree 0 x) (canonicalLeaf 0 x) e) := by
  apply lt_of_le_of_ne (ForestPartialPositiveDR.scale_nonneg (tree 0 x)
    (PairedForestCoarsePositions.parameters hdim x o z) (radius_nonneg hdim x o z) _)
  exact Ne.symm (fun h => he ((scale_pair_zero_iff hdim x o ho z e).mp h))

theorem scale_common_pos (q : DoubledTriple (n + 1) m)
    (hq : ¬(clusterPairCollapses (S x o ho) (firstPair q) ∧
      clusterPairCollapses (S x o ho) (secondPair q))) :
    0 < scale (PairedForestCoarsePositions.parameters hdim x o z).1
      (pairNode (tree 0 x) (canonicalLeaf 0 x) (firstPair q) ⊓
        pairNode (tree 0 x) (canonicalLeaf 0 x) (secondPair q)) := by
  apply scale_pos_of_not_le hdim x o ho z
  · intro h
    exact hq ⟨(pairCollapses_iff_le x o ho _).mpr (Or.inl (h.trans inf_le_left)),
      (pairCollapses_iff_le x o ho _).mpr (Or.inl (h.trans inf_le_right))⟩
  · intro h
    exact hq ⟨(pairCollapses_iff_le x o ho _).mpr (Or.inr (h.trans inf_le_left)),
      (pairCollapses_iff_le x o ho _).mpr (Or.inr (h.trans inf_le_right))⟩

/-- Native doubled base coordinates are the same one positive real affine
normalization of every coarse forest position. -/
theorem doubledBase_eq (a : DoubledLabel (n + 1) m) :
    (datum hdim x o ho z).toInteriorCollisionData.doubledBase a =
      ((normalizer hdim x o ho z).scale : ℂ) * positions hdim x o z a +
        ((normalizer hdim x o ho z).shift : ℂ) := by
  rcases a with (j | j) | j
  · exact PositiveAffine.coe_onUpper _ _
  · have hr : positions hdim x o z (Sum.inl (Sum.inr j)) =
        ((positions hdim x o z (Sum.inl (Sum.inr j))).re : ℂ) :=
      ForestChartConfigurations.boundary_eq_ofReal (shapeData 0 x)
        (PairedForestCoarsePositions.parameters hdim x o z)
        (radius_reflect hdim x o z) (increment_reflect hdim x o z) j
    change (((normalizer hdim x o ho z).onReal _ : ℝ) : ℂ) = _
    rw [hr]
    simp only [PositiveAffine.onReal, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_re]
  · change conj ((base hdim x o ho z j : ℍ) : ℂ) = _
    rw [base, PositiveAffine.coe_onUpper, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    exact congrArg (fun w => ((normalizer hdim x o ho z).scale : ℂ) * w +
      ((normalizer hdim x o ho z).shift : ℂ)) (positions_reflect hdim x o z (Sum.inl (Sum.inl j))).symm

theorem pairBase_eq (e : DoubledPair (n + 1) m) :
    (datum hdim x o ho z).toInteriorCollisionData.pairBase e =
      (normalizer hdim x o ho z).scale •
        pairDifference (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e := by
  unfold InteriorCollisionData.pairBase
  rw [doubledBase_eq, doubledBase_eq]
  change _ = (normalizer hdim x o ho z).scale • (positions hdim x o z e.val.2 - positions hdim x o z e.val.1)
  rw [Complex.real_smul, mul_sub]
  ring

theorem direction_external (e : DoubledPair (n + 1) m) (he : ¬clusterPairCollapses (S x o ho) e) :
    direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e =
      complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairBase e) := by
  rw [pairBase_eq, complexPhase_pos_real_smul (normalizer hdim x o ho z).scale_pos]
  exact ForestPartialPositiveDR.direction_eq_actual (tree 0 x) _ _ e (scale_pair_pos hdim x o ho z e he)

theorem ratio_external (q : DoubledTriple (n + 1) m)
    (hq : ¬(clusterPairCollapses (S x o ho) (firstPair q) ∧
      clusterPairCollapses (S x o ho) (secondPair q))) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) q =
      (normalizedNormRatio ((datum hdim x o ho z).toInteriorCollisionData.pairBase (firstPair q))
        ((datum hdim x o ho z).toInteriorCollisionData.pairBase (secondPair q)) : ℝ) := by
  rw [pairBase_eq, pairBase_eq]
  simp only [Complex.real_smul]
  rw [normalizedNormRatio_pos_real_mul _ (normalizer hdim x o ho z).scale_pos]
  exact ForestPartialPositiveDR.ratioValue_eq_actual (tree 0 x) _ _ (radius_nonneg hdim x o z) q
    (scale_common_pos hdim x o ho z q hq).ne'

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestResolvedCoordinates
