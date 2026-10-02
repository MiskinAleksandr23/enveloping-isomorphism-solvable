import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeData
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope

/-! Exact centers and positive radii of the actual extracted approximating
configurations. Leaf radii are set to their parent radii, giving local radius
one on leaves. This parameter sequence is used in the unconstrained forward
encoder; it does not assert independent free-frame constraints at positive scale. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestParameters

open Filter Topology Configuration ComplexConjugate
open SubsetNormalizedLimits (LargeSubset)
open ReflectedForestExtraction ReflectedSubsetNormalization
open ExtractedForestChildShapes
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

abbrev tree := compactificationTree i x
abbrev extraction := compactificationExtraction i x

def point (k : ℕ) : DoubledLabel n m → ℂ :=
  CompactificationClusterLimits.doubledSequence i x ((extraction i x).subsequence k)

theorem point_injective (k : ℕ) : Function.Injective (point i x k) :=
  CompactificationClusterLimits.doubledSequence_injective i x _

theorem root_large : 1 < (⊥ : tree i x).val.card := by
  change 1 < (Finset.univ : Finset (DoubledLabel n m)).card
  exact Finset.one_lt_card.mpr ⟨Sum.inl (Sum.inl i), Finset.mem_univ _,
    Sum.inr i, Finset.mem_univ _, by simp⟩

theorem node_nonempty (v : tree i x) : v.val.Nonempty :=
  ClusterPartitionTree.nonempty_of_mem_clusters (extraction i x).partitions
    (extraction i x).partitions_proper Finset.univ v.val ⟨Sum.inr i, Finset.mem_univ _⟩ v.property

def selectedLabel (v : tree i x) : v.val :=
  ⟨(node_nonempty i x v).choose, (node_nonempty i x v).choose_spec⟩

theorem parent_part (v : tree i x) (hv : v ≠ ⊥) :
    1 < (Order.pred v).val.card ∧ v.val ∈ ((extraction i x).partitions (Order.pred v).val).parts := by
  apply ClusterPartitionTree.parent_part v
  intro h
  exact hv (Subtype.ext h)
  exact ⟨Sum.inr i, Finset.mem_univ _⟩

theorem parent_cover (v : tree i x) (hv : v ≠ ⊥) : Order.pred v ⋖ v :=
  ((extraction i x).tree_child_iff_partition Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩ _ _).mpr
    (parent_part i x v hv)

def center (k : ℕ) (v : tree i x) : ℂ :=
  if hv : 1 < v.val.card then centerOn doubledReflection doubledReflection_involutive
    ⟨v.val, hv⟩ (point i x k)
  else point i x k (selectedLabel i x v)

/-- Internal radii are genuine extracted radii. Dummy leaf radii make every
local radius positive, while leaving all positions and increments unchanged. -/
def positiveRadius (k : ℕ) (v : tree i x) : ℝ :=
  if hv : 1 < v.val.card then radiusOn doubledReflection doubledReflection_involutive
    ⟨v.val, hv⟩ (point i x k)
  else (extraction i x).nodeRadius (Order.pred v).val k

theorem positiveRadius_of_large (k : ℕ) (v : tree i x) (hv : 1 < v.val.card) :
    positiveRadius i x k v = (extraction i x).nodeRadius v.val k := by
  simp only [positiveRadius, ReflectedForestExtraction.Extraction.nodeRadius, dif_pos hv, point]

theorem positiveRadius_pos (k : ℕ) (v : tree i x) : 0 < positiveRadius i x k v := by
  by_cases hv : 1 < v.val.card
  · rw [positiveRadius, dif_pos hv]
    exact radiusOn_pos _ _ _ _ (point_injective i x k)
  · have hvroot : v ≠ ⊥ := by intro heq; exact hv (heq ▸ root_large i x)
    have hp := (parent_part i x v hvroot).1
    rw [positiveRadius, dif_neg hv, ReflectedForestExtraction.Extraction.nodeRadius, dif_pos hp]
    exact radiusOn_pos _ _ _ _ (point_injective i x k)

theorem positiveRadius_leaf (k : ℕ) (v : tree i x) (hv : ¬1 < v.val.card) :
    positiveRadius i x k v = positiveRadius i x k (Order.pred v) := by
  have hvroot : v ≠ ⊥ := by intro heq; exact hv (heq ▸ root_large i x)
  rw [positiveRadius, dif_neg hv, positiveRadius_of_large i x k _ (parent_part i x v hvroot).1]

theorem selectedLabel_leaf (v : DoubledLabel n m) :
    (selectedLabel i x (canonicalLeaf i x v)).val = v :=
  Finset.mem_singleton.mp (selectedLabel i x (canonicalLeaf i x v)).property

@[simp] theorem center_leaf (k : ℕ) (v : DoubledLabel n m) :
    center i x k (canonicalLeaf i x v) = point i x k v := by
  simp only [center, canonicalLeaf_label, Finset.card_singleton, lt_self_iff_false, dif_neg not_false]
  rw [selectedLabel_leaf]

def localRadii (k : ℕ) : tree i x → ℝ :=
  ForestNormalizationTelescope.localRadius (tree i x) (positiveRadius i x k)

def localIncrements (k : ℕ) : tree i x → ℂ :=
  ForestNormalizationTelescope.localIncrement (tree i x) (positiveRadius i x k) (center i x k)

theorem localRadii_pos (k : ℕ) (v : tree i x) : 0 < localRadii i x k v :=
  ForestNormalizationTelescope.localRadius_pos (tree i x) _ (positiveRadius_pos i x k) v

theorem localRadii_root (k : ℕ) : localRadii i x k ⊥ = 1 :=
  ForestNormalizationTelescope.localRadius_root (tree i x) _ (positiveRadius_pos i x k)

theorem localRadii_leaf (k : ℕ) (v : tree i x) (hv : ¬1 < v.val.card) : localRadii i x k v = 1 := by
  change positiveRadius i x k v / positiveRadius i x k (Order.pred v) = 1
  rw [positiveRadius_leaf i x k v hv, div_self (positiveRadius_pos i x k (Order.pred v)).ne']

/-- The radius-one convention on leaves removes redundant radial variables. -/
def limitingRadii (v : tree i x) : ℝ := if v = ⊥ then 1 else if 1 < v.val.card then 0 else 1

theorem tendsto_localRadii (v : tree i x) :
    Tendsto (fun k => localRadii i x k v) atTop (𝓝 (limitingRadii i x v)) := by
  by_cases hvroot : v = ⊥
  · subst v
    simpa only [localRadii_root, limitingRadii, ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · by_cases hv : 1 < v.val.card
    · have hp := (parent_part i x v hvroot).1
      have h := (extraction i x).tree_child_scale_separation Finset.univ
        ⟨Sum.inr i, Finset.mem_univ _⟩ (Order.pred v) v (parent_cover i x v hvroot)
      simpa only [localRadii, ForestNormalizationTelescope.localRadius,
        positiveRadius_of_large i x _ v hv, positiveRadius_of_large i x _ (Order.pred v) hp,
        limitingRadii, if_neg hvroot, if_pos hv] using h
    · simpa only [localRadii_leaf i x _ v hv, limitingRadii, if_neg hvroot, if_neg hv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

theorem position_eq_normalized_point (k : ℕ) (v : DoubledLabel n m) :
    ForestInsertionDifference.position (tree i x) (localRadii i x k) (localIncrements i x k) (canonicalLeaf i x v) =
      (positiveRadius i x k ⊥)⁻¹ • (point i x k v - center i x k ⊥) := by
  unfold localRadii localIncrements
  rw [ForestNormalizationTelescope.position_localRadius_increment (tree i x)
    (positiveRadius i x k) (positiveRadius_pos i x k) (center i x k), center_leaf]

theorem pairDifference_eq (k : ℕ) (v w : DoubledLabel n m) :
    ForestInsertionDifference.position (tree i x) (localRadii i x k) (localIncrements i x k) (canonicalLeaf i x v) -
      ForestInsertionDifference.position (tree i x) (localRadii i x k) (localIncrements i x k) (canonicalLeaf i x w) =
        (positiveRadius i x k ⊥)⁻¹ • (point i x k v - point i x k w) := by
  rw [position_eq_normalized_point, position_eq_normalized_point, ← smul_sub]
  congr 1
  abel_nf

/-- Every actual center displacement converges to its representative-independent child shape. -/
theorem tendsto_localIncrements (v : tree i x) :
    Tendsto (fun k => localIncrements i x k v) atTop (𝓝 (canonicalIncrement i x v)) := by
  by_cases hvroot : v = ⊥
  · subst v
    simp [localIncrements, canonicalIncrement, increment]
  · have hp := parent_part i x v hvroot
    let A : LargeSubset (DoubledLabel n m) := ⟨(Order.pred v).val, hp.1⟩
    have hinc (j : v.val) : canonicalIncrement i x v =
        (extraction i x).shapes A ⟨j.val, ((extraction i x).partitions (Order.pred v).val).le hp.2 j.property⟩ := by
      have h := increment_eq_shape_of_child (extraction i x) Finset.univ
        ⟨Sum.inr i, Finset.mem_univ _⟩ _ v (parent_cover i x v hvroot) j.val j.property
      simpa only [canonicalIncrement, extraction, A, SubsetNormalizedLimits.extendedShape,
        dif_pos (((extraction i x).partitions (Order.pred v).val).le hp.2 j.property)] using h
    by_cases hv : 1 < v.val.card
    · let B : LargeSubset (DoubledLabel n m) := ⟨v.val, hv⟩
      rw [hinc (chosenAnchor doubledReflection doubledReflection_involutive B)]
      simpa only [localIncrements, ForestNormalizationTelescope.localIncrement,
        positiveRadius, dif_pos hp.1, center, dif_pos hv, point, A, B,
        SubsetNormalizedLimits.inclusion] using
          (extraction i x).child_center_offset A B hp.2
    · let j := selectedLabel i x v
      rw [hinc j]
      have h := ((continuous_apply
        (⟨j.val, ((extraction i x).partitions (Order.pred v).val).le hp.2 j.property⟩ : A.val)).tendsto
          ((extraction i x).shapes A)).comp ((extraction i x).limits A)
      simpa only [Function.comp_def, normalizedOn_apply, localIncrements,
        ForestNormalizationTelescope.localIncrement, positiveRadius, dif_pos hp.1,
        center, dif_neg hv, point] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestParameters
