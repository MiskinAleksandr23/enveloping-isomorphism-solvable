import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedChildLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetPartitions
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedPartitionTree
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactificationClusterLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.DoubledReflection

/-!
# Actual reflected rooted-tree extraction above compactification points

All normalized subset shapes are extracted by one finite-product compactness
argument. Their genuine equal-value partitions recursively construct a finite
native RootedTree. Reflection, node shapes, strict cardinal decrease, and all
child-scale limits are proved for this construction; no extraction existence
or hierarchy certificate is an input to the compactification theorem.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestExtraction

open Filter Topology ComplexConjugate Configuration
open SubsetNormalizedLimits (LargeSubset ShapeFamily inclusion)
open ReflectedSubsetNormalization ReflectedSubsetLimits
open scoped Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

structure Extraction (σ : I → I) (hσ : Function.Involutive σ) (p : ℕ → I → ℂ) where
  input_mirror : ∀ k j, p k (σ j) = conj (p k j)
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  shapes : ShapeFamily I
  limits : ∀ A : LargeSubset I,
    Tendsto (fun k => normalizedOn σ hσ A (p (subsequence k))) atTop (𝓝 (shapes A))
  shapes_mirror : MirrorCompatible σ hσ shapes
  anchor_re : ∀ A : LargeSubset I, (shapes A (chosenAnchor σ hσ A)).re = 0
  anchor_zero : ∀ A : LargeSubset I, ¬IsStable σ A → shapes A (chosenAnchor σ hσ A) = 0
  unit_norm : ∀ A : LargeSubset I, ‖shapes A‖ = 1

omit [DecidableEq I] in
/-- Actual simultaneous compact extraction constructs the reflected data. -/
theorem nonempty_extraction (σ : I → I) (hσ : Function.Involutive σ) (p : ℕ → I → ℂ)
    (hp : ∀ k, Function.Injective (p k)) (hmirror : ∀ k j, p k (σ j) = conj (p k j)) :
    Nonempty (Extraction σ hσ p) := by
  obtain ⟨φ, q, hφ, hlim, hmir, hre, hz, hn, _⟩ := exists_common_reflected_limits σ hσ p hp hmirror
  exact ⟨⟨hmirror, φ, hφ, q, hlim, hmir, hre, hz, hn⟩⟩

def extract (σ : I → I) (hσ : Function.Involutive σ) (p : ℕ → I → ℂ)
    (hp : ∀ k, Function.Injective (p k)) (hmirror : ∀ k j, p k (σ j) = conj (p k j)) :
    Extraction σ hσ p := Classical.choice (nonempty_extraction σ hσ p hp hmirror)

namespace Extraction

variable {σ : I → I} {hσ : Function.Involutive σ} {p : ℕ → I → ℂ}

omit [DecidableEq I] in
theorem shapes_nonconstant (E : Extraction σ hσ p) (A : LargeSubset I) :
    ∃ j k, E.shapes A j ≠ E.shapes A k :=
  nonconstant_of_mirrorCompatible σ hσ E.shapes E.shapes_mirror A
    (E.anchor_re A) (E.anchor_zero A) (E.unit_norm A)

def partitions (E : Extraction σ hσ p) (A : Finset I) : Finpartition A :=
  SubsetNormalizedLimits.partition E.shapes A

theorem partitions_proper (E : Extraction σ hσ p) (A : Finset I) (hA : 1 < A.card)
    (B : Finset I) (hB : B ∈ (E.partitions A).parts) : B.card < A.card :=
  SubsetNormalizedLimits.partition_proper E.shapes E.shapes_nonconstant A hA B hB

theorem partitions_mirror (E : Extraction σ hσ p) (A : Finset I) :
    (E.partitions (A.image σ)).parts = (E.partitions A).parts.image (Finset.image σ) :=
  ReflectedSubsetPartitions.partition_parts_mirror σ hσ E.shapes E.shapes_mirror A

def clusters (E : Extraction σ hσ p) (R : Finset I) : Finset (Finset I) :=
  ClusterPartitionTree.clusters E.partitions E.partitions_proper R

def tree (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty) : RootedTree :=
  ClusterPartitionTree.tree E.partitions E.partitions_proper R hR

instance treeFintype (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty) : Fintype (E.tree R hR) :=
  inferInstanceAs (Fintype (ClusterPartitionTree.tree E.partitions E.partitions_proper R hR))

/-- Reflection is an actual involutive order automorphism of the extracted tree. -/
def reflection (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty) (hroot : R.image σ = R) :
    E.tree R hR ≃o E.tree R hR :=
  ReflectedPartitionTree.nodeOrderIso σ hσ E.partitions E.partitions_mirror E.partitions_proper R hR hroot

theorem reflection_involutive (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty) (hroot : R.image σ = R) :
    Function.Involutive (E.reflection R hR hroot) :=
  ReflectedPartitionTree.nodeOrderIso_involutive σ hσ E.partitions E.partitions_mirror E.partitions_proper R hR hroot

@[simp] theorem reflection_label (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (hroot : R.image σ = R) (v : E.tree R hR) : (E.reflection R hR hroot v).val = v.val.image σ := rfl

theorem reflection_parent (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (hroot : R.image σ = R) (v : E.tree R hR) :
    E.reflection R hR hroot (Order.pred v) = Order.pred (E.reflection R hR hroot v) :=
  (E.reflection R hR hroot).map_pred v

theorem reflection_lca (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (hroot : R.image σ = R) (v w : E.tree R hR) :
    E.reflection R hR hroot (v ⊓ w) = E.reflection R hR hroot v ⊓ E.reflection R hR hroot w :=
  (E.reflection R hR hroot).map_inf v w

theorem reflected_pair_disjoint (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (hroot : R.image σ = R) (v : E.tree R hR) (hv : E.reflection R hR hroot v ≠ v) :
    Disjoint v.val (E.reflection R hR hroot v).val :=
  ReflectedPartitionTree.reflected_pair_disjoint σ hσ E.partitions E.partitions_mirror E.partitions_proper R hR hroot v hv

theorem tree_child_iff_partition (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (v w : E.tree R hR) : v ⋖ w ↔ 1 < v.val.card ∧ w.val ∈ (E.partitions v.val).parts :=
  ClusterPartitionTree.covBy_iff_part v w

theorem tree_child_card_lt (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (v w : E.tree R hR) (hvw : v ⋖ w) : w.val.card < v.val.card := by
  have h := (E.tree_child_iff_partition R hR v w).mp hvw
  exact E.partitions_proper v.val h.1 w.val h.2

theorem tree_leaf_iff_singleton (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (v : E.tree R hR) : IsMax v ↔ ∃ j ∈ R, v.val = {j} :=
  ClusterPartitionTree.isMax_iff_singleton v

theorem child_shape_constant (E : Extraction σ hσ p) (A B : LargeSubset I)
    (hB : B.val ∈ (E.partitions A.val).parts) :
    ∀ j : B.val, E.shapes A (inclusion A B ((E.partitions A.val).le hB) j) =
      E.shapes A (inclusion A B ((E.partitions A.val).le hB) (chosenAnchor σ hσ B)) := by
  intro j
  exact SubsetNormalizedLimits.eq_shape_of_mem_same_part E.shapes A hB _ _ j.property (chosenAnchor σ hσ B).property

/-- Actual mixed child/parent radii separate on the same subsequence as all node shapes. -/
theorem child_scale_separation (E : Extraction σ hσ p) (A B : LargeSubset I)
    (hB : B.val ∈ (E.partitions A.val).parts) :
    Tendsto (fun k => radiusOn σ hσ B (p (E.subsequence k)) / radiusOn σ hσ A (p (E.subsequence k)))
      atTop (𝓝 0) :=
  ReflectedChildLimits.radius_ratio_tendsto_zero σ hσ p E.input_mirror E.subsequence A B
    ((E.partitions A.val).le hB) (E.shapes A) (E.limits A) (E.child_shape_constant A B hB)

/-- The actual child-center offset converges to its coarse child-shape value. -/
theorem child_center_offset (E : Extraction σ hσ p) (A B : LargeSubset I)
    (hB : B.val ∈ (E.partitions A.val).parts) :
    Tendsto (fun k => (radiusOn σ hσ A (p (E.subsequence k)))⁻¹ •
      (centerOn σ hσ B (p (E.subsequence k)) - centerOn σ hσ A (p (E.subsequence k)))) atTop
        (𝓝 (E.shapes A (inclusion A B ((E.partitions A.val).le hB) (chosenAnchor σ hσ B)))) :=
  ReflectedChildLimits.center_offset_tendsto σ hσ p E.input_mirror E.subsequence A B
    ((E.partitions A.val).le hB) (E.shapes A) (E.limits A) (E.child_shape_constant A B hB)

/-- Leaf radii are zero; every nontrivial node uses its actual normalization radius. -/
def nodeRadius (E : Extraction σ hσ p) (A : Finset I) (k : ℕ) : ℝ :=
  if hA : 1 < A.card then radiusOn σ hσ ⟨A, hA⟩ (p (E.subsequence k)) else 0

/-- Every native tree edge, including an edge to a leaf, has vanishing relative scale. -/
theorem tree_child_scale_separation (E : Extraction σ hσ p) (R : Finset I) (hR : R.Nonempty)
    (v w : E.tree R hR) (hvw : v ⋖ w) :
    Tendsto (fun k => E.nodeRadius w.val k / E.nodeRadius v.val k) atTop (𝓝 0) := by
  have hv := (E.tree_child_iff_partition R hR v w).mp hvw
  by_cases hw : 1 < w.val.card
  · simpa only [nodeRadius, dif_pos hv.1, dif_pos hw] using E.child_scale_separation ⟨v.val, hv.1⟩ ⟨w.val, hw⟩ hv.2
  · simpa only [nodeRadius, dif_neg hw, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Extraction

section Compactification

variable {n m : ℕ}

/-- The reflected finite extraction is constructed for every actual compactification point. -/
def compactificationExtraction (i : Fin n) (x : Compactification i m) :
    Extraction doubledReflection doubledReflection_involutive (CompactificationClusterLimits.doubledSequence i x) :=
  extract doubledReflection doubledReflection_involutive (CompactificationClusterLimits.doubledSequence i x)
    (CompactificationClusterLimits.doubledSequence_injective i x)
    (fun k j => (normalizedSequence i x k).val.doubledPoint_reflection j)

def compactificationTree (i : Fin n) (x : Compactification i m) : RootedTree :=
  (compactificationExtraction i x).tree Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩

instance compactificationTreeFintype (i : Fin n) (x : Compactification i m) :
    Fintype (compactificationTree i x) :=
  inferInstanceAs (Fintype ((compactificationExtraction i x).tree Finset.univ _))

def compactificationReflection (i : Fin n) (x : Compactification i m) :
    compactificationTree i x ≃o compactificationTree i x :=
  (compactificationExtraction i x).reflection Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩
    (ReflectedPartitionTree.image_univ doubledReflection doubledReflection_involutive)

theorem compactificationExtraction_tendsto (i : Fin n) (x : Compactification i m) :
    Tendsto (fun k => compactificationEmbedding i
      (normalizedSequence i x ((compactificationExtraction i x).subsequence k))) atTop (𝓝 x) :=
  (tendsto_normalizedSequence i x).comp (compactificationExtraction i x).strictMono.tendsto_atTop

theorem compactificationExtraction_directions (i : Fin n) (x : Compactification i m) (v : DoubledPair n m) :
    Tendsto (fun k => complexPhase ((normalizedSequence i x
      ((compactificationExtraction i x).subsequence k)).val.pairDifference v)) atTop (𝓝 (x.val.2.1 v)) :=
  CompactificationClusterLimits.tendsto_direction_subsequence i x _ (compactificationExtraction i x).strictMono v

theorem compactificationExtraction_ratios (i : Fin n) (x : Compactification i m) (v : DoubledTriple n m) :
    Tendsto (fun k => (normalizedSequence i x
      ((compactificationExtraction i x).subsequence k)).val.tripleDistanceRatio v) atTop (𝓝 (x.val.2.2 v)) :=
  CompactificationClusterLimits.tendsto_ratio_subsequence i x _ (compactificationExtraction i x).strictMono v

end Compactification

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestExtraction
