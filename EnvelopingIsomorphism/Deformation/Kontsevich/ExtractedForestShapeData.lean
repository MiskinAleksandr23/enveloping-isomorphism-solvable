import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChildShapes
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveScaleAdmissibility

/-! All finite shape inequalities are produced from an actual compactification point. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChildShapes

open Configuration ReflectedForestExtraction ComplexConjugate
open scoped Classical

variable {n m : ℕ}

/-- The actual singleton leaf of every original doubled label. -/
def canonicalLeaf (i : Fin n) (x : Compactification i m) (v : DoubledLabel n m) : compactificationTree i x :=
  ⟨{v}, ClusterPartitionTree.singleton_mem_clusters (compactificationExtraction i x).partitions
    (compactificationExtraction i x).partitions_proper Finset.univ v (Finset.mem_univ _)⟩

@[simp] theorem canonicalLeaf_label (i : Fin n) (x : Compactification i m) (v : DoubledLabel n m) :
    (canonicalLeaf i x v).val = {v} := rfl

theorem canonicalLeaf_injective (i : Fin n) (x : Compactification i m) : Function.Injective (canonicalLeaf i x) := by
  intro v w h
  have he : ({v} : Finset (DoubledLabel n m)) = {w} :=
    congrArg (fun z : compactificationTree i x => z.val) h
  exact Finset.singleton_injective he

theorem canonicalLeaf_isMax (i : Fin n) (x : Compactification i m) (v : DoubledLabel n m) :
    IsMax (canonicalLeaf i x v) :=
  ((compactificationExtraction i x).tree_leaf_iff_singleton Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ (canonicalLeaf i x v)).mpr ⟨v, Finset.mem_univ _, rfl⟩

@[simp] theorem le_canonicalLeaf_iff (i : Fin n) (x : Compactification i m)
    (c : compactificationTree i x) (v : DoubledLabel n m) :
    c ≤ canonicalLeaf i x v ↔ v ∈ c.val := Finset.singleton_subset_iff

theorem canonicalLeaf_reflect (i : Fin n) (x : Compactification i m) (v : DoubledLabel n m) :
    compactificationReflection i x (canonicalLeaf i x v) = canonicalLeaf i x (doubledReflection v) := by
  apply Subtype.ext
  change ({v} : Finset (DoubledLabel n m)).image doubledReflection = {doubledReflection v}
  exact Finset.image_singleton (doubledReflection (n := n) (m := m)) v

/-- The previously constructed representative-independent increments, on the actual extracted tree. -/
def canonicalIncrement (i : Fin n) (x : Compactification i m) : compactificationTree i x → ℂ :=
  increment (compactificationExtraction i x) Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩

theorem canonicalIncrement_reflect (i : Fin n) (x : Compactification i m) (v : compactificationTree i x) :
    canonicalIncrement i x (compactificationReflection i x v) = conj (canonicalIncrement i x v) :=
  increment_reflect (compactificationExtraction i x) Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩
    (ReflectedPartitionTree.image_univ doubledReflection doubledReflection_involutive) v

theorem canonicalIncrement_siblings_distinct (i : Fin n) (x : Compactification i m)
    (c d e : compactificationTree i x) (hd : c ⋖ d) (he : c ⋖ e) (hne : d ≠ e) :
    canonicalIncrement i x d ≠ canonicalIncrement i x e :=
  siblings_distinct (compactificationExtraction i x) Finset.univ ⟨Sum.inr i, Finset.mem_univ _⟩ c d e hd he hne

/-- The upper/mirror gap is strictly positive, derived from the original upper-half-plane points. -/
theorem canonical_upper_gap (i : Fin n) (x : Compactification i m) (j : Fin n)
    (d e : compactificationTree i x)
    (hd : (canonicalLeaf i x (Sum.inl (Sum.inl j)) ⊓ canonicalLeaf i x (Sum.inr j)) ⋖ d)
    (hdu : d ≤ canonicalLeaf i x (Sum.inl (Sum.inl j)))
    (he : (canonicalLeaf i x (Sum.inl (Sum.inl j)) ⊓ canonicalLeaf i x (Sum.inr j)) ⋖ e)
    (hel : e ≤ canonicalLeaf i x (Sum.inr j)) :
    0 < (canonicalIncrement i x d - canonicalIncrement i x e).im := by
  have hne : d ≠ e := ForestInsertionDifference.distinct_lca_children (compactificationTree i x) hd hdu he hel
  exact increment_sub_im_pos_of_original (compactificationExtraction i x) Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ _ d e hd he hne
    (Sum.inl (Sum.inl j)) (Sum.inr j)
    ((le_canonicalLeaf_iff i x d _).mp hdu) ((le_canonicalLeaf_iff i x e _).mp hel)
    (fun r => ExtractedForestShapeLimits.doubledSequence_upper_sub_conjugate_re i x r j)
    (fun r => (ExtractedForestShapeLimits.doubledSequence_upper_sub_conjugate_im_pos i x r j).le)

/-- The boundary gap is strictly positive, derived from the original ordered real boundary labels. -/
theorem canonical_boundary_gap (i : Fin n) (x : Compactification i m) (j k : Fin m) (hjk : j < k)
    (d e : compactificationTree i x)
    (hd : (canonicalLeaf i x (Sum.inl (Sum.inr k)) ⊓ canonicalLeaf i x (Sum.inl (Sum.inr j))) ⋖ d)
    (hdk : d ≤ canonicalLeaf i x (Sum.inl (Sum.inr k)))
    (he : (canonicalLeaf i x (Sum.inl (Sum.inr k)) ⊓ canonicalLeaf i x (Sum.inl (Sum.inr j))) ⋖ e)
    (hej : e ≤ canonicalLeaf i x (Sum.inl (Sum.inr j))) :
    0 < (canonicalIncrement i x d - canonicalIncrement i x e).re := by
  have hne : d ≠ e := ForestInsertionDifference.distinct_lca_children (compactificationTree i x) hd hdk he hej
  exact increment_sub_re_pos_of_original (compactificationExtraction i x) Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ _ d e hd he hne
    (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr j))
    ((le_canonicalLeaf_iff i x d _).mp hdk) ((le_canonicalLeaf_iff i x e _).mp hej)
    (fun r => ExtractedForestShapeLimits.doubledSequence_boundary_sub_im i x r j k)
    (fun r => (ExtractedForestShapeLimits.doubledSequence_boundary_sub_re_pos i x r j k hjk).le)

/-- All inputs of positive-scale admissibility are actual consequences of the extracted point. -/
def shapeData (i : Fin n) (x : Compactification i m) :
    ForestPositiveScale.ShapeData (compactificationTree i x) n m where
  leaf := canonicalLeaf i x
  leaf_injective := canonicalLeaf_injective i x
  leaf_max := canonicalLeaf_isMax i x
  reflection := compactificationReflection i x
  reflection_involutive :=
    (compactificationExtraction i x).reflection_involutive Finset.univ
      ⟨Sum.inr i, Finset.mem_univ _⟩
      (ReflectedPartitionTree.image_univ doubledReflection doubledReflection_involutive)
  leaf_reflect := canonicalLeaf_reflect i x
  increment := canonicalIncrement i x
  increment_reflect := canonicalIncrement_reflect i x
  siblings_distinct := canonicalIncrement_siblings_distinct i x
  upper_gap := canonical_upper_gap i x
  boundary_gap := canonical_boundary_gap i x

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChildShapes
