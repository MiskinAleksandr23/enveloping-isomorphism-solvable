import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeDimension
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeCoordinates

/-! The actual extracted free forest model has dimension 2*n+m-2. The count
comes from native leaves, actual reflection orbits and actual marked factors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDimension

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedForestShapeCoordinates
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

theorem root_nonleaf : ¬IsMax (⊥ : tree i x) := by
  intro h
  have hc := (ClusterPartitionTree.isMax_iff_card_eq_one
    (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) (⊥ : tree i x)).mp h
  have hl := root_large i x
  omega

/-- The actual singleton-leaf construction loses and introduces no doubled labels. -/
def leafEquiv : DoubledLabel n m ≃ {u : tree i x // IsMax u} where
  toFun j := ⟨canonicalLeaf i x j, canonicalLeaf_isMax i x j⟩
  invFun u := (selectedLabel i x u.val).val
  left_inv := selectedLabel_leaf i x
  right_inv u := by
    apply Subtype.ext
    change canonicalLeaf i x (selectedLabel i x u.val).val = u.val
    obtain ⟨j, _, hj⟩ := ((extraction i x).tree_leaf_iff_singleton Finset.univ
      ⟨Sum.inr i, Finset.mem_univ _⟩ u.val).mp u.property
    have he : u.val = canonicalLeaf i x j := Subtype.ext hj
    rw [he, selectedLabel_leaf]

theorem leaf_card : Fintype.card {u : tree i x // IsMax u} = 2 * n + m := by
  have h := Fintype.card_congr (leafEquiv i x)
  simp only [DoubledLabel, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- Integer-free counting form, retaining the two removed affine parameters. -/
theorem total_dimension_add_two : radialCount i x + circleCount i x + realCount i x + 2 = 2 * n + m := by
  have h := ForestShapeDimension.total_dimension_leaves (tree i x) (reflection i x) (reflection_reflection i x)
    (frames i x) (root_nonleaf i x) (pairedMarks i x) (fixedMarks i x)
  rw [leaf_card i x] at h
  exact h

/-- Exact dimension of the genuine free orthant/circle/real model at every x. -/
theorem total_dimension : radialCount i x + circleCount i x + realCount i x = 2 * n + m - 2 := by
  have h := total_dimension_add_two i x
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDimension
