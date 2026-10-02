import EnvelopingIsomorphism.Deformation.GeneralGraphReindexing
import EnvelopingIsomorphism.Deformation.GraphGraftFibreCoefficients
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomains
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphAdmissibility

/-! Original real-boundary cluster graphs reconstruct as genuine grafts after
the explicit anchor-preserving internal relabelling. The external block keeps
its original increasing order and collapses at its original left endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphGraftReconstruction
open scoped BigOperators Classical
open BoundaryGraphFaceFactorization
open BoundaryGraphOrderedCoordinates
  (anchoredPartitionEquiv anchoredPartition_outer anchoredPartition_inner
    shapeSourceEquiv coarseSourceEquiv centerSlot centerSlot_val shapeM_eq_sub shapeM_pos
    coarsePermutation coarsePermutation_center coarsePermutation_outside boundaryVertex
    outsideOrderedEnum outsideOrderedEnum_val)
open KontsevichGraph.General

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

abbrev boundaryCast (hlu : l < u) := BoundaryGraphOrderedCoordinates.graftBoundaryEquiv hlu

@[simp] theorem boundaryCast_symm_val (hlu : l < u) (j : Fin m) :
    ((boundaryCast hlu).symm j).val = j.val := rfl

theorem partition_symm_inside (ha : a ∈ S) (hi : i ∉ S) (v : Fin n) (hv : v ∈ S) :
    (anchoredPartitionEquiv ha hi).symm v =
      Fin.natAdd (coarseN i S + 1) (shapeSourceEquiv ha ⟨v, hv⟩) := by
  apply (anchoredPartitionEquiv ha hi).injective
  simp only [Equiv.apply_symm_apply, anchoredPartition_inner, Equiv.symm_apply_apply]

theorem partition_symm_outside (ha : a ∈ S) (hi : i ∉ S) (v : Fin n) (hv : v ∉ S) :
    (anchoredPartitionEquiv ha hi).symm v =
      Fin.castAdd (shapeN a S + 1) (coarseSourceEquiv hi ⟨v, hv⟩) := by
  apply (anchoredPartitionEquiv ha hi).injective
  simp only [Equiv.apply_symm_apply, anchoredPartition_outer, Equiv.symm_apply_apply]

def reindexedVertex (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u) :
    KontsevichGraph.General.Vertex n m ≃
      KontsevichGraph.General.Vertex ((coarseN i S + 1) + (shapeN a S + 1))
        (outsideM l u + (shapeM l u - 1) + 1) :=
  Equiv.sumCongr (anchoredPartitionEquiv ha hi).symm (boundaryCast hlu).symm

def collapsedVertex (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : KontsevichGraph.General.Vertex n m) :
    KontsevichGraph.General.Vertex (coarseN i S + 1) (outsideM l u + 1) :=
  graftCollapse (a := coarseN i S + 1) (b := shapeN a S + 1) (l := shapeM l u - 1)
    (centerSlot (le_of_lt hlu)) (reindexedVertex ha hi hlu v)

theorem collapsedVertex_internal_inside (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : Fin n) (hv : v ∈ S) :
    collapsedVertex ha hi hlu (Sum.inl v) = Sum.inr (centerSlot (le_of_lt hlu)) := by
  change graftCollapse (centerSlot (le_of_lt hlu))
    (Sum.inl ((anchoredPartitionEquiv ha hi).symm v)) = _
  rw [partition_symm_inside ha hi v hv]
  simp [graftCollapse]

theorem collapsedVertex_internal_outside (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : Fin n) (hv : v ∉ S) :
    collapsedVertex ha hi hlu (Sum.inl v) = Sum.inl (coarseSource (i := i) v hv) := by
  change graftCollapse (centerSlot (le_of_lt hlu))
    (Sum.inl ((anchoredPartitionEquiv ha hi).symm v)) = _
  rw [partition_symm_outside ha hi v hv]
  simp [graftCollapse, coarseSourceEquiv]

theorem collapsedVertex_external_inside (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : Fin m) (hv : v ∈ boundaryClusterBlock l u) :
    collapsedVertex ha hi hlu (Sum.inr v) = Sum.inr (centerSlot (le_of_lt hlu)) := by
  change Sum.inr (graftBoundaryCollapse (centerSlot (le_of_lt hlu)) ((boundaryCast hlu).symm v)) = _
  apply congrArg Sum.inr
  apply Fin.ext
  have hv' := (mem_boundaryClusterBlock l u v).mp hv
  have ht := shapeM_eq_sub (le_of_lt hlu)
  have htpos := shapeM_pos hlu
  simp only [graftBoundaryCollapse, boundaryCast_symm_val, centerSlot_val]
  split_ifs <;> omega

theorem collapsedVertex_external_outside (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : Fin m) (hv : v ∉ boundaryClusterBlock l u) :
    collapsedVertex ha hi hlu (Sum.inr v) =
      Sum.inr ((centerSlot (le_of_lt hlu)).succAbove (outsideOrderedEnum l u ⟨v, hv⟩)) := by
  change Sum.inr (graftBoundaryCollapse (centerSlot (le_of_lt hlu)) ((boundaryCast hlu).symm v)) = _
  apply congrArg Sum.inr
  apply Fin.ext
  have hv' : ¬ (l.val ≤ v.val ∧ v.val < u.val) := by simpa only [mem_boundaryClusterBlock] using hv
  have ht := shapeM_eq_sub (le_of_lt hlu)
  have htpos := shapeM_pos hlu
  have hl : l.val < u.val := hlu
  simp only [graftBoundaryCollapse, boundaryCast_symm_val, centerSlot_val,
    Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    outsideOrderedEnum_val (le_of_lt hlu)]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ, outsideOrderedEnum_val (le_of_lt hlu)] at * <;> split_ifs at * <;> omega

/-- The genuine graft collapse is exactly the geometry's old quotient map
followed by its explicit order-restoring boundary permutation. -/
theorem collapsedVertex_eq_coarseTarget (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : KontsevichGraph.General.Vertex n m) :
    collapsedVertex ha hi hlu v =
      boundaryVertex (coarsePermutation (le_of_lt hlu))
        (coarseTarget (i := i) (S := S) (l := l) (u := u) v) := by
  cases v with
  | inl v =>
    by_cases hv : v ∈ S
    · rw [collapsedVertex_internal_inside ha hi hlu v hv]
      simp only [coarseTarget, dif_pos hv, boundaryVertex, Equiv.sumCongr_apply,
        Sum.map_inr, coarsePermutation_center]
    · rw [collapsedVertex_internal_outside ha hi hlu v hv]
      simp only [coarseTarget, dif_neg hv, boundaryVertex, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.refl_apply]
  | inr v =>
    by_cases hv : v ∈ boundaryClusterBlock l u
    · rw [collapsedVertex_external_inside ha hi hlu v hv]
      simp only [coarseTarget, dif_pos hv, boundaryVertex, Equiv.sumCongr_apply,
        Sum.map_inr, coarsePermutation_center]
    · rw [collapsedVertex_external_outside ha hi hlu v hv]
      simp only [coarseTarget, dif_neg hv, boundaryVertex, Equiv.sumCongr_apply,
        Sum.map_inr, coarsePermutation_outside]

theorem collapsedVertex_of_mask (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : KontsevichGraph.General.Vertex n m)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) :
    collapsedVertex ha hi hlu v = Sum.inr (centerSlot (le_of_lt hlu)) := by
  cases v with
  | inl v => exact collapsedVertex_internal_inside ha hi hlu v hv
  | inr v => exact collapsedVertex_external_inside ha hi hlu v hv

variable {q : Fin n → ℕ}

/-- The original graph expressed in the actual ordered boundary graft labels. -/
def orderedGraph (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u) :=
  Γ.reindexForGraft (anchoredPartitionEquiv ha hi) (boundaryCast hlu)

theorem orderedGraph_innerClosed (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S →
      boundaryClusterCollapses S l u (Sum.inl (Γ.target e))) :
    (orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu)) := by
  rintro ⟨v,j⟩
  apply (graftCollapse_eq_slot_iff _ _).mp
  rw [orderedGraph, Graph.reindexForGraft_target_inner]
  apply collapsedVertex_of_mask ha hi hlu
  apply hn
  change anchoredPartitionEquiv ha hi (Fin.natAdd (coarseN i S + 1) v) ∈ S
  rw [anchoredPartition_inner]
  exact ((shapeSourceEquiv ha).symm v).property

theorem orderedGraph_coarseDistinct (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (hd : ∀ v : Fin n, v ∉ S → Function.Injective
      (fun j : Fin (q v) ↦ coarseTarget (i := i) (S := S) (l := l) (u := u) (Γ.target ⟨v,j⟩))) :
    (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)) := by
  intro v j t he
  dsimp only [orderedGraph] at he
  simp only [Graph.reindexForGraft_target_outer] at he
  change collapsedVertex ha hi hlu (Γ.target _) = collapsedVertex ha hi hlu (Γ.target _) at he
  rw [collapsedVertex_eq_coarseTarget, collapsedVertex_eq_coarseTarget] at he
  apply hd (anchoredPartitionEquiv ha hi (Fin.castAdd (shapeN a S + 1) v))
  · rw [anchoredPartition_outer]
    exact ((coarseSourceEquiv hi).symm v).property
  · exact (boundaryVertex (coarsePermutation (le_of_lt hlu))).injective he

/-- Both hypotheses needed by finite graft extraction follow from the actual
nonzero face density. No graph matching identity is assumed. -/
theorem orderedGraph_admissible_of_nonzero
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (BoundaryGraphValenceSelection.graphEdges Γ order) y ≠ 0) :
    (orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu)) ∧
      (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)) :=
  ⟨orderedGraph_innerClosed Γ ha hi hlu
    (BoundaryGraphAdmissibility.graph_noOutgoing_of_nativeFaceDensity_ne_zero Γ order y hy hne),
   orderedGraph_coarseDistinct Γ ha hi hlu
    (BoundaryGraphAdmissibility.graph_coarseTarget_injective_of_nativeFaceDensity_ne_zero Γ order y hy hne)⟩

/-- Exact reconstruction at the original external left endpoint, including the
incoming-edge assignment, on every face with nonzero actual density. -/
theorem orderedGraph_reconstruction_of_nonzero
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (BoundaryGraphValenceSelection.graphEdges Γ order) y ≠ 0) :
    let H := orderedGraph Γ ha hi hlu
    let h := orderedGraph_admissible_of_nonzero Γ ha hi hlu order y hy hne
    (H.extractedOuter (centerSlot (le_of_lt hlu)) h.2).graft
      (H.extractedInner (centerSlot (le_of_lt hlu)) h.1) (centerSlot (le_of_lt hlu))
      (H.extractedChoices (centerSlot (le_of_lt hlu)) h.2) = H := by
  exact Graph.graft_extracted _ _ _ _

/-- The graft coefficient at an actual nonzero real face is the product of
its uniquely extracted graph coefficients; incoming choices contribute no
unaccounted multiplicity. -/
theorem orderedGraph_graftCoefficient_of_nonzero
    {k : Type*} [CommRing k]
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (BoundaryGraphValenceSelection.graphEdges Γ order) y ≠ 0)
    (w : Graph (pulledOuterArity q (anchoredPartitionEquiv ha hi)) (outsideM l u + 1) → k)
    (v : Graph (pulledInnerArity q (anchoredPartitionEquiv ha hi)) ((shapeM l u - 1) + 1) → k) :
    let H := orderedGraph Γ ha hi hlu
    let h := orderedGraph_admissible_of_nonzero Γ ha hi hlu order y hy hne
    GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu)) w v H =
      w (H.extractedOuter (centerSlot (le_of_lt hlu)) h.2) *
        v (H.extractedInner (centerSlot (le_of_lt hlu)) h.1) := by
  exact GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct _ _ _ _ _ _

/-- An inadmissible graft fibre has zero actual face density throughout the
physical open face, by the contrapositive of geometric extraction. -/
theorem nativeFaceDensity_zero_of_orderedGraph_not_admissible
    (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hbad : ¬ ((orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu)) ∧
      (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))))
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    nativeFaceDensity (l := l) (u := u) (BoundaryGraphValenceSelection.graphEdges Γ order) y = 0 := by
  by_contra hne
  exact hbad (orderedGraph_admissible_of_nonzero Γ ha hi hlu order y hy hne)

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphGraftReconstruction
