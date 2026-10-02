import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphGraftReconstruction
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedIntegrals

/-! Explicit outgoing-slot bijections of the actual extracted graph pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphExtractedOrders
open scoped Classical
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)} {q : Fin n → ℕ}

def outerSlotEquiv (ha : a ∈ S) (hi : i ∉ S) :
    KontsevichGraph.General.Edge (pulledOuterArity q (anchoredPartitionEquiv ha hi)) ≃
      {e : KontsevichGraph.General.Edge q // e.1 ∉ S} :=
  (Equiv.sigmaCongrRight (fun v ↦ finCongr (show
      pulledOuterArity q (anchoredPartitionEquiv ha hi) v = q ((coarseSourceEquiv hi).symm v).val by
        simp only [pulledOuterArity, anchoredPartition_outer]))).trans
    ((Equiv.sigmaCongrLeft (β := fun v : {v : Fin n // v ∉ S} ↦ Fin (q v.val))
      (coarseSourceEquiv hi).symm).trans (Equiv.subtypeSigmaEquiv (fun v ↦ Fin (q v)) (fun v ↦ v ∉ S)).symm)

def innerSlotEquiv (ha : a ∈ S) (hi : i ∉ S) :
    KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi)) ≃
      {e : KontsevichGraph.General.Edge q // e.1 ∈ S} :=
  (Equiv.sigmaCongrRight (fun v ↦ finCongr (show
      pulledInnerArity q (anchoredPartitionEquiv ha hi) v = q ((shapeSourceEquiv ha).symm v).val by
        simp only [pulledInnerArity, anchoredPartition_inner]))).trans
    ((Equiv.sigmaCongrLeft (β := fun v : {v : Fin n // v ∈ S} ↦ Fin (q v.val))
      (shapeSourceEquiv ha).symm).trans (Equiv.subtypeSigmaEquiv (fun v ↦ Fin (q v)) (fun v ↦ v ∈ S)).symm)

@[simp] theorem outerSlotEquiv_source (ha : a ∈ S) (hi : i ∉ S)
    (e : KontsevichGraph.General.Edge (pulledOuterArity q (anchoredPartitionEquiv ha hi))) :
    ((outerSlotEquiv ha hi e).val).1 = ((coarseSourceEquiv hi).symm e.1).val := rfl

@[simp] theorem innerSlotEquiv_source (ha : a ∈ S) (hi : i ∉ S)
    (e : KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi))) :
    ((innerSlotEquiv ha hi e).val).1 = ((shapeSourceEquiv ha).symm e.1).val := rfl

@[simp] theorem outerSlotEquiv_slot (ha : a ∈ S) (hi : i ∉ S)
    (e : KontsevichGraph.General.Edge (pulledOuterArity q (anchoredPartitionEquiv ha hi))) :
    ((outerSlotEquiv ha hi e).val).2.val = e.2.val := rfl

@[simp] theorem innerSlotEquiv_slot (ha : a ∈ S) (hi : i ∉ S)
    (e : KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi))) :
    ((innerSlotEquiv ha hi e).val).2.val = e.2.val := rfl

theorem outerSlotEquiv_val (ha : a ∈ S) (hi : i ∉ S)
    (v : Fin (coarseN i S + 1)) (j : Fin (pulledOuterArity q (anchoredPartitionEquiv ha hi) v)) :
    (outerSlotEquiv ha hi ⟨v,j⟩).val = ⟨anchoredPartitionEquiv ha hi (Fin.castAdd (shapeN a S + 1) v),j⟩ := by
  apply Sigma.ext (anchoredPartition_outer ha hi v).symm
  apply (Fin.heq_ext_iff (congrArg q (anchoredPartition_outer ha hi v).symm)).mpr
  rfl

theorem innerSlotEquiv_val (ha : a ∈ S) (hi : i ∉ S)
    (v : Fin (shapeN a S + 1)) (j : Fin (pulledInnerArity q (anchoredPartitionEquiv ha hi) v)) :
    (innerSlotEquiv ha hi ⟨v,j⟩).val = ⟨anchoredPartitionEquiv ha hi (Fin.natAdd (coarseN i S + 1) v),j⟩ := by
  apply Sigma.ext (anchoredPartition_inner ha hi v).symm
  apply (Fin.heq_ext_iff (congrArg q (anchoredPartition_inner ha hi v).symm)).mpr
  rfl

theorem extractedOuter_target (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu)))
    (e : KontsevichGraph.General.Edge (pulledOuterArity q (anchoredPartitionEquiv ha hi))) :
    ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd).target e =
      boundaryVertex (coarsePermutation (le_of_lt hlu))
        (coarseTarget (i := i) (S := S) (l := l) (u := u) (Γ.target (outerSlotEquiv ha hi e).val)) := by
  rcases e with ⟨v,j⟩
  change graftCollapse _ ((orderedGraph Γ ha hi hlu).target _) = _
  rw [orderedGraph, Graph.reindexForGraft_target_outer, outerSlotEquiv_val]
  exact collapsedVertex_eq_coarseTarget ha hi hlu _

open BoundaryGraphValenceSelection in
/-- The original row order, restricted to outer rows and transported to the
actual extracted outer graph's outgoing slots. -/
def extractedOuterOrder (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u) :
    Fin (coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (pulledOuterArity q (anchoredPartitionEquiv ha hi)) :=
  (externalEnum (graphEdges Γ order) S hc).symm.trans
    ((order.subtypeEquiv (fun _ ↦ Iff.rfl)).trans (outerSlotEquiv ha hi).symm)

open BoundaryGraphValenceSelection in
def extractedInnerOrder (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u) :
    Fin (shapeDegree a S l u) ≃ KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi)) :=
  (internalEnum (graphEdges Γ order) S hc).symm.trans
    ((order.subtypeEquiv (fun _ ↦ Iff.rfl)).trans (innerSlotEquiv ha hi).symm)

def innerBoundaryCast (hlu : l < u) : Fin ((shapeM l u - 1) + 1) ≃ Fin (shapeM l u) :=
  finCongr (by have h := shapeM_pos hlu; omega)

def innerVertexCast (hlu : l < u) :
    KontsevichGraph.General.Vertex (shapeN a S + 1) ((shapeM l u - 1) + 1) ≃
      GraphForms.Vertex (shapeN a S) (shapeM l u) :=
  Equiv.sumCongr (Equiv.refl _) (innerBoundaryCast hlu)

theorem graftInnerVertex_orderedShapeTarget (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (v : KontsevichGraph.General.Vertex n m)
    (hv : boundaryClusterCollapses S l u (Sum.inl v)) :
    graftInnerVertex (centerSlot (le_of_lt hlu))
      ((innerVertexCast (a := a) (S := S) hlu).symm
        (boundaryVertex (shapePermutation l u) (shapeTarget (a := a) v hv))) =
      reindexedVertex ha hi hlu v := by
  cases v with
  | inl v =>
    change Sum.inl (Fin.natAdd (coarseN i S + 1) (shapeSource (a := a) v hv)) =
      Sum.inl ((anchoredPartitionEquiv ha hi).symm v)
    rw [partition_symm_inside ha hi v hv]
    rfl
  | inr v =>
    apply congrArg Sum.inr
    apply Fin.ext
    change (centerSlot (le_of_lt hlu)).val +
      ((innerBoundaryCast hlu).symm (shapePermutation l u (shapeBoundaryEnum ⟨v,hv⟩))).val =
        ((boundaryCast hlu).symm v).val
    rw [shapePermutation_native]
    change l.val + (shapeOrderedEnum l u ⟨v,hv⟩).val = v.val
    rw [shapeOrderedEnum_val (le_of_lt hlu)]
    have h := (mem_boundaryClusterBlock l u v).mp hv
    change l.val + (v.val - l.val) = v.val
    omega

theorem extractedInner_target (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (hc : (orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu)))
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (e : KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi))) :
    innerVertexCast (a := a) (S := S) hlu
      (((orderedGraph Γ ha hi hlu).extractedInner (centerSlot (le_of_lt hlu)) hc).target e) =
      boundaryVertex (shapePermutation l u)
        (shapeTarget (a := a) (Γ.target (innerSlotEquiv ha hi e).val)
          (hn _ (innerSlotEquiv ha hi e).property)) := by
  apply (innerVertexCast (a := a) (S := S) hlu).symm.injective
  rw [Equiv.symm_apply_apply]
  apply graftInnerVertex_injective (a := coarseN i S + 1) (centerSlot (le_of_lt hlu))
  rw [graftInnerVertex_orderedShapeTarget ha hi hlu]
  change graftInnerVertex _ ((orderedGraph Γ ha hi hlu).extractedInnerTarget _ hc e) = _
  rw [Graph.extractedInnerTarget_spec]
  rcases e with ⟨v,j⟩
  rw [orderedGraph, Graph.reindexForGraft_target_inner, innerSlotEquiv_val]
  rfl

@[simp] theorem outerSlotEquiv_symm_source (ha : a ∈ S) (hi : i ∉ S)
    (e : {e : KontsevichGraph.General.Edge q // e.1 ∉ S}) :
    ((outerSlotEquiv ha hi).symm e).1 = coarseSource (i := i) e.val.1 e.property := rfl

@[simp] theorem innerSlotEquiv_symm_source (ha : a ∈ S) (hi : i ∉ S)
    (e : {e : KontsevichGraph.General.Edge q // e.1 ∈ S}) :
    ((innerSlotEquiv ha hi).symm e).1 = shapeSource (a := a) e.val.1 e.property := rfl

/-- Only the proved equality of the external counts is cast; their increasing
order and every outgoing slot are retained. -/
def extractedShapeGraph (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (hc : (orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu))) :
    Graph (pulledInnerArity q (anchoredPartitionEquiv ha hi)) (shapeM l u) :=
  ((orderedGraph Γ ha hi hlu).extractedInner (centerSlot (le_of_lt hlu)) hc).reindex
    (Equiv.refl _) (innerBoundaryCast hlu).symm

open BoundaryGraphValenceSelection BoundaryGraphOrderedIntegrals

theorem extractedOuter_orderedEdges (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    GeometricWeights.orderedEdges
      ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd)
      (extractedOuterOrder Γ ha hi order hc) =
      orderedCoarseEdges (graphEdges Γ order) hc (le_of_lt hlu) := by
  funext j
  apply congrArg₂ GraphForms.Edge.mk
  · rfl
  · change ((orderedGraph Γ ha hi hlu).extractedOuter (centerSlot (le_of_lt hlu)) hd).target _ = _
    rw [extractedOuter_target]
    simp only [extractedOuterOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl

theorem extractedInner_orderedEdges (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S) (hlu : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (hc : (orderedGraph Γ ha hi hlu).InnerClosed (centerSlot (le_of_lt hlu)))
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e))) :
    GeometricWeights.orderedEdges (extractedShapeGraph Γ ha hi hlu hc)
      (extractedInnerOrder Γ ha hi order hcount) =
      orderedShapeEdges (graphEdges Γ order) hcount (fun j hj ↦ hn (order j) hj) := by
  funext j
  apply congrArg₂ GraphForms.Edge.mk
  · rfl
  · change innerVertexCast (a := a) (S := S) hlu
      (((orderedGraph Γ ha hi hlu).extractedInner (centerSlot (le_of_lt hlu)) hc).target _) = _
    rw [extractedInner_target Γ ha hi hlu hc hn]
    have hrefl (e : KontsevichGraph.General.Edge (pulledInnerArity q (anchoredPartitionEquiv ha hi))) :
        reindexEdgeEquiv _ (Equiv.refl _) e = e := by rcases e with ⟨v,j⟩; rfl
    simp only [hrefl, extractedInnerOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphExtractedOrders
