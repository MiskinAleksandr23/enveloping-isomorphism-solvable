import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestBinaryRowSign

/-! Actual total row-sign cancellation for general arities. The parity
criterion applies in particular to a single odd vector block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestProfileRowSign
open scoped Classical BigOperators
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphCanonicalFibreMatching
open KontsevichGraph.General RealForestBinaryRowSign
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m+1)}
  (q : Fin n → ℕ) (ha : a ∈ S) (hi : i ∉ S)

def packedArity : Fin n → ℕ := profileArity q (vertexPermutation ha hi).symm

@[simp] theorem packedArity_inner (v : Fin (shapeN a S + 1)) :
    packedArity q ha hi (packedInner ha hi v) = pulledInnerArity q (anchoredPartitionEquiv ha hi) v := by
  simp [packedArity, profileArity, pulledInnerArity, anchoredPartition_inner]

@[simp] theorem packedArity_outer (v : Fin (coarseN i S + 1)) :
    packedArity q ha hi (packedOuter ha hi v) = pulledOuterArity q (anchoredPartitionEquiv ha hi) v := by
  simp [packedArity, profileArity, pulledOuterArity, anchoredPartition_outer]

theorem packed_inner_lt_inner (v w : Fin (shapeN a S + 1)) :
    packedInner ha hi v < packedInner ha hi w ↔ v < w := Iff.rfl

theorem packed_outer_lt_outer (v w : Fin (coarseN i S + 1)) :
    packedOuter ha hi v < packedOuter ha hi w ↔ v < w := by
  change (shapeN a S + 1) + v.val < (shapeN a S + 1) + w.val ↔ v.val < w.val
  omega

theorem packed_inner_lt_outer (v : Fin (shapeN a S + 1)) (w : Fin (coarseN i S + 1)) :
    packedInner ha hi v < packedOuter ha hi w := by
  change v.val < (shapeN a S + 1) + w.val
  have hv := v.isLt
  omega

def packedCoordinates : Fin (shapeN a S + 1) ⊕ Fin (coarseN i S + 1) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (vertexCount ha hi))

theorem edgePrefix_packed_inner (v : Fin (shapeN a S + 1)) :
    edgePrefix (packedArity q ha hi) (packedInner ha hi v) =
      edgePrefix (pulledInnerArity q (anchoredPartitionEquiv ha hi)) v := by
  unfold edgePrefix
  rw [← Equiv.sum_comp (packedCoordinates ha hi), Fintype.sum_sum_type]
  change (∑ w, if packedInner ha hi w < packedInner ha hi v then
    packedArity q ha hi (packedInner ha hi w) else 0) +
    (∑ w, if packedOuter ha hi w < packedInner ha hi v then
    packedArity q ha hi (packedOuter ha hi w) else 0) = _
  simp only [packed_inner_lt_inner, packedArity_inner,
    not_lt_of_gt (packed_inner_lt_outer ha hi _ _), ↓reduceIte, Finset.sum_const_zero, add_zero]

theorem edgePrefix_packed_outer (v : Fin (coarseN i S + 1)) :
    edgePrefix (packedArity q ha hi) (packedOuter ha hi v) =
      (∑ w, pulledInnerArity q (anchoredPartitionEquiv ha hi) w) +
        edgePrefix (pulledOuterArity q (anchoredPartitionEquiv ha hi)) v := by
  unfold edgePrefix
  rw [← Equiv.sum_comp (packedCoordinates ha hi), Fintype.sum_sum_type]
  change (∑ w, if packedInner ha hi w < packedOuter ha hi v then
    packedArity q ha hi (packedInner ha hi w) else 0) +
    (∑ w, if packedOuter ha hi w < packedOuter ha hi v then
    packedArity q ha hi (packedOuter ha hi w) else 0) = _
  simp only [packed_inner_lt_outer, packed_outer_lt_outer, packedArity_inner, packedArity_outer, ↓reduceIte]

variable (Γ : Graph q m)
  (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
  (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)

include order in
theorem edgeDegree : ∑ v, q v = shapeDegree a S l u + coarseDegree i S l u := by
  have h := Fintype.card_congr order
  simpa [KontsevichGraph.General.Edge] using h.symm

def rowPermutation : Equiv.Perm (Fin (shapeDegree a S l u + coarseDegree i S l u)) :=
  (finCongr (edgeDegree q order)).permCongr (profileRowPerm q (vertexPermutation ha hi).symm)

theorem rowPermutation_sign_of_even_off (v : Fin n) (hq : ∀ w, w ≠ v → Even (q w)) :
    (rowPermutation q ha hi order).sign = 1 := by
  rw [rowPermutation, Equiv.Perm.sign_permCongr]
  exact profileRowPerm_sign_eq_one_of_even_off q _ v hq

variable (horder : ∀ e : KontsevichGraph.General.Edge q,
  (order.symm e).val = edgePrefix q e.1 + e.2.val)

include horder in
theorem rowPermutation_val (j : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
    (rowPermutation q ha hi order j).val =
      edgePrefix (packedArity q ha hi) ((vertexPermutation ha hi).symm (order j).1) + (order j).2.val := by
  have hj : (finCongr (edgeDegree q order)).symm j = (vertexMajorEdgeEquiv q).symm (order j) := by
    apply Fin.ext
    have h := horder (order j)
    rw [Equiv.symm_apply_apply] at h
    change j.val = _
    rw [← Sigma.eta (order j), vertexMajorEdgeEquiv_symm_val]
    exact h
  change (profileRowPerm q (vertexPermutation ha hi).symm ((finCongr (edgeDegree q order)).symm j)).val = _
  rw [hj, profileRowPerm_edge_val]
  rfl

theorem innerRow_val (j : Fin (shapeDegree a S l u)) :
    (innerRowPermutation Γ ha hi order hc j).val =
      edgePrefix (pulledInnerArity q (anchoredPartitionEquiv ha hi))
        (extractedInnerOrder Γ ha hi order hc j).1 + (extractedInnerOrder Γ ha hi order hc j).2.val := by
  change ((vertexMajorEdgeEquiv (pulledInnerArity q (anchoredPartitionEquiv ha hi))).symm
    (extractedInnerOrder Γ ha hi order hc j)).val = _
  rw [← Sigma.eta (extractedInnerOrder Γ ha hi order hc j), vertexMajorEdgeEquiv_symm_val]

theorem outerRow_val (j : Fin (coarseDegree i S l u)) :
    (outerRowPermutation Γ ha hi order hc j).val =
      edgePrefix (pulledOuterArity q (anchoredPartitionEquiv ha hi))
        (extractedOuterOrder Γ ha hi order hc j).1 + (extractedOuterOrder Γ ha hi order hc j).2.val := by
  change ((vertexMajorEdgeEquiv (pulledOuterArity q (anchoredPartitionEquiv ha hi))).symm
    (extractedOuterOrder Γ ha hi order hc j)).val = _
  rw [← Sigma.eta (extractedOuterOrder Γ ha hi order hc j), vertexMajorEdgeEquiv_symm_val]

theorem innerSlot_extractedOrder (j : Fin (shapeDegree a S l u)) :
    (innerSlotEquiv ha hi (extractedInnerOrder Γ ha hi order hc j)).val =
      order (internalIndex (graphEdges Γ order) S hc j) := by
  simp only [extractedInnerOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem outerSlot_extractedOrder (j : Fin (coarseDegree i S l u)) :
    (outerSlotEquiv ha hi (extractedOuterOrder Γ ha hi order hc j)).val =
      order (externalIndex (graphEdges Γ order) S hc j) := by
  simp only [extractedOuterOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

include horder in
theorem edgeBlock_trans_rowPermutation :
    (edgeBlockPermutation (graphEdges Γ order) S hc).trans (rowPermutation q ha hi order) =
      finSumFinEquiv.permCongr (Equiv.sumCongr
        (innerRowPermutation Γ ha hi order hc) (outerRowPermutation Γ ha hi order hc)) := by
  apply Equiv.ext
  intro j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    simp only [Equiv.trans_apply, edgeBlockPermutation_inl, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    rw [rowPermutation_val q ha hi order horder]
    rw [← innerSlot_extractedOrder q ha hi Γ order hc,
      innerSlotEquiv_slot, innerSlotEquiv_source, ← vertexPermutation_inner ha hi,
      Equiv.symm_apply_apply, edgePrefix_packed_inner]
    change _ = (innerRowPermutation Γ ha hi order hc j).val
    rw [innerRow_val]
  | inr j =>
    simp only [Equiv.trans_apply, edgeBlockPermutation_inr, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply Fin.ext
    rw [rowPermutation_val q ha hi order horder]
    rw [← outerSlot_extractedOrder q ha hi Γ order hc,
      outerSlotEquiv_slot, outerSlotEquiv_source, ← vertexPermutation_outer ha hi,
      Equiv.symm_apply_apply, edgePrefix_packed_outer]
    change _ = shapeDegree a S l u + (outerRowPermutation Γ ha hi order hc j).val
    rw [innerDegree Γ ha hi order hc, outerRow_val]
    exact Nat.add_assoc _ _ _

include horder in
/-- Every intermediate enumeration cancels, leaving only the sign of the
actual source-profile row permutation. One exceptional odd block is allowed. -/
theorem edgeOrderingSign_eq_one_of_even_off (v : Fin n) (hq : ∀ w, w ≠ v → Even (q w)) :
    RealForestGraftSlotMatching.edgeOrderingSign Γ ha hi order hc = 1 := by
  have hs := congrArg Equiv.Perm.sign (edgeBlock_trans_rowPermutation q ha hi Γ order hc horder)
  rw [Equiv.Perm.sign_trans, rowPermutation_sign_of_even_off q ha hi order v hq,
    one_mul, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr] at hs
  unfold RealForestGraftSlotMatching.edgeOrderingSign
  rw [Equiv.Perm.sign_symm, hs]
  rcases Int.units_eq_one_or (innerRowPermutation Γ ha hi order hc).sign with hi' | hi' <;>
    rcases Int.units_eq_one_or (outerRowPermutation Γ ha hi order hc).sign with ho' | ho' <;>
    rw [hi', ho'] <;> norm_num

theorem edgeOrderingSign_eq_one_of_canonical_even_off
    (hD : shapeDegree a S l u + coarseDegree i S l u = ∑ v, q v)
    (he : order = (finCongr hD).trans (vertexMajorEdgeEquiv q))
    (v : Fin n) (hq : ∀ w, w ≠ v → Even (q w)) :
    RealForestGraftSlotMatching.edgeOrderingSign Γ ha hi order hc = 1 := by
  apply edgeOrderingSign_eq_one_of_even_off q ha hi Γ order hc _ v hq
  rintro ⟨w,j⟩
  rw [he]
  change ((vertexMajorEdgeEquiv q).symm ⟨w,j⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestProfileRowSign

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestProfileRowSign
open scoped Classical
open BoundaryGraphFaceFactorization BoundaryGraphValenceSelection
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m+1)}

/-- The single-vector profile has precisely one odd source block, regardless
of whether that block lies inside or outside the geometric real cluster. -/
theorem mixed_edgeOrderingSign_eq_one (v : Fin n)
    (Γ : Graph (oneExceptionalArity 1 v) m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (oneExceptionalArity 1 v))
    (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (horder : ∀ e : KontsevichGraph.General.Edge (oneExceptionalArity 1 v),
      (order.symm e).val = edgePrefix (oneExceptionalArity 1 v) e.1 + e.2.val) :
    RealForestGraftSlotMatching.edgeOrderingSign Γ ha hi order hc = 1 := by
  apply edgeOrderingSign_eq_one_of_even_off _ ha hi Γ order hc horder v
  intro w hw
  simp [oneExceptionalArity, hw]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestProfileRowSign
