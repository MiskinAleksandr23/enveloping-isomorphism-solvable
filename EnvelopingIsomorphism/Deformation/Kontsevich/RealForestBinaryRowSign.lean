import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestGraftSlotMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.BlockPermutationSign

/-! Cancellation of all intermediate row enumerations for a source-major
binary graph. Only permutations of entire two-row source blocks remain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestBinaryRowSign
open scoped Classical BigOperators
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphCanonicalFibreMatching
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def innerOuterVertices (ha : a ∈ S) (hi : i ∉ S) :
    Fin (shapeN a S + 1) ⊕ Fin (coarseN i S + 1) ≃ Fin n :=
  (Equiv.sumCongr (shapeSourceEquiv ha).symm (coarseSourceEquiv hi).symm).trans
    (Equiv.sumCompl (fun v : Fin n ↦ v ∈ S))

theorem vertexCount (ha : a ∈ S) (hi : i ∉ S) :
    (shapeN a S + 1) + (coarseN i S + 1) = n := by
  simpa using Fintype.card_congr (innerOuterVertices ha hi)

def vertexPermutation (ha : a ∈ S) (hi : i ∉ S) : Equiv.Perm (Fin n) :=
  (finCongr (vertexCount ha hi).symm).trans
    (finSumFinEquiv.symm.trans (innerOuterVertices ha hi))

def packedInner (ha : a ∈ S) (hi : i ∉ S) (v : Fin (shapeN a S + 1)) : Fin n :=
  finCongr (vertexCount ha hi) (finSumFinEquiv (.inl v))

def packedOuter (ha : a ∈ S) (hi : i ∉ S) (v : Fin (coarseN i S + 1)) : Fin n :=
  finCongr (vertexCount ha hi) (finSumFinEquiv (.inr v))

@[simp] theorem vertexPermutation_inner (ha : a ∈ S) (hi : i ∉ S) (v : Fin (shapeN a S + 1)) :
    vertexPermutation ha hi (packedInner ha hi v) = ((shapeSourceEquiv ha).symm v).val := by
  simp [vertexPermutation, packedInner, innerOuterVertices]

@[simp] theorem vertexPermutation_outer (ha : a ∈ S) (hi : i ∉ S) (v : Fin (coarseN i S + 1)) :
    vertexPermutation ha hi (packedOuter ha hi v) = ((coarseSourceEquiv hi).symm v).val := by
  simp [vertexPermutation, packedOuter, innerOuterVertices]

variable (Γ : Graph (fun _ : Fin n ↦ 2) m) (ha : a ∈ S) (hi : i ∉ S)
  (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin n ↦ 2))
  (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)

def pairedPermutation : Equiv.Perm (Fin (shapeDegree a S l u + coarseDegree i S l u)) :=
  (order.trans (Equiv.sigmaEquivProd (Fin n) (Fin 2))).symm.permCongr
    (Equiv.prodCongr (vertexPermutation ha hi) (Equiv.refl (Fin 2)))

theorem pairedPermutation_sign : (pairedPermutation ha hi order).sign = 1 := by
  rw [pairedPermutation, Equiv.Perm.sign_permCongr]
  have he : Equiv.prodCongr (vertexPermutation ha hi) (Equiv.refl (Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 ↦ vertexPermutation ha hi) := by ext j <;> rfl
  rw [he, Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]
  exact Int.units_mul_self _

theorem order_pairedPermutation (j : Fin (shapeDegree a S l u + coarseDegree i S l u)) :
    order (pairedPermutation ha hi order j) =
      ⟨vertexPermutation ha hi (order j).1, (order j).2⟩ := by
  simp [pairedPermutation, Equiv.permCongr_def]

include Γ ha hi order hc in
theorem shapeDegree_binary : shapeDegree a S l u = (shapeN a S + 1) * 2 := by
  have h := innerDegree Γ ha hi order hc
  simpa [pulledInnerArity, GraphForms.dimension, shapeDegree] using h.symm

include Γ ha hi order hc in
theorem coarseDegree_binary : coarseDegree i S l u = (coarseN i S + 1) * 2 := by
  have h := outerDegree Γ ha hi order hc
  simpa [pulledOuterArity, GraphForms.dimension, coarseDegree] using h.symm

theorem innerCanonical_symm_val
    (e : KontsevichGraph.General.Edge (pulledInnerArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    ((GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hc)).symm e).val =
      2 * e.1.val + e.2.val := by
  change ((vertexMajorEdgeEquiv (fun _ : Fin (shapeN a S + 1) ↦ 2)).symm e).val = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

theorem outerCanonical_symm_val
    (e : KontsevichGraph.General.Edge (pulledOuterArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    ((GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hc)).symm e).val =
      2 * e.1.val + e.2.val := by
  change ((vertexMajorEdgeEquiv (fun _ : Fin (coarseN i S + 1) ↦ 2)).symm e).val = _
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

variable (horder : ∀ e : KontsevichGraph.General.Edge (fun _ : Fin n ↦ 2),
  (order.symm e).val = 2 * e.1.val + e.2.val)
include horder

theorem order_innerCanonical
    (e : KontsevichGraph.General.Edge (pulledInnerArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    order (finSumFinEquiv (.inl ((GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hc)).symm e))) =
      ⟨packedInner ha hi e.1, e.2⟩ := by
  apply order.symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change ((GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hc)).symm e).val = _
  rw [innerCanonical_symm_val Γ ha hi order hc, horder]
  rfl

theorem order_outerCanonical
    (e : KontsevichGraph.General.Edge (pulledOuterArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    order (finSumFinEquiv (.inr ((GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hc)).symm e))) =
      ⟨packedOuter ha hi e.1, e.2⟩ := by
  apply order.symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change shapeDegree a S l u +
    ((GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hc)).symm e).val = _
  rw [outerCanonical_symm_val Γ ha hi order hc, horder, shapeDegree_binary Γ ha hi order hc]
  change (shapeN a S + 1) * 2 + (2 * e.1.val + e.2.val) =
    2 * ((shapeN a S + 1) + e.1.val) + e.2.val
  omega

theorem paired_innerCanonical
    (e : KontsevichGraph.General.Edge (pulledInnerArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    order (pairedPermutation ha hi order
      (finSumFinEquiv (.inl ((GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hc)).symm e)))) =
      (innerSlotEquiv ha hi e).val := by
  rw [order_pairedPermutation, order_innerCanonical Γ ha hi order hc horder]
  rw [vertexPermutation_inner]
  rfl

theorem paired_outerCanonical
    (e : KontsevichGraph.General.Edge (pulledOuterArity (fun _ : Fin n ↦ 2) (anchoredPartitionEquiv ha hi))) :
    order (pairedPermutation ha hi order
      (finSumFinEquiv (.inr ((GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hc)).symm e)))) =
      (outerSlotEquiv ha hi e).val := by
  rw [order_pairedPermutation, order_outerCanonical Γ ha hi order hc horder]
  rw [vertexPermutation_outer]
  rfl

omit horder in
theorem innerSlot_extractedOrder (j : Fin (shapeDegree a S l u)) :
    (innerSlotEquiv ha hi (extractedInnerOrder Γ ha hi order hc j)).val =
      order (internalIndex (graphEdges Γ order) S hc j) := by
  simp only [extractedInnerOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

omit horder in
theorem outerSlot_extractedOrder (j : Fin (coarseDegree i S l u)) :
    (outerSlotEquiv ha hi (extractedOuterOrder Γ ha hi order hc j)).val =
      order (externalIndex (graphEdges Γ order) S hc j) := by
  simp only [extractedOuterOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem edgeBlock_eq_rows_paired :
    edgeBlockPermutation (graphEdges Γ order) S hc =
      (finSumFinEquiv.permCongr (Equiv.sumCongr
        (innerRowPermutation Γ ha hi order hc) (outerRowPermutation Γ ha hi order hc))).trans
        (pairedPermutation ha hi order) := by
  apply Equiv.ext
  intro j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    apply order.injective
    rw [edgeBlockPermutation_inl]
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change order (internalIndex _ S hc j) = order (pairedPermutation ha hi order
      (finSumFinEquiv (.inl (innerRowPermutation Γ ha hi order hc j))))
    change _ = order (pairedPermutation ha hi order (finSumFinEquiv (.inl
      ((GeometricWeights.canonicalOrder (innerDegree Γ ha hi order hc)).symm
        (extractedInnerOrder Γ ha hi order hc j)))))
    rw [paired_innerCanonical Γ ha hi order hc horder, innerSlot_extractedOrder]
  | inr j =>
    apply order.injective
    rw [edgeBlockPermutation_inr]
    simp only [Equiv.trans_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change order (externalIndex _ S hc j) = order (pairedPermutation ha hi order
      (finSumFinEquiv (.inr (outerRowPermutation Γ ha hi order hc j))))
    change _ = order (pairedPermutation ha hi order (finSumFinEquiv (.inr
      ((GeometricWeights.canonicalOrder (outerDegree Γ ha hi order hc)).symm
        (extractedOuterOrder Γ ha hi order hc j)))))
    rw [paired_outerCanonical Γ ha hi order hc horder, outerSlot_extractedOrder]

/-- The intermediate arbitrary enumerations cancel. The remaining true
source-major permutation moves whole binary source blocks and is even. -/
theorem edgeOrderingSign_eq_one :
    RealForestGraftSlotMatching.edgeOrderingSign Γ ha hi order hc = 1 := by
  have hs := congrArg Equiv.Perm.sign (edgeBlock_eq_rows_paired Γ ha hi order hc horder)
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    pairedPermutation_sign, one_mul] at hs
  unfold RealForestGraftSlotMatching.edgeOrderingSign
  rw [Equiv.Perm.sign_symm, hs]
  rcases Int.units_eq_one_or (innerRowPermutation Γ ha hi order hc).sign with hi' | hi' <;>
    rcases Int.units_eq_one_or (outerRowPermutation Γ ha hi order hc).sign with ho' | ho' <;>
    rw [hi', ho'] <;> norm_num

omit horder in
/-- The source-major hypothesis is automatic for the existing canonical
vertex-major edge order, with any proof of the native dimension equality. -/
theorem edgeOrderingSign_eq_one_of_canonical
    (hD : shapeDegree a S l u + coarseDegree i S l u = ∑ _ : Fin n, 2)
    (he : order = (finCongr hD).trans (vertexMajorEdgeEquiv (fun _ : Fin n ↦ 2))) :
    RealForestGraftSlotMatching.edgeOrderingSign Γ ha hi order hc = 1 := by
  apply edgeOrderingSign_eq_one Γ ha hi order hc
  rintro ⟨v,k⟩
  rw [he]
  change ((vertexMajorEdgeEquiv (fun _ : Fin n ↦ 2)).symm ⟨v,k⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestBinaryRowSign
