import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceWeight
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLegPermutation
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

/-! The actual exit enumeration is identified with any fixed genuine split
template by an explicit root-slot permutation, including its geometric sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitCanonicalQuotient
open KontsevichGraph.General KontsevichGraph.General.Graph
open TwoPointSplitFaceAdmissibility TwoPointSplitFaceContraction
open scoped Classical
variable {n m p : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (v : Fin (n + 1)) (hq : q v = p) (Γ : Graph q m) (Θ : Graph qLocal p)
  (χ : Γ.VertexSplitChoices v) (L : Fin p → KontsevichGraph.General.Edge qLocal)
  (hL : ∀ e j, Θ.target e = Sum.inr j ↔ L j = e)
  (hp : Fintype.card (KontsevichGraph.General.Edge qLocal) = p + 1)
  (D : Data v (Γ.vertexSplit Θ v hq χ))

include hL in
theorem exists_original_leg (e : Exit v (Γ.vertexSplit Θ v hq χ)) : ∃ j, L j = e.val := by
  cases ht : Θ.target e.val with
  | inl c =>
    have hn := e.property
    apply False.elim
    apply hn
    change vertexSplitCollapseVertex v ((Γ.vertexSplit Θ v hq χ).target
      (vertexSplitLocalEdge q qLocal v e.val)) = _
    rw [vertexSplit_target_local, ht, vertexSplitTemplateVertex_child, vertexSplitCollapseVertex_child]
  | inr j => exact ⟨j, (hL e.val j).mp ht⟩

def slotMap (j : Fin p) : Fin p :=
  (exists_original_leg v hq Γ Θ χ L hL (legEquiv v (Γ.vertexSplit Θ v hq χ) hp D j)).choose

theorem leg_slotMap (j : Fin p) :
    L (slotMap v hq Γ Θ χ L hL hp D j) = leg v (Γ.vertexSplit Θ v hq χ) hp D j :=
  (exists_original_leg v hq Γ Θ χ L hL (legEquiv v (Γ.vertexSplit Θ v hq χ) hp D j)).choose_spec

def slotPermutation : Equiv.Perm (Fin p) := Equiv.ofBijective (slotMap v hq Γ Θ χ L hL hp D)
  ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro j k he
    apply leg_injective v (Γ.vertexSplit Θ v hq χ) hp D
    exact (leg_slotMap v hq Γ Θ χ L hL hp D j).symm.trans
      ((congrArg L he).trans (leg_slotMap v hq Γ Θ χ L hL hp D k)), rfl⟩)

theorem leg_slotPermutation (j : Fin p) :
    leg v (Γ.vertexSplit Θ v hq χ) hp D j = L (slotPermutation v hq Γ Θ χ L hL hp D j) :=
  (leg_slotMap v hq Γ Θ χ L hL hp D j).symm

/-- The extracted quotient is the actual original quotient, reordered only
in the root slots by the actual comparison of its two leg enumerations. -/
theorem quotient_eq_permuteOutgoing :
    quotient v hq (Γ.vertexSplit Θ v hq χ) hp D =
      Γ.permuteOutgoing (rootOutgoing v hq (slotPermutation v hq Γ Θ χ L hL hp D)) := by
  apply Graph.ext
  funext e
  rw [quotient_target]
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv q v hq).symm.surjective e
  rcases e with e | j
  · rw [vertexSplitOldEdgeEquiv_symm_outside, embedding_outside,
      vertexSplit_target_outside, collapse_vertexSplitOutsideTarget]
    change Γ.target e.val = Γ.target
      ⟨e.val.1,rootOutgoing v hq (slotPermutation v hq Γ Θ χ L hL hp D) e.val.1 e.val.2⟩
    rw [rootOutgoing_other v hq _ e.val.1 e.property]
    rfl
  · rw [vertexSplitOldEdgeEquiv_symm_root, embedding_root, leg_slotPermutation,
      vertexSplit_target_local, (hL _ _).mpr rfl,
      vertexSplitTemplateVertex_leg, vertexSplitCollapseVertex_old]
    change Γ.target ⟨v,Fin.cast hq.symm _⟩ = Γ.target
      ⟨v,rootOutgoing v hq (slotPermutation v hq Γ Θ χ L hL hp D) v (Fin.cast hq.symm j)⟩
    rw [rootOutgoing_root, Fin.cast_cast, Fin.cast_eq_self]

/-- The extracted template is the fixed genuine template with exactly the
inverse root-slot relabelling; internal child targets are unchanged. -/
theorem template_eq_relabelLegs :
    template v hq (Γ.vertexSplit Θ v hq χ) hp D =
      Θ.relabelLegs (slotPermutation v hq Γ Θ χ L hL hp D).symm := by
  apply Graph.ext
  funext e
  cases ht : Θ.target e with
  | inl c =>
    simp only [relabelLegs, ht, Sum.map_inl, id_eq]
    apply contractedTemplate_target_child
    rw [vertexSplit_target_local, ht, vertexSplitTemplateVertex_child]
  | inr j =>
    have he : leg v (Γ.vertexSplit Θ v hq χ) hp D
        ((slotPermutation v hq Γ Θ χ L hL hp D).symm j) = e := by
      rw [leg_slotPermutation v hq Γ Θ χ L hL hp D, Equiv.apply_symm_apply]
      exact (hL e j).mp ht
    simp only [relabelLegs, ht, Sum.map_inr]
    rw [← he, template_leg]

/-- Canonical quotient-order matching retains the exact root permutation
sign. No invariance of ordered geometric weights is assumed. -/
theorem canonicalWeight_quotient (hdegree : ∑ w, q w = GraphForms.dimension n m) :
    GeometricWeights.canonicalWeight (quotient v hq (Γ.vertexSplit Θ v hq χ) hp D) hdegree =
      permutationSign (R := ℝ) (slotPermutation v hq Γ Θ χ L hL hp D) *
        GeometricWeights.canonicalWeight Γ hdegree := by
  rw [quotient_eq_permuteOutgoing v hq Γ Θ χ L hL hp D,
    GeometricWeightOutgoing.canonicalWeight_permuteOutgoing, rootOutgoing_sign]

/-- The native face integral is the weight of the original, fixed quotient.
The comparison permutation records precisely the arbitrary extracted leg order. -/
theorem normalized_integral_original
    {i a b : Fin (n + 2)}
    (ha : a ∈ TwoPointBinaryFaceAdmissibility.cluster v)
    (hb : b ∈ TwoPointBinaryFaceAdmissibility.cluster v) (hba : b ≠ a)
    (hanchor : i ∈ TwoPointBinaryFaceAdmissibility.cluster v → a = i)
    (order : Fin (InteriorGraphFaceCoordinates.shapeDegree a b (TwoPointBinaryFaceAdmissibility.cluster v) +
      InteriorGraphFaceCoordinates.coarseDegree i a (TwoPointBinaryFaceAdmissibility.cluster v) m) ≃
      KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
    (hc : Fintype.card {j // InteriorGraphFaceCoordinates.IsInternal
      (TwoPointBinaryFaceAdmissibility.cluster v)
      (TwoPointSplitFaceAdmissibility.orderedEdges v (Γ.vertexSplit Θ v hq χ) order j)} =
      InteriorGraphFaceCoordinates.shapeDegree a b (TwoPointBinaryFaceAdmissibility.cluster v)) :
    TwoPointSplitFaceWeight.normalizedIntegral v (Γ.vertexSplit Θ v hq χ) order =
      (GeometricWeights.outgoingFactor (vertexSplitArity q qLocal v) /
        GeometricWeights.outgoingFactor q) *
      TwoPointSplitFaceWeight.faceSign v hq (Γ.vertexSplit Θ v hq χ) hp D ha hanchor order hc *
      permutationSign (R := ℝ) (slotPermutation v hq Γ Θ χ L hL hp D) *
      GeometricWeights.canonicalWeight Γ
        (TwoPointSplitFaceWeight.quotient_edgeCount
          (TwoPointSplitFaceWeight.inducedOrder v hq (Γ.vertexSplit Θ v hq χ) hp D ha hanchor order hc)) := by
  rw [TwoPointSplitFaceWeight.normalized_integral_eq_signed_canonical
    v hq (Γ.vertexSplit Θ v hq χ) hp D ha hanchor order hc hb hba,
    canonicalWeight_quotient v hq Γ Θ χ L hL hp D]
  unfold TwoPointSplitFaceWeight.faceSign
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitCanonicalQuotient
