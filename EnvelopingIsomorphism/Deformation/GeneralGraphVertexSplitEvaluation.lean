import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLabels
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitTensors
import EnvelopingIsomorphism.Deformation.GeneralGraphInsertion

/-! Actual derivative and tensor evaluation after an internal vertex is split. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

open scoped BigOperators

variable {R : Type*} [CommRing R] {n m p d : ℕ}
  {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
  (Γ : Graph q m) (Θ : Graph qLocal p) (r : Fin (n + 1)) (hq : q r = p)
  (legEdge : Fin p → Edge qLocal) (hleg : ∀ j, Θ.target (legEdge j) = Sum.inr j)
  (hcomplete : ∀ e j, Θ.target e = Sum.inr j → e = legEdge j)

/-- Read the whole old label family from the actual embedding of all old edges. -/
def vertexSplitInheritedLabel (lab : Edge (vertexSplitArity q qLocal r) → Fin d) : Edge q → Fin d :=
  fun e ↦ lab (Θ.vertexSplitOldEdge legEdge hleg q r hq e)

theorem vertexSplitInheritedLabel_outside
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d)
    (v : Fin (n + 1)) (hv : v ≠ r) (j : Fin (q v)) :
    vertexSplitInheritedLabel Θ r hq legEdge hleg lab ⟨v, j⟩ =
      lab (vertexSplitOutsideEdge q qLocal r ⟨⟨v, j⟩, hv⟩) :=
  congrArg lab (Θ.vertexSplitOldEdge_outside legEdge hleg ⟨⟨v, j⟩, hv⟩)

include hcomplete in
/-- Every incoming derivative at an unchanged vertex is inherited from the old graph. -/
theorem vertexDerivative_vertexSplit_old (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d)
    (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    (Γ.vertexSplit Θ r hq χ).vertexDerivative (R := R) lab (vertexSplitOldVertex r v) =
      Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab) v := by
  rw [vertexDerivative,
    incoming_vertexSplit_old_map Θ legEdge hleg Γ r hq hcomplete χ v hv,
    iteratedPDeriv_finset_map]
  rfl

/-- A child receives the assigned old incoming derivatives after its own template derivatives. -/
theorem vertexDerivative_vertexSplit_child (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) (c : Fin 2) :
    (Γ.vertexSplit Θ r hq χ).vertexDerivative (R := R) lab (Sum.inl (vertexSplitChild r c)) =
      (iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map
        (vertexSplitLabelEquiv q qLocal r d lab).1)).comp
        (Θ.vertexDerivative (vertexSplitLabelEquiv q qLocal r d lab).2 (Sum.inl c)) := by
  rw [vertexDerivative, incoming_vertexSplit_child,
    iteratedPDeriv_finset_union _ _ (incoming_vertexSplit_child_disjoint Γ Θ r χ c),
    iteratedPDeriv_finset_map, iteratedPDeriv_finset_map]
  rfl

/-- The actual polynomial contributed by a child, including both incoming edge families. -/
def vertexSplitChildFactor (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (c : Fin 2) : Polynomial d R :=
  iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map
    (vertexSplitLabelEquiv q qLocal r d lab).1)
    (Θ.vertexDerivative (vertexSplitLabelEquiv q qLocal r d lab).2 (Sum.inl c)
      (U c (fun j ↦ (vertexSplitLabelEquiv q qLocal r d lab).2 ⟨c, j⟩)))

include hcomplete in
/-- Reindexing the genuine source partition separates the unchanged tensors and the children. -/
theorem vertexSplit_internal_product (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d)
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) :
    (∏ v : Fin (n + 2), (Γ.vertexSplit Θ r hq χ).vertexDerivative lab (Sum.inl v)
      (vertexSplitTensors q qLocal r T U v (fun j ↦ lab ⟨v, j⟩))) =
      (∏ v : {v : Fin (n + 1) // v ≠ r},
        Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab) (Sum.inl v.val)
          (T v.val (fun j ↦ vertexSplitInheritedLabel Θ r hq legEdge hleg lab ⟨v.val, j⟩))) *
      ∏ c : Fin 2, vertexSplitChildFactor Γ Θ r χ lab U c := by
  classical
  let F : Fin (n + 2) → Polynomial d R := fun v ↦
    (Γ.vertexSplit Θ r hq χ).vertexDerivative lab (Sum.inl v)
      (vertexSplitTensors q qLocal r T U v (fun j ↦ lab ⟨v, j⟩))
  calc
    (∏ v, F v) = ∏ s : {v : Fin (n + 1) // v ≠ r} ⊕ Fin 2,
        F ((vertexSplitSourceEquiv r).symm s) := by
      apply Fintype.prod_equiv (vertexSplitSourceEquiv r)
      intro v
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [vertexSplitSourceEquiv_symm_old, vertexSplitSourceEquiv_symm_child]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro v hv
        dsimp only [F]
        rw [vertexSplitTensors_old_labels q qLocal r T U v.val v.property]
        change (Γ.vertexSplit Θ r hq χ).vertexDerivative lab
          (vertexSplitOldVertex r (Sum.inl v.val)) _ = _
        rw [vertexDerivative_vertexSplit_old Γ Θ r hq legEdge hleg hcomplete χ lab
          (Sum.inl v.val) (by simpa using v.property)]
        apply congrArg (Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab)
          (Sum.inl v.val))
        apply congrArg (T v.val)
        funext j
        exact (vertexSplitInheritedLabel_outside Θ r hq legEdge hleg lab v.val v.property j).symm
      · apply Finset.prod_congr rfl
        intro c hc
        dsimp only [F]
        rw [vertexSplitTensors_child_labels, vertexDerivative_vertexSplit_child]
        rfl

include hcomplete in
/-- External input derivatives are unchanged, with the same entire inherited label family. -/
theorem vertexSplit_external_product (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) (f : Fin m → Polynomial d R) :
    (∏ j : Fin m, (Γ.vertexSplit Θ r hq χ).vertexDerivative lab (Sum.inr j) (f j)) =
      ∏ j : Fin m, Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab)
        (Sum.inr j) (f j) := by
  apply Finset.prod_congr rfl
  intro j hj
  change (Γ.vertexSplit Θ r hq χ).vertexDerivative lab
    (vertexSplitOldVertex r (Sum.inr j)) (f j) = _
  rw [vertexDerivative_vertexSplit_old Γ Θ r hq legEdge hleg hcomplete χ lab (Sum.inr j)
    (by simp)]

include hcomplete in
/-- The full labelled contraction factors into the unchanged vertices and the two children. -/
theorem vertexSplit_contraction_product (χ : Γ.VertexSplitChoices r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d)
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (f : Fin m → Polynomial d R) :
    ((∏ v : Fin (n + 2), (Γ.vertexSplit Θ r hq χ).vertexDerivative lab (Sum.inl v)
      (vertexSplitTensors q qLocal r T U v (fun j ↦ lab ⟨v, j⟩))) *
      ∏ j : Fin m, (Γ.vertexSplit Θ r hq χ).vertexDerivative lab (Sum.inr j) (f j)) =
      ((∏ v : {v : Fin (n + 1) // v ≠ r},
        Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab) (Sum.inl v.val)
          (T v.val (fun j ↦ vertexSplitInheritedLabel Θ r hq legEdge hleg lab ⟨v.val, j⟩))) *
        ∏ j : Fin m, Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab)
          (Sum.inr j) (f j)) *
        ∏ c : Fin 2, vertexSplitChildFactor Γ Θ r χ lab U c := by
  rw [vertexSplit_internal_product Γ Θ r hq legEdge hleg hcomplete,
    vertexSplit_external_product Γ Θ r hq legEdge hleg hcomplete]
  ring

include hcomplete in
/-- The genuine split-graph cochain is the finite sum of these factored contractions. -/
theorem cochainOperator_vertexSplit_expansion (χ : Γ.VertexSplitChoices r)
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (f : Fin m → Polynomial d R) :
    (Γ.vertexSplit Θ r hq χ).cochainOperator (vertexSplitTensors q qLocal r T U) f =
      ∑ lab : Edge (vertexSplitArity q qLocal r) → Fin d,
        ((∏ v : {v : Fin (n + 1) // v ≠ r},
          Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab) (Sum.inl v.val)
            (T v.val (fun j ↦ vertexSplitInheritedLabel Θ r hq legEdge hleg lab ⟨v.val, j⟩))) *
          ∏ j : Fin m, Γ.vertexDerivative (vertexSplitInheritedLabel Θ r hq legEdge hleg lab)
            (Sum.inr j) (f j)) *
          ∏ c : Fin 2, vertexSplitChildFactor Γ Θ r χ lab U c := by
  rw [cochainOperator_apply]
  apply Finset.sum_congr rfl
  intro lab hlab
  exact vertexSplit_contraction_product Γ Θ r hq legEdge hleg hcomplete χ lab T U f

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
