import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSubstitution
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitChoices
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitEvaluation

/-! The finite assignment and label identifications used by actual internal
graph substitution. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

open scoped BigOperators

variable {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin (n + 1) → ℕ}

theorem iteratedPDeriv_vertexSplitChoicesEquiv (Γ : Graph q m) (r : Fin (n + 1))
    (χ : Γ.VertexSplitChoices r) (c : Fin 2) (lab : Edge q → Fin d) :
    iteratedPDeriv (k := R)
        ((assignedEdges (Γ.incoming (Sum.inl r)) (Γ.vertexSplitChoicesEquiv r χ) c).toList.map lab) =
      iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map (fun e ↦ lab e.val)) := by
  rw [assignedEdges_vertexSplitChoicesEquiv, iteratedPDeriv_finset_map]
  rfl

theorem reconstructedLabel_outside (r : Fin (n + 1))
    (outsideLab : VertexSplitOutsideEdge q r → Fin d) (slots : Fin (q r) → Fin d)
    (e : VertexSplitOutsideEdge q r) :
    (vertexSplitOldLabelEquiv q r rfl d).symm (outsideLab, slots) e.val = outsideLab e := by
  have h := vertexSplitOldLabelEquiv_outside q r rfl d
    ((vertexSplitOldLabelEquiv q r rfl d).symm (outsideLab, slots)) e
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem iteratedPDeriv_vertexSplitChoices_reconstructed (Γ : Graph q m) (r : Fin (n + 1))
    (χ : Γ.VertexSplitChoices r) (c : Fin 2)
    (outsideLab : VertexSplitOutsideEdge q r → Fin d) (slots : Fin (q r) → Fin d) :
    iteratedPDeriv (k := R)
        ((assignedEdges (Γ.incoming (Sum.inl r)) (Γ.vertexSplitChoicesEquiv r χ) c).toList.map
          ((vertexSplitOldLabelEquiv q r rfl d).symm (outsideLab, slots))) =
      iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map outsideLab) := by
  rw [iteratedPDeriv_vertexSplitChoicesEquiv]
  simp only [reconstructedLabel_outside]

variable {qLocal : Fin 2 → ℕ}

/-- The genuine split graph has exactly the same remaining label sum as the
coordinate-template expansion. -/
theorem cochainOperator_vertexSplit_labels (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal (q r)) (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (χ : Γ.VertexSplitChoices r)
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (f : Fin m → Polynomial d R) :
    (Γ.vertexSplit Θ r rfl χ).cochainOperator (vertexSplitTensors q qLocal r T U) f =
      ∑ outsideLab : VertexSplitOutsideEdge q r → Fin d,
        ∑ localLab : Edge qLocal → Fin d,
          let oldLab := (vertexSplitOldLabelEquiv q r rfl d).symm
            (outsideLab, externalLabels legEdge localLab)
          Γ.vertexOuterFactor r oldLab T f * ∏ c : Fin 2,
            iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map outsideLab)
              (Θ.vertexDerivative localLab (Sum.inl c) (U c (fun j ↦ localLab ⟨c, j⟩))) := by
  classical
  let ht := Θ.leg_target_of_singleton legEdge hleg
  let hc := Θ.leg_complete_of_singleton legEdge hleg
  rw [cochainOperator_vertexSplit_expansion Γ Θ r rfl legEdge ht hc]
  let F : (VertexSplitOutsideEdge q r → Fin d) × (Edge qLocal → Fin d) → Polynomial d R :=
    fun labels ↦
      Γ.vertexOuterFactor r
        ((vertexSplitOldLabelEquiv q r rfl d).symm (labels.1, externalLabels legEdge labels.2)) T f *
        ∏ c : Fin 2,
          iteratedPDeriv ((Γ.vertexSplitAssignedEdges r χ c).toList.map labels.1)
            (Θ.vertexDerivative labels.2 (Sum.inl c) (U c (fun j ↦ labels.2 ⟨c, j⟩)))
  calc
    _ = ∑ labels, F labels := by
      apply Fintype.sum_equiv (vertexSplitLabelEquiv q qLocal r d)
      intro lab
      change Γ.vertexOuterFactor r (vertexSplitInheritedLabel Θ r rfl legEdge ht lab) T f *
        (∏ c : Fin 2, vertexSplitChildFactor Γ Θ r χ lab U c) = _
      have hlabels := vertexSplitOldEdge_labels r Θ legEdge ht lab
      change vertexSplitInheritedLabel Θ r rfl legEdge ht lab = _ at hlabels
      rw [hlabels]
      rfl
    _ = _ := Fintype.sum_prod_type F

/-- Substitution of an actual two-vertex coordinate template into an internal
tensor is the finite sum of all genuine admissible vertex splits. Every old
incoming arrow is assigned independently to one of the two children. -/
theorem cochainOperator_vertexSplit (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal (q r)) (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator (Function.update T r (Θ.templateTensor U)) f =
      ∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit Θ r rfl χ).cochainOperator (vertexSplitTensors q qLocal r T U) f := by
  classical
  rw [cochainOperator_template_expansion Γ r Θ legEdge hleg]
  symm
  apply Fintype.sum_equiv (Γ.vertexSplitChoicesEquiv r)
  intro χ
  rw [cochainOperator_vertexSplit_labels Γ r Θ legEdge hleg]
  simp only [iteratedPDeriv_vertexSplitChoices_reconstructed]

/-- The same substitution theorem with an explicit equality of outgoing arities. -/
theorem cochainOperator_vertexSplit_arity {p : ℕ} (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal p) (hq : q r = p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (c : Fin 2) → Tensor (qLocal c) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator (Function.update T r (hq.symm ▸ Θ.templateTensor U)) f =
      ∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit Θ r hq χ).cochainOperator (vertexSplitTensors q qLocal r T U) f := by
  subst p
  exact cochainOperator_vertexSplit Γ r Θ legEdge hleg T U f

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
