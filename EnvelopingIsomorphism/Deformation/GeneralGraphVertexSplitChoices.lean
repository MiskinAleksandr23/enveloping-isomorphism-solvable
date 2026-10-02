import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitConstruction
import EnvelopingIsomorphism.Deformation.GraphLeibnizFinset

/-! Exact assignment reindexing for the incoming edges of a split internal vertex. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

variable {n m : ℕ} {q : Fin (n + 1) → ℕ}
variable (Γ : Graph q m) (r : Fin (n + 1))

/-- The actual incoming finset subtype is the target-equality fibre used by the constructor. -/
def vertexSplitIncomingSubtypeEquiv :
    Γ.incoming (Sum.inl r) ≃ {e : Edge q // Γ.target e = Sum.inl r} where
  toFun e := ⟨e.val, by simpa only [incoming, Finset.mem_filter, Finset.mem_univ, true_and]
    using e.property⟩
  invFun e := ⟨e.val, by simp only [incoming, Finset.mem_filter, Finset.mem_univ,
    true_and, e.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A genuine equivalence between constructor choices and finite-edge Leibniz assignments. -/
def vertexSplitChoicesEquiv : Γ.VertexSplitChoices r ≃ (Γ.incoming (Sum.inl r) → Fin 2) :=
  Equiv.arrowCongr (Γ.vertexSplitIncomingSubtypeEquiv r).symm (Equiv.refl _)

@[simp] theorem vertexSplitChoicesEquiv_apply (χ : Γ.VertexSplitChoices r)
    (e : Γ.incoming (Sum.inl r)) :
    Γ.vertexSplitChoicesEquiv r χ e = χ (Γ.vertexSplitIncomingSubtypeEquiv r e) := rfl

@[simp] theorem vertexSplitChoicesEquiv_symm_apply (χ : Γ.incoming (Sum.inl r) → Fin 2)
    (e : {e : Edge q // Γ.target e = Sum.inl r}) :
    (Γ.vertexSplitChoicesEquiv r).symm χ e = χ ((Γ.vertexSplitIncomingSubtypeEquiv r).symm e) := rfl

/-- The assigned old-edge finset is exactly the assigned outside-source finset mapped
by subtype value. Every edge entering `r` has source different from `r`, by no loops. -/
theorem assignedEdges_vertexSplitChoicesEquiv (χ : Γ.VertexSplitChoices r) (c : Fin 2) :
    assignedEdges (Γ.incoming (Sum.inl r)) (Γ.vertexSplitChoicesEquiv r χ) c =
      (Γ.vertexSplitAssignedEdges r χ c).map
        (Function.Embedding.subtype (fun e : Edge q ↦ e.1 ≠ r)) := by
  classical
  ext e
  rw [mem_assignedEdges, Finset.mem_map]
  constructor
  · rintro ⟨he, hc⟩
    have hh : Γ.target e = Sum.inl r := (Γ.vertexSplitIncomingSubtypeEquiv r ⟨e, he⟩).property
    have hs : e.1 ≠ r := Γ.vertexSplit_incoming_source_ne r e hh
    refine ⟨⟨e, hs⟩, ?_, rfl⟩
    rw [mem_vertexSplitAssignedEdges]
    refine ⟨hh, ?_⟩
    rw [vertexSplitChoice_of_hit Γ r χ e hh]
    exact hc
  · rintro ⟨f, hf, hfe⟩
    change f.val = e at hfe
    subst e
    obtain ⟨hh, hc⟩ := (Γ.mem_vertexSplitAssignedEdges r χ c f).mp hf
    have he : f.val ∈ Γ.incoming (Sum.inl r) := by simp [incoming, hh]
    refine ⟨he, ?_⟩
    rw [vertexSplitChoice_of_hit Γ r χ f.val hh] at hc
    exact hc

/-- The same equality in the direction used to rewrite a mapped outside-edge derivative. -/
theorem map_vertexSplitAssignedEdges (χ : Γ.VertexSplitChoices r) (c : Fin 2) :
    (Γ.vertexSplitAssignedEdges r χ c).map
        (Function.Embedding.subtype (fun e : Edge q ↦ e.1 ≠ r)) =
      assignedEdges (Γ.incoming (Sum.inl r)) (Γ.vertexSplitChoicesEquiv r χ) c :=
  (Γ.assignedEdges_vertexSplitChoicesEquiv r χ c).symm

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
