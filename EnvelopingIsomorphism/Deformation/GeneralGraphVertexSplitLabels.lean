import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitConstruction

/-! All old edge labels survive a vertex split with exactly one edge at each template leg. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {n m p : ℕ} (q : Fin (n + 1) → ℕ) (r : Fin (n + 1)) (hq : q r = p)

private theorem vertexSplitOldEdgeMap_bijective : Function.Bijective
    (Sum.elim (fun e : VertexSplitOutsideEdge q r ↦ e.val)
      (fun j : Fin p ↦ (⟨r, Fin.cast hq.symm j⟩ : Edge q))) := by
  constructor
  · rintro (e | i) (f | j) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact False.elim (e.property (congrArg Sigma.fst h))
    · exact False.elim (f.property (congrArg Sigma.fst h).symm)
    · apply congrArg Sum.inr
      apply Fin.ext
      exact congrArg (fun e : Edge q ↦ e.2.val) h
  · rintro ⟨v, j⟩
    by_cases hv : v = r
    · subst v
      exact ⟨Sum.inr (Fin.cast hq j), by simp⟩
    · exact ⟨Sum.inl ⟨⟨v, j⟩, hv⟩, rfl⟩

/-- Old edges consist of all sources outside the root and its ordered outgoing slots. -/
def vertexSplitOldEdgeEquiv : Edge q ≃ VertexSplitOutsideEdge q r ⊕ Fin p :=
  (Equiv.ofBijective _ (vertexSplitOldEdgeMap_bijective q r hq)).symm

@[simp] theorem vertexSplitOldEdgeEquiv_symm_outside (e : VertexSplitOutsideEdge q r) :
    (vertexSplitOldEdgeEquiv q r hq).symm (Sum.inl e) = e.val := rfl

@[simp] theorem vertexSplitOldEdgeEquiv_symm_root (j : Fin p) :
    (vertexSplitOldEdgeEquiv q r hq).symm (Sum.inr j) = ⟨r, Fin.cast hq.symm j⟩ := rfl

@[simp] theorem vertexSplitOldEdgeEquiv_outside (e : VertexSplitOutsideEdge q r) :
    vertexSplitOldEdgeEquiv q r hq e.val = Sum.inl e :=
  (vertexSplitOldEdgeEquiv q r hq).apply_symm_apply (Sum.inl e)

@[simp] theorem vertexSplitOldEdgeEquiv_root (j : Fin p) :
    vertexSplitOldEdgeEquiv q r hq ⟨r, Fin.cast hq.symm j⟩ = Sum.inr j :=
  (vertexSplitOldEdgeEquiv q r hq).apply_symm_apply (Sum.inr j)

/-- The corresponding exact factorization of all old label assignments. -/
def vertexSplitOldLabelEquiv (d : ℕ) : (Edge q → Fin d) ≃
    (VertexSplitOutsideEdge q r → Fin d) × (Fin p → Fin d) :=
  (Equiv.arrowCongr (vertexSplitOldEdgeEquiv q r hq) (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem vertexSplitOldLabelEquiv_outside (d : ℕ) (lab : Edge q → Fin d)
    (e : VertexSplitOutsideEdge q r) :
    (vertexSplitOldLabelEquiv q r hq d lab).1 e = lab e.val := rfl

@[simp] theorem vertexSplitOldLabelEquiv_root (d : ℕ) (lab : Edge q → Fin d) (j : Fin p) :
    (vertexSplitOldLabelEquiv q r hq d lab).2 j = lab ⟨r, Fin.cast hq.symm j⟩ := rfl

variable {q r hq} {qLocal : Fin 2 → ℕ}

namespace Graph

variable (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
  (hleg : ∀ j, Θ.target (legEdge j) = Sum.inr j)

include hleg in
/-- Distinct external legs have distinct chosen edges, solely by their targets. -/
theorem vertexSplitLegEdge_injective : Function.Injective legEdge := by
  intro i j h
  exact Sum.inr.inj ((hleg i).symm.trans ((congrArg Θ.target h).trans (hleg j)))

def vertexSplitLegEmbedding : Fin p ↪ Edge qLocal :=
  ⟨legEdge, Θ.vertexSplitLegEdge_injective legEdge hleg⟩

/-- Embed every old edge: outside-source edges stay outside, while root slots
become the unique template edges ending at their corresponding external legs. -/
def vertexSplitOldEdge (q : Fin (n + 1) → ℕ) (r : Fin (n + 1)) (hq : q r = p) :
    Edge q ↪ Edge (vertexSplitArity q qLocal r) :=
  (vertexSplitOldEdgeEquiv q r hq).toEmbedding.trans
    ((Function.Embedding.sumMap (Function.Embedding.refl _) (Θ.vertexSplitLegEmbedding legEdge hleg)).trans
      (vertexSplitEdgeEquiv q qLocal r).symm.toEmbedding)

@[simp] theorem vertexSplitOldEdge_outside (e : VertexSplitOutsideEdge q r) :
    Θ.vertexSplitOldEdge legEdge hleg q r hq e.val = vertexSplitOutsideEdge q qLocal r e := by
  simp [vertexSplitOldEdge, Function.Embedding.trans_apply, Function.Embedding.sumMap,
    vertexSplitOutsideEdge]

@[simp] theorem vertexSplitOldEdge_root (j : Fin p) :
    Θ.vertexSplitOldEdge legEdge hleg q r hq ⟨r, Fin.cast hq.symm j⟩ =
      vertexSplitLocalEdge q qLocal r (legEdge j) := by
  simp [vertexSplitOldEdge, Function.Embedding.trans_apply, Function.Embedding.sumMap,
    vertexSplitLocalEdge, vertexSplitLegEmbedding]

theorem vertexSplitOldEdge_root_slot (j : Fin (q r)) :
    Θ.vertexSplitOldEdge legEdge hleg q r hq ⟨r, j⟩ =
      vertexSplitLocalEdge q qLocal r (legEdge (Fin.cast hq j)) := by
  simpa using Θ.vertexSplitOldEdge_root legEdge hleg (q := q) (r := r) (hq := hq) (Fin.cast hq j)

variable (Γ : Graph q m) (r : Fin (n + 1)) (hq : q r = p)

/-- For a target unaffected by splitting, the whole old edge embedding preserves
and reflects the actual graph target. -/
theorem vertexSplitOldEdge_target_iff (χ : Γ.VertexSplitChoices r)
    (e : Edge q) (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    (Γ.vertexSplit Θ r hq χ).target (Θ.vertexSplitOldEdge legEdge hleg q r hq e) =
      vertexSplitOldVertex r v ↔ Γ.target e = v := by
  obtain ⟨e, rfl⟩ := (vertexSplitOldEdgeEquiv q r hq).symm.surjective e
  rcases e with e | j
  · change (Γ.vertexSplit Θ r hq χ).target
      (Θ.vertexSplitOldEdge legEdge hleg q r hq e.val) = _ ↔ _
    rw [vertexSplitOldEdge_outside, vertexSplit_target_outside]
    exact Γ.vertexSplitOutsideTarget_eq_old_iff r χ e v hv
  · change (Γ.vertexSplit Θ r hq χ).target
      (Θ.vertexSplitOldEdge legEdge hleg q r hq ⟨r, Fin.cast hq.symm j⟩) = _ ↔ _
    rw [vertexSplitOldEdge_root, vertexSplit_target_local, hleg,
      vertexSplitTemplateVertex_leg]
    exact (vertexSplitOldVertex_injective r).eq_iff

/-- With one template edge at every leg, the new incoming set at any unchanged
vertex is exactly the image of its entire original incoming set. -/
theorem incoming_vertexSplit_old_map
    (hcomplete : ∀ e j, Θ.target e = Sum.inr j → e = legEdge j)
    (χ : Γ.VertexSplitChoices r) (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    (Γ.vertexSplit Θ r hq χ).incoming (vertexSplitOldVertex r v) =
      (Γ.incoming v).map (Θ.vertexSplitOldEdge legEdge hleg q r hq) := by
  ext e
  constructor
  · intro he
    have ht : (Γ.vertexSplit Θ r hq χ).target e = vertexSplitOldVertex r v := by
      simpa only [incoming, Finset.mem_filter, Finset.mem_univ, true_and] using he
    obtain ⟨e, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
    rcases e with e | e
    · change (Γ.vertexSplit Θ r hq χ).target (vertexSplitOutsideEdge q qLocal r e) = _ at ht
      rw [vertexSplit_target_outside] at ht
      have hold := (Γ.vertexSplitOutsideTarget_eq_old_iff r χ e v hv).mp ht
      apply Finset.mem_map.mpr
      exact ⟨e.val, by simpa [incoming] using hold,
        Θ.vertexSplitOldEdge_outside legEdge hleg e⟩
    · change (Γ.vertexSplit Θ r hq χ).target (vertexSplitLocalEdge q qLocal r e) = _ at ht
      rw [vertexSplit_target_local] at ht
      obtain ⟨j, hj, hold⟩ := (Γ.vertexSplitTemplateVertex_eq_old_iff r hq (Θ.target e) v hv).mp ht
      have heq := hcomplete e j hj
      apply Finset.mem_map.mpr
      refine ⟨⟨r, Fin.cast hq.symm j⟩, by simpa [incoming] using hold, ?_⟩
      exact (Θ.vertexSplitOldEdge_root legEdge hleg (q := q) (r := r) (hq := hq) j).trans
        (congrArg (vertexSplitLocalEdge q qLocal r) heq.symm)
  · rintro he
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he
    have ht : Γ.target e = v := by simpa [incoming] using he
    have hnew := (Θ.vertexSplitOldEdge_target_iff legEdge hleg Γ r hq χ e v hv).mpr ht
    simpa [incoming] using hnew

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
