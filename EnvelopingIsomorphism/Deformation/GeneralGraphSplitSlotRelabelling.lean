import EnvelopingIsomorphism.Deformation.GeneralGraphSlotRelabelling
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLegPermutation

/-! Actual internal relabelling of a two-child split. Both the contracted
root and the child order may move; all dependent source arities and incoming
assignments are transported through their genuine finite equivalences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.SlotRelabelling
open scoped Classical
variable {n N m p : ℕ} {q : Fin (n + 1) → ℕ} {q' : Fin (N + 1) → ℕ}
  {qL qL' : Fin 2 → ℕ}

variable (r : Fin (n + 1)) (r' : Fin (N + 1))
variable (σ : Fin (n + 1) ≃ Fin (N + 1)) (hr : σ r = r')

def splitOutsideVertices : {v : Fin (n + 1) // v ≠ r} ≃ {v : Fin (N + 1) // v ≠ r'} :=
  Equiv.subtypeEquiv σ (by
    intro v
    have h : v ≠ r ↔ σ v ≠ σ r := σ.injective.ne_iff.symm
    simpa only [hr] using h)

def splitVertices (δ : Equiv.Perm (Fin 2)) : Fin (n + 2) ≃ Fin (N + 2) :=
  (vertexSplitSourceEquiv r).trans
    ((Equiv.sumCongr (splitOutsideVertices r r' σ hr) δ).trans (vertexSplitSourceEquiv r').symm)

@[simp] theorem splitVertices_old (δ : Equiv.Perm (Fin 2)) (v : Fin (n + 1)) (hv : v ≠ r) :
    splitVertices r r' σ hr δ (vertexSplitOldEmbedding r v) = vertexSplitOldEmbedding r' (σ v) := by
  change splitVertices r r' σ hr δ ((vertexSplitSourceEquiv r).symm (Sum.inl ⟨v,hv⟩)) = _
  simp only [splitVertices, Equiv.trans_apply, Equiv.apply_symm_apply]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, vertexSplitSourceEquiv_symm_old]
  rfl

@[simp] theorem splitVertices_child (δ : Equiv.Perm (Fin 2)) (c : Fin 2) :
    splitVertices r r' σ hr δ (vertexSplitChild r c) = vertexSplitChild r' (δ c) := by
  change splitVertices r r' σ hr δ ((vertexSplitSourceEquiv r).symm (Sum.inr c)) = _
  simp only [splitVertices, Equiv.trans_apply, Equiv.apply_symm_apply]
  simp only [Equiv.sumCongr_apply, Sum.map_inr, vertexSplitSourceEquiv_symm_child]

@[simp] theorem splitVertices_oldVertex (δ : Equiv.Perm (Fin 2))
    (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    Sum.map (splitVertices r r' σ hr δ) id (vertexSplitOldVertex r v) =
      vertexSplitOldVertex r' (Sum.map σ id v) := by
  cases v with
  | inr v => rfl
  | inl v =>
    change Sum.inl (splitVertices r r' σ hr δ (vertexSplitOldEmbedding r v)) = _
    rw [splitVertices_old r r' σ hr δ v (fun h => hv (congrArg Sum.inl h))]
    rfl

variable {Γ : Graph q m} {Γ' : Graph q' m} (F : SlotRelabelling Γ Γ')
variable {Θ : Graph qL p} {Θ' : Graph qL' p} (G : SlotRelabelling Θ Θ')

def splitOutsideEdges (hF : F.vertices r = r') : VertexSplitOutsideEdge q r ≃ VertexSplitOutsideEdge q' r' :=
  Equiv.subtypeEquiv F.edges (by
    intro e
    rw [F.source]
    have h : e.1 ≠ r ↔ F.vertices e.1 ≠ F.vertices r := F.vertices.injective.ne_iff.symm
    simpa only [hF] using h)

@[simp] theorem splitOutsideEdges_val (hF : F.vertices r = r') (e : VertexSplitOutsideEdge q r) :
    (splitOutsideEdges r r' F hF e).val = F.edges e.val := rfl

def splitEdges (hF : F.vertices r = r') :
    Edge (vertexSplitArity q qL r) ≃ Edge (vertexSplitArity q' qL' r') :=
  (vertexSplitEdgeEquiv q qL r).trans
    ((Equiv.sumCongr (splitOutsideEdges r r' F hF) G.edges).trans
      (vertexSplitEdgeEquiv q' qL' r').symm)

@[simp] theorem splitEdges_outside (hF : F.vertices r = r') (e : VertexSplitOutsideEdge q r) :
    splitEdges r r' F G hF (vertexSplitOutsideEdge q qL r e) =
      vertexSplitOutsideEdge q' qL' r' (splitOutsideEdges r r' F hF e) := by
  simp [splitEdges, vertexSplitOutsideEdge]

@[simp] theorem splitEdges_local (hF : F.vertices r = r') (e : Edge qL) :
    splitEdges r r' F G hF (vertexSplitLocalEdge q qL r e) =
      vertexSplitLocalEdge q' qL' r' (G.edges e) := by
  simp [splitEdges, vertexSplitLocalEdge]

def splitIncomingEquiv (hF : F.vertices r = r') :
    {e : Edge q // Γ.target e = Sum.inl r} ≃ {e : Edge q' // Γ'.target e = Sum.inl r'} :=
  Equiv.subtypeEquiv F.edges (by
    intro e
    rw [F.target]
    constructor
    · intro h
      rw [h]
      exact congrArg Sum.inl hF
    · intro h
      have he : Sum.map F.vertices id (Γ.target e) = Sum.map F.vertices id (Sum.inl r) := by
        simpa only [Sum.map_inl, hF] using h
      exact (Sum.map_injective.mpr ⟨F.vertices.injective, Function.injective_id⟩) he)

def splitChoices (hF : F.vertices r = r') (χ : Γ.VertexSplitChoices r) : Γ'.VertexSplitChoices r' :=
  fun e => G.vertices (χ ((splitIncomingEquiv r r' F hF).symm e))

variable (hq : q r = p) (hq' : q' r' = p)

theorem split_root_edge (hF : F.vertices r = r') (j : Fin p) :
    F.edges ⟨r,Fin.cast hq.symm j⟩ = ⟨r',Fin.cast hq'.symm j⟩ := by
  apply edge_eq_of_source_slot
  · exact (F.source _).trans hF
  · exact F.slot _

theorem split_templateVertex (hF : F.vertices r = r') (v : Vertex 2 p) :
    Sum.map (splitVertices r r' F.vertices hF G.vertices) id (Γ.vertexSplitTemplateVertex r hq v) =
      Γ'.vertexSplitTemplateVertex r' hq' (Sum.map G.vertices id v) := by
  cases v with
  | inl c =>
    change Sum.inl (splitVertices r r' F.vertices hF G.vertices (vertexSplitChild r c)) = _
    rw [splitVertices_child]
    rfl
  | inr j =>
    rw [Graph.vertexSplitTemplateVertex_leg]
    rw [splitVertices_oldVertex r r' F.vertices hF G.vertices _ (Γ.noLoops r _)]
    change vertexSplitOldVertex r' (Sum.map F.vertices id (Γ.target ⟨r,Fin.cast hq.symm j⟩)) = _
    rw [← F.target, split_root_edge r r' F hq hq' hF j]
    rfl

/-- Actual native splitting commutes with arbitrary root movement and child
exchange, with quotient and local arities transported edge by edge. -/
def vertexSplit (hF : F.vertices r = r') (χ : Γ.VertexSplitChoices r) :
    SlotRelabelling (Γ.vertexSplit Θ r hq χ)
      (Γ'.vertexSplit Θ' r' hq' (splitChoices r r' F G hF χ)) where
  vertices := splitVertices r r' F.vertices hF G.vertices
  edges := splitEdges r r' F G hF
  source e := by
    obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q qL r).symm.surjective e
    cases e with
    | inl e =>
      change (splitEdges r r' F G hF (vertexSplitOutsideEdge q qL r e)).1 =
        splitVertices r r' F.vertices hF G.vertices (vertexSplitOutsideEdge q qL r e).1
      rw [splitEdges_outside, vertexSplitOutsideEdge_source, vertexSplitOutsideEdge_source,
        splitVertices_old r r' F.vertices hF G.vertices e.val.1 e.property]
      exact congrArg (vertexSplitOldEmbedding r') (F.source e.val)
    | inr e =>
      change (splitEdges r r' F G hF (vertexSplitLocalEdge q qL r e)).1 =
        splitVertices r r' F.vertices hF G.vertices (vertexSplitLocalEdge q qL r e).1
      rw [splitEdges_local, vertexSplitLocalEdge_source, vertexSplitLocalEdge_source, splitVertices_child]
      exact congrArg (vertexSplitChild r') (G.source e)
  slot e := by
    obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q qL r).symm.surjective e
    cases e with
    | inl e =>
      change (splitEdges r r' F G hF (vertexSplitOutsideEdge q qL r e)).2.val =
        (vertexSplitOutsideEdge q qL r e).2.val
      exact (congrArg (fun x : Edge (vertexSplitArity q' qL' r') => x.2.val)
        (splitEdges_outside r r' F G hF e)).trans
        ((vertexSplitOutsideEdge_slot_val q' qL' r' _).trans
          ((F.slot e.val).trans (vertexSplitOutsideEdge_slot_val q qL r e).symm))
    | inr e =>
      change (splitEdges r r' F G hF (vertexSplitLocalEdge q qL r e)).2.val =
        (vertexSplitLocalEdge q qL r e).2.val
      exact (congrArg (fun x : Edge (vertexSplitArity q' qL' r') => x.2.val)
        (splitEdges_local r r' F G hF e)).trans
        ((vertexSplitLocalEdge_slot_val q' qL' r' _).trans
          ((G.slot e).trans (vertexSplitLocalEdge_slot_val q qL r e).symm))
  target e := by
    obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q qL r).symm.surjective e
    cases e with
    | inl e =>
      change (Γ'.vertexSplit Θ' r' hq' (splitChoices r r' F G hF χ)).target
        (splitEdges r r' F G hF (vertexSplitOutsideEdge q qL r e)) =
        Sum.map (splitVertices r r' F.vertices hF G.vertices) id
          ((Γ.vertexSplit Θ r hq χ).target (vertexSplitOutsideEdge q qL r e))
      rw [splitEdges_outside, Graph.vertexSplit_target_outside, Graph.vertexSplit_target_outside]
      have ht : Γ'.target (F.edges e.val) = Sum.inl r' ↔ Γ.target e.val = Sum.inl r := by
        rw [F.target]
        constructor
        · intro h
          apply (Sum.map_injective.mpr ⟨F.vertices.injective, Function.injective_id⟩)
          simpa only [Sum.map_inl, hF] using h
        · intro h
          rw [h]
          exact congrArg Sum.inl hF
      simp only [Graph.vertexSplitOutsideTarget, splitOutsideEdges_val]
      by_cases he : Γ.target e.val = Sum.inl r
      · rw [dif_pos he, dif_pos (ht.mpr he)]
        change Sum.inl (vertexSplitChild r' (G.vertices (χ ((splitIncomingEquiv r r' F hF).symm
          ⟨F.edges e.val,ht.mpr he⟩)))) = _
        rw [Sum.map_inl, splitVertices_child]
        congr 3
        apply congrArg χ
        apply Subtype.ext
        exact F.edges.symm_apply_apply e.val
      · rw [dif_neg he, dif_neg (mt ht.mp he), F.target,
          splitVertices_oldVertex r r' F.vertices hF G.vertices _ he]
    | inr e =>
      change (Γ'.vertexSplit Θ' r' hq' (splitChoices r r' F G hF χ)).target
        (splitEdges r r' F G hF (vertexSplitLocalEdge q qL r e)) =
        Sum.map (splitVertices r r' F.vertices hF G.vertices) id
          ((Γ.vertexSplit Θ r hq χ).target (vertexSplitLocalEdge q qL r e))
      rw [splitEdges_local, Graph.vertexSplit_target_local, Graph.vertexSplit_target_local,
        G.target, split_templateVertex r r' F G hq hq' hF]

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.SlotRelabelling
