import EnvelopingIsomorphism.Deformation.GeneralGraphReindexing

/-! Actual incidence-preserving graph relabellings retaining each outgoing
slot number. The arities may be dependent and the vertex types may differ. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical
variable {n N M m : ℕ} {q : Fin n → ℕ} {p : Fin N → ℕ} {s : Fin M → ℕ}

structure SlotRelabelling (Γ : Graph q m) (Δ : Graph p m) where
  vertices : Fin n ≃ Fin N
  edges : Edge q ≃ Edge p
  source : ∀ e, (edges e).1 = vertices e.1
  slot : ∀ e, (edges e).2.val = e.2.val
  target : ∀ e, Δ.target (edges e) = Sum.map vertices id (Γ.target e)

namespace SlotRelabelling
variable {Γ : Graph q m} {Δ : Graph p m} {Θ : Graph s m}

def refl (Γ : Graph q m) : SlotRelabelling Γ Γ where
  vertices := Equiv.refl _
  edges := Equiv.refl _
  source _ := rfl
  slot _ := rfl
  target e := by
    change Γ.target e = Sum.map id id (Γ.target e)
    simp

def trans (F : SlotRelabelling Γ Δ) (G : SlotRelabelling Δ Θ) : SlotRelabelling Γ Θ where
  vertices := F.vertices.trans G.vertices
  edges := F.edges.trans G.edges
  source e := by simp only [Equiv.trans_apply, G.source, F.source]
  slot e := (G.slot _).trans (F.slot _)
  target e := by
    rw [Equiv.trans_apply, G.target, F.target]
    cases Γ.target e <;> rfl

def symm (F : SlotRelabelling Γ Δ) : SlotRelabelling Δ Γ where
  vertices := F.vertices.symm
  edges := F.edges.symm
  source e := by
    apply F.vertices.injective
    simpa using (F.source (F.edges.symm e)).symm
  slot e := by
    have h := (F.slot (F.edges.symm e)).symm
    rw [Equiv.apply_symm_apply] at h
    exact h
  target e := by
    have h := F.target (F.edges.symm e)
    rw [Equiv.apply_symm_apply] at h
    have hh := congrArg (Sum.map F.vertices.symm id) h
    cases he : Γ.target (F.edges.symm e) <;> simp [he] at hh ⊢ <;> exact hh.symm

/-- Outgoing slots and source labels determine an edge even with dependent arities. -/
theorem edge_eq_of_source_slot {e f : Edge q} (hs : e.1 = f.1) (hj : e.2.val = f.2.val) : e = f := by
  rcases e with ⟨v,j⟩
  rcases f with ⟨w,k⟩
  dsimp only at hs hj
  subst w
  exact congrArg (Sigma.mk v) (Fin.ext hj)

/-- Two actual relabellings with the same vertex equivalence give the same graph. -/
theorem graph_eq {Γ' : Graph p m} (F : SlotRelabelling Γ Δ) (G : SlotRelabelling Γ Γ')
    (hv : F.vertices = G.vertices) : Δ = Γ' := by
  apply Graph.ext
  funext e
  obtain ⟨e, rfl⟩ := F.edges.surjective e
  have he : F.edges e = G.edges e := edge_eq_of_source_slot
    ((F.source e).trans ((congrArg (fun v => v e.1) hv).trans (G.source e).symm))
    ((F.slot e).trans (G.slot e).symm)
  rw [F.target, he, G.target, hv]

end SlotRelabelling

namespace Graph

def slotRelabelling_permuteProfile (Γ : Graph q m) (σ : Equiv.Perm (Fin n)) :
    SlotRelabelling Γ (Γ.permuteProfile σ) where
  vertices := σ
  edges := profileEdgeEquiv q σ
  source := profileEdgeEquiv_source q σ
  slot := profileEdgeEquiv_slot_val q σ
  target := Γ.permuteProfile_target σ

def slotRelabelling_castProfile (Γ : Graph q m) {q' : Fin n → ℕ} (h : q = q') :
    SlotRelabelling Γ (castProfileEquiv h m Γ) := by
  subst q'
  exact SlotRelabelling.refl Γ

def slotRelabelling_oneExceptional (i : Fin n) (a : ℕ)
    (Γ : Graph (oneExceptionalArity a i) m) (σ : Equiv.Perm (Fin n)) :
    SlotRelabelling Γ (oneExceptionalGraphEquiv a i σ m Γ) :=
  (slotRelabelling_permuteProfile Γ σ).trans
    (slotRelabelling_castProfile _ (profileArity_oneExceptional a i σ))

end Graph

namespace SlotRelabelling
variable {a b A B o l : ℕ} {qa : Fin a → ℕ} {qb : Fin b → ℕ}
  {qA : Fin A → ℕ} {qB : Fin B → ℕ}
variable {Γ : Graph qa (o + 1)} {Γ' : Graph qA (o + 1)}
  {Δ : Graph qb (l + 1)} {Δ' : Graph qB (l + 1)}

def blockVertices (e : Fin a ≃ Fin A) (f : Fin b ≃ Fin B) : Fin (a + b) ≃ Fin (A + B) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

@[simp] theorem blockVertices_outer (e : Fin a ≃ Fin A) (f : Fin b ≃ Fin B) (v : Fin a) :
    blockVertices e f (Fin.castAdd b v) = Fin.castAdd B (e v) := by simp [blockVertices]

@[simp] theorem blockVertices_inner (e : Fin a ≃ Fin A) (f : Fin b ≃ Fin B) (v : Fin b) :
    blockVertices e f (Fin.natAdd a v) = Fin.natAdd A (f v) := by simp [blockVertices]

def blockEdges (e : Edge qa ≃ Edge qA) (f : Edge qb ≃ Edge qB) :
    Edge (graftArity qa qb) ≃ Edge (graftArity qA qB) :=
  (graftEdgeEquiv qa qb).trans ((Equiv.sumCongr e f).trans (graftEdgeEquiv qA qB).symm)

@[simp] theorem blockEdges_outer (e : Edge qa ≃ Edge qA) (f : Edge qb ≃ Edge qB) (x : Edge qa) :
    blockEdges e f (graftOuterEdge qa qb x) = graftOuterEdge qA qB (e x) := by
  simp [blockEdges, graftOuterEdge]

@[simp] theorem blockEdges_inner (e : Edge qa ≃ Edge qA) (f : Edge qb ≃ Edge qB) (x : Edge qb) :
    blockEdges e f (graftInnerEdge qa qb x) = graftInnerEdge qA qB (f x) := by
  simp [blockEdges, graftInnerEdge]

def incomingEquiv (F : SlotRelabelling Γ Γ') (r : Fin (o + 1)) :
    {e : Edge qa // Γ.target e = Sum.inr r} ≃ {e : Edge qA // Γ'.target e = Sum.inr r} :=
  Equiv.subtypeEquiv F.edges (by
    intro e
    rw [F.target]
    cases Γ.target e <;> simp)

def graftChoices (F : SlotRelabelling Γ Γ') (G : SlotRelabelling Δ Δ')
    (r : Fin (o + 1)) (χ : Γ.GraftChoices (b := b) (l := l) r) :
    Γ'.GraftChoices (b := B) (l := l) r :=
  fun e => Sum.map G.vertices id (χ ((incomingEquiv F r).symm e))

@[simp] theorem blockVertices_outerTarget (e : Fin a ≃ Fin A) (f : Fin b ≃ Fin B)
    (r : Fin (o + 1)) (v : Vertex a (o + 1)) :
    Sum.map (blockVertices e f) id (graftOuterVertex (b := b) (l := l) r v) =
      graftOuterVertex (b := B) (l := l) r (Sum.map e id v) := by
  cases v <;> simp [graftOuterVertex]

@[simp] theorem blockVertices_innerTarget (e : Fin a ≃ Fin A) (f : Fin b ≃ Fin B)
    (r : Fin (o + 1)) (v : Vertex b (l + 1)) :
    Sum.map (blockVertices e f) id (graftInnerVertex r v) =
      graftInnerVertex r (Sum.map f id v) := by
  cases v <;> simp [graftInnerVertex]

/-- Native graft incidence commutes with independent, slot-preserving actual
factor relabellings, including all dependent outgoing arities. -/
def graft (F : SlotRelabelling Γ Γ') (G : SlotRelabelling Δ Δ')
    (r : Fin (o + 1)) (χ : Γ.GraftChoices (b := b) (l := l) r) :
    SlotRelabelling (Γ.graft Δ r χ) (Γ'.graft Δ' r (graftChoices F G r χ)) where
  vertices := blockVertices F.vertices G.vertices
  edges := blockEdges F.edges G.edges
  source e := by
    obtain ⟨e, rfl⟩ := (graftEdgeEquiv qa qb).symm.surjective e
    cases e with
    | inl e =>
      change (blockEdges F.edges G.edges (graftOuterEdge qa qb e)).1 =
        blockVertices F.vertices G.vertices (graftOuterEdge qa qb e).1
      simp only [blockEdges_outer, graftOuterEdge_source, F.source, blockVertices_outer]
    | inr e =>
      change (blockEdges F.edges G.edges (graftInnerEdge qa qb e)).1 =
        blockVertices F.vertices G.vertices (graftInnerEdge qa qb e).1
      simp only [blockEdges_inner, graftInnerEdge_source, G.source, blockVertices_inner]
  slot e := by
    obtain ⟨e, rfl⟩ := (graftEdgeEquiv qa qb).symm.surjective e
    cases e with
    | inl e =>
      change (blockEdges F.edges G.edges (graftOuterEdge qa qb e)).2.val = (graftOuterEdge qa qb e).2.val
      exact (congrArg (fun x : Edge (graftArity qA qB) => x.2.val)
        (blockEdges_outer F.edges G.edges e)).trans
        ((graftOuterEdge_slot_val qA qB (F.edges e)).trans
          ((F.slot e).trans (graftOuterEdge_slot_val qa qb e).symm))
    | inr e =>
      change (blockEdges F.edges G.edges (graftInnerEdge qa qb e)).2.val = (graftInnerEdge qa qb e).2.val
      exact (congrArg (fun x : Edge (graftArity qA qB) => x.2.val)
        (blockEdges_inner F.edges G.edges e)).trans
        ((graftInnerEdge_slot_val qA qB (G.edges e)).trans
          ((G.slot e).trans (graftInnerEdge_slot_val qa qb e).symm))
  target e := by
    obtain ⟨e, rfl⟩ := (graftEdgeEquiv qa qb).symm.surjective e
    cases e with
    | inl e =>
      change (Γ'.graft Δ' r (graftChoices F G r χ)).target
        (blockEdges F.edges G.edges (graftOuterEdge qa qb e)) =
          Sum.map (blockVertices F.vertices G.vertices) id
            ((Γ.graft Δ r χ).target (graftOuterEdge qa qb e))
      rw [blockEdges_outer, Graph.graft_target_outer, Graph.graft_target_outer]
      have ht : Γ'.target (F.edges e) = Sum.inr r ↔ Γ.target e = Sum.inr r := by
        rw [F.target]
        cases Γ.target e <;> simp
      unfold Graph.graftOuterTarget
      by_cases h : Γ.target e = Sum.inr r
      · rw [dif_pos h, dif_pos (ht.mpr h), blockVertices_innerTarget]
        congr 1
        change Sum.map G.vertices id (χ ((incomingEquiv F r).symm
          ⟨F.edges e, ht.mpr h⟩)) = Sum.map G.vertices id (χ ⟨e, h⟩)
        congr 2
        apply Subtype.ext
        exact F.edges.symm_apply_apply e
      · rw [dif_neg h, dif_neg (mt ht.mp h), F.target, blockVertices_outerTarget]
    | inr e =>
      change (Γ'.graft Δ' r (graftChoices F G r χ)).target
        (blockEdges F.edges G.edges (graftInnerEdge qa qb e)) =
          Sum.map (blockVertices F.vertices G.vertices) id
            ((Γ.graft Δ r χ).target (graftInnerEdge qa qb e))
      rw [blockEdges_inner, Graph.graft_target_inner, Graph.graft_target_inner,
        G.target, blockVertices_innerTarget]

end SlotRelabelling
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
