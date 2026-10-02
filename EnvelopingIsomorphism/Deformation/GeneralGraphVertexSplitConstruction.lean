import EnvelopingIsomorphism.Deformation.GeneralGraphSplitConstruction
import Mathlib.Logic.Equiv.Fin.Basic

/-! Replace one internal graph vertex by a genuine two-vertex graph template. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {n m p : ℕ}

abbrev vertexSplitOldEmbedding (r : Fin (n + 1)) := splitExternalEmbedding r
abbrev vertexSplitChild (r : Fin (n + 1)) := splitExternalVertex r
abbrev vertexSplitCollapse (r : Fin (n + 1)) := splitExternalCollapse r

theorem vertexSplitChild_injective (r : Fin (n + 1)) :
    Function.Injective (vertexSplitChild r) := by
  intro c d h
  fin_cases c <;> fin_cases d <;> simp_all
  · exact Fin.ne_of_lt Fin.castSucc_lt_succ h
  · exact Fin.ne_of_gt Fin.castSucc_lt_succ h

theorem vertexSplitOld_ne_child (r v : Fin (n + 1)) (hv : v ≠ r) (c : Fin 2) :
    vertexSplitOldEmbedding r v ≠ vertexSplitChild r c := by
  intro h
  apply hv
  simpa using congrArg (vertexSplitCollapse r) h

private theorem vertexSplitSourceMap_bijective (r : Fin (n + 1)) :
    Function.Bijective (Sum.elim
      (fun v : {v : Fin (n + 1) // v ≠ r} ↦ vertexSplitOldEmbedding r v.val)
      (vertexSplitChild r)) := by
  constructor
  · rintro (v | c) (w | d) h
    · exact congrArg Sum.inl (Subtype.ext (splitExternalEmbedding_injective r h))
    · exact False.elim (vertexSplitOld_ne_child r v.val v.property d h)
    · exact False.elim (vertexSplitOld_ne_child r w.val w.property c h.symm)
    · exact congrArg Sum.inr (vertexSplitChild_injective r h)
  · intro v
    by_cases hleft : v = r.castSucc
    · exact ⟨Sum.inr 0, by simp [hleft]⟩
    · by_cases hright : v = r.succ
      · exact ⟨Sum.inr 1, by simp [hright]⟩
      · have hne : vertexSplitCollapse r v ≠ r := by
          intro h
          apply hright
          have hv := Fin.succAbove_predAbove hleft
          change r.predAbove v = r at h
          rw [h] at hv
          simpa using hv.symm
        exact ⟨Sum.inl ⟨vertexSplitCollapse r v, hne⟩, Fin.succAbove_predAbove hleft⟩

/-- Canonical source partition: unchanged old vertices and the two consecutive children. -/
def vertexSplitSourceEquiv (r : Fin (n + 1)) :
    Fin (n + 2) ≃ {v : Fin (n + 1) // v ≠ r} ⊕ Fin 2 :=
  (Equiv.ofBijective _ (vertexSplitSourceMap_bijective r)).symm

@[simp] theorem vertexSplitSourceEquiv_symm_old (r : Fin (n + 1))
    (v : {v : Fin (n + 1) // v ≠ r}) :
    (vertexSplitSourceEquiv r).symm (Sum.inl v) = vertexSplitOldEmbedding r v.val := rfl

@[simp] theorem vertexSplitSourceEquiv_symm_child (r : Fin (n + 1)) (c : Fin 2) :
    (vertexSplitSourceEquiv r).symm (Sum.inr c) = vertexSplitChild r c := rfl

@[simp] theorem vertexSplitSourceEquiv_old (r v : Fin (n + 1)) (hv : v ≠ r) :
    vertexSplitSourceEquiv r (vertexSplitOldEmbedding r v) = Sum.inl ⟨v, hv⟩ :=
  (vertexSplitSourceEquiv r).apply_symm_apply (Sum.inl ⟨v, hv⟩)

@[simp] theorem vertexSplitSourceEquiv_child (r : Fin (n + 1)) (c : Fin 2) :
    vertexSplitSourceEquiv r (vertexSplitChild r c) = Sum.inr c :=
  (vertexSplitSourceEquiv r).apply_symm_apply (Sum.inr c)

variable (q : Fin (n + 1) → ℕ) (qLocal : Fin 2 → ℕ) (r : Fin (n + 1))

/-- Children have the template arities; every other vertex retains its original arity. -/
def vertexSplitArity (v : Fin (n + 2)) : ℕ :=
  Sum.elim (fun w : {w : Fin (n + 1) // w ≠ r} ↦ q w.val) qLocal (vertexSplitSourceEquiv r v)

@[simp] theorem vertexSplitArity_old (v : Fin (n + 1)) (hv : v ≠ r) :
    vertexSplitArity q qLocal r (vertexSplitOldEmbedding r v) = q v := by
  simp [vertexSplitArity, vertexSplitSourceEquiv_old r v hv]

@[simp] theorem vertexSplitArity_child (c : Fin 2) :
    vertexSplitArity q qLocal r (vertexSplitChild r c) = qLocal c := by
  simp [vertexSplitArity]

@[simp] theorem vertexSplitArity_left : vertexSplitArity q qLocal r r.castSucc = qLocal 0 := by
  simpa only [vertexSplitChild, splitExternalVertex_zero] using vertexSplitArity_child q qLocal r 0

@[simp] theorem vertexSplitArity_right : vertexSplitArity q qLocal r r.succ = qLocal 1 := by
  simpa only [vertexSplitChild, splitExternalVertex_one] using vertexSplitArity_child q qLocal r 1

theorem vertexSplitArity_of_ne_children (v : Fin (n + 2))
    (hleft : v ≠ r.castSucc) (hright : v ≠ r.succ) :
    vertexSplitArity q qLocal r v = q (vertexSplitCollapse r v) := by
  have hne : vertexSplitCollapse r v ≠ r := by
    intro h
    apply hright
    have hv := Fin.succAbove_predAbove hleft
    change r.predAbove v = r at h
    rw [h] at hv
    simpa using hv.symm
  have hv : vertexSplitOldEmbedding r (vertexSplitCollapse r v) = v :=
    Fin.succAbove_predAbove hleft
  rw [← hv, vertexSplitArity_old q qLocal r _ hne]
  simp

abbrev VertexSplitOutsideEdge := {e : Edge q // e.1 ≠ r}

private def vertexSplitOutsideSigmaEquiv :
    ((v : {v : Fin (n + 1) // v ≠ r}) × Fin (q v.val)) ≃ VertexSplitOutsideEdge q r where
  toFun e := ⟨⟨e.1.val, e.2⟩, e.1.property⟩
  invFun e := ⟨⟨e.val.1, e.property⟩, e.val.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Edges are exactly the old edges outside the replaced source and all template edges. -/
def vertexSplitEdgeEquiv :
    Edge (vertexSplitArity q qLocal r) ≃ VertexSplitOutsideEdge q r ⊕ Edge qLocal :=
  ((Equiv.sigmaCongrLeft
    (β := fun s ↦ Fin (Sum.elim (fun v : {v : Fin (n + 1) // v ≠ r} ↦ q v.val) qLocal s))
    (vertexSplitSourceEquiv r)).trans (Equiv.sumSigmaDistrib _)).trans
    (Equiv.sumCongr (vertexSplitOutsideSigmaEquiv q r) (Equiv.refl _))

def vertexSplitOutsideEdge : VertexSplitOutsideEdge q r ↪ Edge (vertexSplitArity q qLocal r) :=
  Function.Embedding.inl.trans (vertexSplitEdgeEquiv q qLocal r).symm.toEmbedding

def vertexSplitLocalEdge : Edge qLocal ↪ Edge (vertexSplitArity q qLocal r) :=
  Function.Embedding.inr.trans (vertexSplitEdgeEquiv q qLocal r).symm.toEmbedding

@[simp] theorem vertexSplitEdgeEquiv_outside (e : VertexSplitOutsideEdge q r) :
    vertexSplitEdgeEquiv q qLocal r (vertexSplitOutsideEdge q qLocal r e) = Sum.inl e :=
  (vertexSplitEdgeEquiv q qLocal r).apply_symm_apply (Sum.inl e)

@[simp] theorem vertexSplitEdgeEquiv_local (e : Edge qLocal) :
    vertexSplitEdgeEquiv q qLocal r (vertexSplitLocalEdge q qLocal r e) = Sum.inr e :=
  (vertexSplitEdgeEquiv q qLocal r).apply_symm_apply (Sum.inr e)

@[simp] theorem vertexSplitOutsideEdge_source (e : VertexSplitOutsideEdge q r) :
    (vertexSplitOutsideEdge q qLocal r e).1 = vertexSplitOldEmbedding r e.val.1 := rfl

@[simp] theorem vertexSplitLocalEdge_source (e : Edge qLocal) :
    (vertexSplitLocalEdge q qLocal r e).1 = vertexSplitChild r e.1 := rfl

theorem vertexSplitEdgeEquiv_slot_val (e : Edge (vertexSplitArity q qLocal r)) :
    Sum.elim (fun f : VertexSplitOutsideEdge q r ↦ f.val.2.val)
      (fun f : Edge qLocal ↦ f.2.val) (vertexSplitEdgeEquiv q qLocal r e) = e.2.val := by
  have h (s : (v : {v : Fin (n + 1) // v ≠ r} ⊕ Fin 2) ×
      Fin (Sum.elim (fun w : {w : Fin (n + 1) // w ≠ r} ↦ q w.val) qLocal v)) :
      Sum.elim (fun f : VertexSplitOutsideEdge q r ↦ f.val.2.val)
        (fun f : Edge qLocal ↦ f.2.val)
        ((Equiv.sumCongr (vertexSplitOutsideSigmaEquiv q r) (Equiv.refl _))
          (Equiv.sumSigmaDistrib _ s)) = s.2.val := by
    rcases s with ⟨v | c, j⟩ <;> rfl
  exact h ⟨vertexSplitSourceEquiv r e.1, e.2⟩

@[simp] theorem vertexSplitOutsideEdge_slot_val (e : VertexSplitOutsideEdge q r) :
    (vertexSplitOutsideEdge q qLocal r e).2.val = e.val.2.val := by
  simpa only [vertexSplitEdgeEquiv_outside, Sum.elim_inl] using
    (vertexSplitEdgeEquiv_slot_val q qLocal r (vertexSplitOutsideEdge q qLocal r e)).symm

@[simp] theorem vertexSplitLocalEdge_slot_val (e : Edge qLocal) :
    (vertexSplitLocalEdge q qLocal r e).2.val = e.2.val := by
  simpa only [vertexSplitEdgeEquiv_local, Sum.elim_inr] using
    (vertexSplitEdgeEquiv_slot_val q qLocal r (vertexSplitLocalEdge q qLocal r e)).symm

@[simp] theorem vertexSplitOutsideEdge_eq_iff (e f : VertexSplitOutsideEdge q r) :
    vertexSplitOutsideEdge q qLocal r e = vertexSplitOutsideEdge q qLocal r f ↔ e = f :=
  (vertexSplitOutsideEdge q qLocal r).injective.eq_iff

@[simp] theorem vertexSplitLocalEdge_eq_iff (e f : Edge qLocal) :
    vertexSplitLocalEdge q qLocal r e = vertexSplitLocalEdge q qLocal r f ↔ e = f :=
  (vertexSplitLocalEdge q qLocal r).injective.eq_iff

theorem vertexSplitOutsideEdge_ne_local (e : VertexSplitOutsideEdge q r) (f : Edge qLocal) :
    vertexSplitOutsideEdge q qLocal r e ≠ vertexSplitLocalEdge q qLocal r f := by
  intro h
  have := congrArg (vertexSplitEdgeEquiv q qLocal r) h
  simp at this

/-- Finsets of the two edge colours are always disjoint after embedding. -/
theorem vertexSplit_edgeColours_disjoint (s : Finset (VertexSplitOutsideEdge q r))
    (t : Finset (Edge qLocal)) :
    Disjoint (s.map (vertexSplitOutsideEdge q qLocal r)) (t.map (vertexSplitLocalEdge q qLocal r)) := by
  apply Finset.disjoint_left.mpr
  intro e hs ht
  obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨g, _, hg⟩ := Finset.mem_map.mp ht
  exact vertexSplitOutsideEdge_ne_local q qLocal r f g hg.symm

@[simp] theorem vertexSplitOutsideEdge_not_mem_local (e : VertexSplitOutsideEdge q r)
    (t : Finset (Edge qLocal)) :
    vertexSplitOutsideEdge q qLocal r e ∉ t.map (vertexSplitLocalEdge q qLocal r) := by
  intro h
  obtain ⟨f, _, hf⟩ := Finset.mem_map.mp h
  exact vertexSplitOutsideEdge_ne_local q qLocal r e f hf.symm

@[simp] theorem vertexSplitLocalEdge_not_mem_outside (e : Edge qLocal)
    (s : Finset (VertexSplitOutsideEdge q r)) :
    vertexSplitLocalEdge q qLocal r e ∉ s.map (vertexSplitOutsideEdge q qLocal r) := by
  intro h
  obtain ⟨f, _, hf⟩ := Finset.mem_map.mp h
  exact vertexSplitOutsideEdge_ne_local q qLocal r f e hf

def vertexSplitLabelEquiv (d : ℕ) :
    (Edge (vertexSplitArity q qLocal r) → Fin d) ≃
      (VertexSplitOutsideEdge q r → Fin d) × (Edge qLocal → Fin d) :=
  (Equiv.arrowCongr (vertexSplitEdgeEquiv q qLocal r) (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem vertexSplitLabelEquiv_outside (d : ℕ)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) (e : VertexSplitOutsideEdge q r) :
    (vertexSplitLabelEquiv q qLocal r d lab).1 e = lab (vertexSplitOutsideEdge q qLocal r e) := rfl

@[simp] theorem vertexSplitLabelEquiv_local (d : ℕ)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) (e : Edge qLocal) :
    (vertexSplitLabelEquiv q qLocal r d lab).2 e = lab (vertexSplitLocalEdge q qLocal r e) := rfl

variable {q qLocal r}

/-- Total embedding of old target vertices; targets equal to the replaced vertex are overridden. -/
def vertexSplitOldVertex (r : Fin (n + 1)) : Vertex (n + 1) m → Vertex (n + 2) m :=
  Sum.map (vertexSplitOldEmbedding r) id

def vertexSplitCollapseVertex (r : Fin (n + 1)) : Vertex (n + 2) m → Vertex (n + 1) m :=
  Sum.map (vertexSplitCollapse r) id

@[simp] theorem vertexSplitCollapseVertex_old (r : Fin (n + 1)) (v : Vertex (n + 1) m) :
    vertexSplitCollapseVertex r (vertexSplitOldVertex r v) = v := by
  cases v <;> simp [vertexSplitOldVertex, vertexSplitCollapseVertex]

@[simp] theorem vertexSplitCollapseVertex_child (r : Fin (n + 1)) (c : Fin 2) :
    vertexSplitCollapseVertex (m := m) r (Sum.inl (vertexSplitChild r c)) = Sum.inl r := by
  simp [vertexSplitCollapseVertex]

theorem vertexSplitOldVertex_injective (r : Fin (n + 1)) :
    Function.Injective (vertexSplitOldVertex (m := m) r) := by
  intro v w h
  simpa using congrArg (vertexSplitCollapseVertex r) h

theorem vertexSplitOldVertex_ne_child (r : Fin (n + 1)) (v : Vertex (n + 1) m)
    (hv : v ≠ Sum.inl r) (c : Fin 2) :
    vertexSplitOldVertex r v ≠ Sum.inl (vertexSplitChild r c) := by
  intro h
  apply hv
  simpa using congrArg (vertexSplitCollapseVertex r) h

namespace Graph

variable (Γ : Graph q m) (Θ : Graph qLocal p) (r : Fin (n + 1)) (hq : q r = p)

/-- Each incoming old edge chooses the child that receives it. -/
abbrev VertexSplitChoices := {e : Edge q // Γ.target e = Sum.inl r} → Fin 2

def vertexSplitChoice (χ : Γ.VertexSplitChoices r) (e : Edge q) : Fin 2 :=
  if h : Γ.target e = Sum.inl r then χ ⟨e, h⟩ else 0

@[simp] theorem vertexSplitChoice_of_hit (χ : Γ.VertexSplitChoices r)
    (e : Edge q) (h : Γ.target e = Sum.inl r) : Γ.vertexSplitChoice r χ e = χ ⟨e, h⟩ := by
  simp [vertexSplitChoice, h]

/-- An edge entering `r` cannot itself have source `r`. -/
theorem vertexSplit_incoming_source_ne (e : Edge q) (h : Γ.target e = Sum.inl r) : e.1 ≠ r := by
  intro hs
  apply Γ.noLoops e.1 e.2
  simpa only [hs] using h

/-- Template children are embedded as the consecutive new vertices. A template external
leg follows the matching old outgoing slot at `r` to its original target. -/
def vertexSplitTemplateVertex : Vertex 2 p → Vertex (n + 2) m :=
  Sum.elim (fun c ↦ Sum.inl (vertexSplitChild r c))
    (fun k ↦ vertexSplitOldVertex r (Γ.target ⟨r, Fin.cast hq.symm k⟩))

@[simp] theorem vertexSplitTemplateVertex_child (c : Fin 2) :
    Γ.vertexSplitTemplateVertex r hq (Sum.inl c) = Sum.inl (vertexSplitChild r c) := rfl

@[simp] theorem vertexSplitTemplateVertex_leg (k : Fin p) :
    Γ.vertexSplitTemplateVertex r hq (Sum.inr k) =
      vertexSplitOldVertex r (Γ.target ⟨r, Fin.cast hq.symm k⟩) := rfl

/-- Distinct old outgoing targets and the absence of old loops make template vertex
translation injective, without restrictions on the template's incoming valencies. -/
theorem vertexSplitTemplateVertex_injective :
    Function.Injective (Γ.vertexSplitTemplateVertex r hq) := by
  rintro (c | k) (d | j) h
  · exact congrArg Sum.inl (vertexSplitChild_injective r (Sum.inl.inj h))
  · exact False.elim (vertexSplitOldVertex_ne_child r _ (Γ.noLoops r _) c h.symm)
  · exact False.elim (vertexSplitOldVertex_ne_child r _ (Γ.noLoops r _) d h)
  · have ht := vertexSplitOldVertex_injective r h
    have hk := Γ.distinctTargets r ht
    exact congrArg Sum.inr (Fin.cast_injective _ hk)

/-- Unchanged-source edges keep their old target, except that incoming edges at `r`
are sent to their selected child. -/
def vertexSplitOutsideTarget (χ : Γ.VertexSplitChoices r) (e : VertexSplitOutsideEdge q r) :
    Vertex (n + 2) m :=
  if h : Γ.target e.val = Sum.inl r then Sum.inl (vertexSplitChild r (χ ⟨e.val, h⟩))
  else vertexSplitOldVertex r (Γ.target e.val)

@[simp] theorem collapse_vertexSplitOutsideTarget (χ : Γ.VertexSplitChoices r)
    (e : VertexSplitOutsideEdge q r) :
    vertexSplitCollapseVertex r (Γ.vertexSplitOutsideTarget r χ e) = Γ.target e.val := by
  by_cases h : Γ.target e.val = Sum.inl r <;> simp [vertexSplitOutsideTarget, h]

def vertexSplitTarget (χ : Γ.VertexSplitChoices r) (e : Edge (vertexSplitArity q qLocal r)) :
    Vertex (n + 2) m :=
  Sum.elim (Γ.vertexSplitOutsideTarget r χ) (fun f ↦ Γ.vertexSplitTemplateVertex r hq (Θ.target f))
    (vertexSplitEdgeEquiv q qLocal r e)

@[simp] theorem vertexSplitTarget_outside (χ : Γ.VertexSplitChoices r)
    (e : VertexSplitOutsideEdge q r) :
    Γ.vertexSplitTarget Θ r hq χ (vertexSplitOutsideEdge q qLocal r e) =
      Γ.vertexSplitOutsideTarget r χ e := by simp [vertexSplitTarget]

@[simp] theorem vertexSplitTarget_local (χ : Γ.VertexSplitChoices r) (e : Edge qLocal) :
    Γ.vertexSplitTarget Θ r hq χ (vertexSplitLocalEdge q qLocal r e) =
      Γ.vertexSplitTemplateVertex r hq (Θ.target e) := by simp [vertexSplitTarget]

private theorem vertexSplitTarget_noLoops (χ : Γ.VertexSplitChoices r)
    (e : Edge (vertexSplitArity q qLocal r)) :
    Γ.vertexSplitTarget Θ r hq χ e ≠ Sum.inl e.1 := by
  obtain ⟨f, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  rcases f with f | f
  · change Γ.vertexSplitTarget Θ r hq χ (vertexSplitOutsideEdge q qLocal r f) ≠
      Sum.inl (vertexSplitOutsideEdge q qLocal r f).1
    rw [vertexSplitTarget_outside, vertexSplitOutsideEdge_source]
    intro h
    apply Γ.noLoops f.val.1 f.val.2
    have hh := congrArg (vertexSplitCollapseVertex r) h
    rw [collapse_vertexSplitOutsideTarget] at hh
    simpa [vertexSplitCollapseVertex] using hh
  · change Γ.vertexSplitTarget Θ r hq χ (vertexSplitLocalEdge q qLocal r f) ≠
      Sum.inl (vertexSplitLocalEdge q qLocal r f).1
    rw [vertexSplitTarget_local, vertexSplitLocalEdge_source]
    intro h
    apply Θ.noLoops f.1 f.2
    exact Γ.vertexSplitTemplateVertex_injective r hq h

private theorem edge_eq_of_source_target {a b : ℕ} {q : Fin a → ℕ}
    (G : Graph q b) (e f : Edge q) (hs : e.1 = f.1) (ht : G.target e = G.target f) : e = f := by
  rcases e with ⟨v, i⟩
  rcases f with ⟨w, j⟩
  dsimp only at hs
  subst w
  have hij := G.distinctTargets v ht
  subst j
  rfl

private theorem vertexSplitTarget_eq_of_source (χ : Γ.VertexSplitChoices r)
    (e f : Edge (vertexSplitArity q qLocal r)) (hs : e.1 = f.1)
    (ht : Γ.vertexSplitTarget Θ r hq χ e = Γ.vertexSplitTarget Θ r hq χ f) : e = f := by
  obtain ⟨e, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  obtain ⟨f, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective f
  rcases e with e | e <;> rcases f with f | f
  · change (vertexSplitOutsideEdge q qLocal r e).1 =
      (vertexSplitOutsideEdge q qLocal r f).1 at hs
    simp only [vertexSplitOutsideEdge_source] at hs
    have hs' := splitExternalEmbedding_injective r hs
    have ht' : Γ.target e.val = Γ.target f.val := by
      change Γ.vertexSplitTarget Θ r hq χ (vertexSplitOutsideEdge q qLocal r e) =
        Γ.vertexSplitTarget Θ r hq χ (vertexSplitOutsideEdge q qLocal r f) at ht
      simpa using congrArg (vertexSplitCollapseVertex r) ht
    have hef : e = f := Subtype.ext (edge_eq_of_source_target Γ e.val f.val hs' ht')
    subst f
    rfl
  · change vertexSplitOldEmbedding r e.val.1 = vertexSplitChild r f.1 at hs
    exact False.elim (vertexSplitOld_ne_child r e.val.1 e.property f.1 hs)
  · change vertexSplitChild r e.1 = vertexSplitOldEmbedding r f.val.1 at hs
    exact False.elim (vertexSplitOld_ne_child r f.val.1 f.property e.1 hs.symm)
  · change (vertexSplitLocalEdge q qLocal r e).1 = (vertexSplitLocalEdge q qLocal r f).1 at hs
    simp only [vertexSplitLocalEdge_source] at hs
    have hs' := vertexSplitChild_injective r hs
    have ht' : Θ.target e = Θ.target f := by
      apply Γ.vertexSplitTemplateVertex_injective r hq
      change Γ.vertexSplitTarget Θ r hq χ (vertexSplitLocalEdge q qLocal r e) =
        Γ.vertexSplitTarget Θ r hq χ (vertexSplitLocalEdge q qLocal r f) at ht
      simpa using ht
    have hef := edge_eq_of_source_target Θ e f hs' ht'
    subst f
    rfl

/-- Genuine replacement of the internal vertex `r` by a two-vertex graph template. -/
def vertexSplit (χ : Γ.VertexSplitChoices r) : Graph (vertexSplitArity q qLocal r) m where
  target := Γ.vertexSplitTarget Θ r hq χ
  noLoops v j := Γ.vertexSplitTarget_noLoops Θ r hq χ ⟨v, j⟩
  distinctTargets v i j h := by
    have hh := Γ.vertexSplitTarget_eq_of_source Θ r hq χ ⟨v, i⟩ ⟨v, j⟩ rfl h
    apply Fin.ext
    exact congrArg (fun e : Edge (vertexSplitArity q qLocal r) ↦ e.2.val) hh

@[simp] theorem vertexSplit_target_outside (χ : Γ.VertexSplitChoices r)
    (e : VertexSplitOutsideEdge q r) :
    (Γ.vertexSplit Θ r hq χ).target (vertexSplitOutsideEdge q qLocal r e) =
      Γ.vertexSplitOutsideTarget r χ e := Γ.vertexSplitTarget_outside Θ r hq χ e

@[simp] theorem vertexSplit_target_local (χ : Γ.VertexSplitChoices r) (e : Edge qLocal) :
    (Γ.vertexSplit Θ r hq χ).target (vertexSplitLocalEdge q qLocal r e) =
      Γ.vertexSplitTemplateVertex r hq (Θ.target e) := Γ.vertexSplitTarget_local Θ r hq χ e

theorem vertexSplitOutsideTarget_eq_child_iff (χ : Γ.VertexSplitChoices r)
    (e : VertexSplitOutsideEdge q r) (c : Fin 2) :
    Γ.vertexSplitOutsideTarget r χ e = Sum.inl (vertexSplitChild r c) ↔
      Γ.target e.val = Sum.inl r ∧ Γ.vertexSplitChoice r χ e.val = c := by
  by_cases h : Γ.target e.val = Sum.inl r
  · simp [vertexSplitOutsideTarget, h, (vertexSplitChild_injective r).eq_iff]
  · simp only [h, false_and, iff_false]
    intro he
    apply h
    simpa using congrArg (vertexSplitCollapseVertex r) he

theorem vertexSplitOutsideTarget_eq_old_iff (χ : Γ.VertexSplitChoices r)
    (e : VertexSplitOutsideEdge q r) (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    Γ.vertexSplitOutsideTarget r χ e = vertexSplitOldVertex r v ↔ Γ.target e.val = v := by
  constructor
  · intro h
    simpa using congrArg (vertexSplitCollapseVertex r) h
  · intro h
    simp [vertexSplitOutsideTarget, h, hv]

theorem vertexSplitTemplateVertex_eq_old_iff (w : Vertex 2 p) (v : Vertex (n + 1) m)
    (hv : v ≠ Sum.inl r) :
    Γ.vertexSplitTemplateVertex r hq w = vertexSplitOldVertex r v ↔
      ∃ k : Fin p, w = Sum.inr k ∧ Γ.target ⟨r, Fin.cast hq.symm k⟩ = v := by
  rcases w with c | k
  · simp only [vertexSplitTemplateVertex_child, Sum.inl_ne_inr,
      false_and, exists_false, iff_false]
    exact (vertexSplitOldVertex_ne_child r v hv c).symm
  · simp [vertexSplitTemplateVertex_leg, (vertexSplitOldVertex_injective r).eq_iff]

/-- Original incoming edges with sources different from the replaced vertex. -/
def vertexSplitOutsideIncoming (v : Vertex (n + 1) m) : Finset (VertexSplitOutsideEdge q r) :=
  Finset.univ.filter (fun e ↦ Γ.target e.val = v)

@[simp] theorem mem_vertexSplitOutsideIncoming (v : Vertex (n + 1) m)
    (e : VertexSplitOutsideEdge q r) : e ∈ Γ.vertexSplitOutsideIncoming r v ↔ Γ.target e.val = v := by
  simp [vertexSplitOutsideIncoming]

/-- Incoming old edges allocated to one of the new children. -/
def vertexSplitAssignedEdges (χ : Γ.VertexSplitChoices r) (c : Fin 2) :
    Finset (VertexSplitOutsideEdge q r) :=
  (Γ.vertexSplitOutsideIncoming r (Sum.inl r)).filter
    (fun e ↦ Γ.vertexSplitChoice r χ e.val = c)

@[simp] theorem mem_vertexSplitAssignedEdges (χ : Γ.VertexSplitChoices r)
    (c : Fin 2) (e : VertexSplitOutsideEdge q r) :
    e ∈ Γ.vertexSplitAssignedEdges r χ c ↔
      Γ.target e.val = Sum.inl r ∧ Γ.vertexSplitChoice r χ e.val = c := by
  simp [vertexSplitAssignedEdges]

/-- All template edges ending in a leg whose original outgoing target is `v`. -/
def vertexSplitLegIncoming (v : Vertex (n + 1) m) : Finset (Edge qLocal) :=
  Finset.univ.filter (fun e ↦ ∃ k : Fin p,
    Θ.target e = Sum.inr k ∧ Γ.target ⟨r, Fin.cast hq.symm k⟩ = v)

@[simp] theorem mem_vertexSplitLegIncoming (v : Vertex (n + 1) m) (e : Edge qLocal) :
    e ∈ Γ.vertexSplitLegIncoming Θ r hq v ↔ ∃ k : Fin p,
      Θ.target e = Sum.inr k ∧ Γ.target ⟨r, Fin.cast hq.symm k⟩ = v := by
  simp [vertexSplitLegIncoming]

/-- The new child receives assigned old edges and the template's original incoming edges. -/
theorem incoming_vertexSplit_child (χ : Γ.VertexSplitChoices r) (c : Fin 2) :
    (Γ.vertexSplit Θ r hq χ).incoming (Sum.inl (vertexSplitChild r c)) =
      (Γ.vertexSplitAssignedEdges r χ c).map (vertexSplitOutsideEdge q qLocal r) ∪
        (Θ.incoming (Sum.inl c)).map (vertexSplitLocalEdge q qLocal r) := by
  ext e
  obtain ⟨e, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  rcases e with e | e
  · change vertexSplitOutsideEdge q qLocal r e ∈ _ ↔ vertexSplitOutsideEdge q qLocal r e ∈ _
    simp only [Finset.mem_union, Finset.mem_map', vertexSplitOutsideEdge_not_mem_local,
      or_false, mem_vertexSplitAssignedEdges]
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      vertexSplit_target_outside, vertexSplitOutsideTarget_eq_child_iff]
  · change vertexSplitLocalEdge q qLocal r e ∈ _ ↔ vertexSplitLocalEdge q qLocal r e ∈ _
    simp only [Finset.mem_union, Finset.mem_map', vertexSplitLocalEdge_not_mem_outside, false_or]
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      vertexSplit_target_local]
    rw [← vertexSplitTemplateVertex_child Γ r hq c,
      (Γ.vertexSplitTemplateVertex_injective r hq).eq_iff]

theorem incoming_vertexSplit_child_disjoint (χ : Γ.VertexSplitChoices r) (c : Fin 2) :
    Disjoint ((Γ.vertexSplitAssignedEdges r χ c).map (vertexSplitOutsideEdge q qLocal r))
      ((Θ.incoming (Sum.inl c)).map (vertexSplitLocalEdge q qLocal r)) :=
  vertexSplit_edgeColours_disjoint q qLocal r _ _

/-- An unaffected target receives its unchanged-source old incoming edges together with
the template leg edges routed to it. No single-edge condition on the template is needed. -/
theorem incoming_vertexSplit_old (χ : Γ.VertexSplitChoices r)
    (v : Vertex (n + 1) m) (hv : v ≠ Sum.inl r) :
    (Γ.vertexSplit Θ r hq χ).incoming (vertexSplitOldVertex r v) =
      (Γ.vertexSplitOutsideIncoming r v).map (vertexSplitOutsideEdge q qLocal r) ∪
        (Γ.vertexSplitLegIncoming Θ r hq v).map (vertexSplitLocalEdge q qLocal r) := by
  ext e
  obtain ⟨e, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  rcases e with e | e
  · change vertexSplitOutsideEdge q qLocal r e ∈ _ ↔ vertexSplitOutsideEdge q qLocal r e ∈ _
    simp only [Finset.mem_union, Finset.mem_map', vertexSplitOutsideEdge_not_mem_local,
      or_false, mem_vertexSplitOutsideIncoming]
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      vertexSplit_target_outside, vertexSplitOutsideTarget_eq_old_iff Γ r χ e v hv]
  · change vertexSplitLocalEdge q qLocal r e ∈ _ ↔ vertexSplitLocalEdge q qLocal r e ∈ _
    simp only [Finset.mem_union, Finset.mem_map', vertexSplitLocalEdge_not_mem_outside,
      false_or, mem_vertexSplitLegIncoming]
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      vertexSplit_target_local, vertexSplitTemplateVertex_eq_old_iff Γ r hq _ v hv]

theorem incoming_vertexSplit_old_disjoint (v : Vertex (n + 1) m) :
    Disjoint ((Γ.vertexSplitOutsideIncoming r v).map (vertexSplitOutsideEdge q qLocal r))
      ((Γ.vertexSplitLegIncoming Θ r hq v).map (vertexSplitLocalEdge q qLocal r)) :=
  vertexSplit_edgeColours_disjoint q qLocal r _ _

/-- Distinct old outgoing targets identify the template leg that reaches this target. -/
theorem vertexSplitLegIncoming_target (k : Fin p) :
    Γ.vertexSplitLegIncoming Θ r hq (Γ.target ⟨r, Fin.cast hq.symm k⟩) =
      Θ.incoming (Sum.inr k) := by
  ext e
  simp only [mem_vertexSplitLegIncoming, incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, he, hj⟩
    have hjk := Γ.distinctTargets r hj
    have : j = k := Fin.cast_injective _ hjk
    simpa only [this] using he
  · intro he
    exact ⟨k, he, rfl⟩

/-- Useful specialization for an old outgoing slot: its target receives precisely that
template leg's incoming edges in addition to the unchanged-source old incoming edges. -/
theorem incoming_vertexSplit_leg_target (χ : Γ.VertexSplitChoices r) (k : Fin p) :
    (Γ.vertexSplit Θ r hq χ).incoming
        (vertexSplitOldVertex r (Γ.target ⟨r, Fin.cast hq.symm k⟩)) =
      (Γ.vertexSplitOutsideIncoming r (Γ.target ⟨r, Fin.cast hq.symm k⟩)).map
          (vertexSplitOutsideEdge q qLocal r) ∪
        (Θ.incoming (Sum.inr k)).map (vertexSplitLocalEdge q qLocal r) := by
  rw [incoming_vertexSplit_old Γ Θ r hq χ _ (Γ.noLoops r _), vertexSplitLegIncoming_target]

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
