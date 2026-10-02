import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLabels

/-! Actual contraction and reconstruction of a two-child internal cluster.
The input is the expanded graph and a list of its exiting edges; the quotient,
local template and all incoming choices are constructed from actual targets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical
variable {n m p : ℕ}

/-- The collapsed internal fibre consists precisely of the two children. -/
theorem vertexSplitCollapse_eq_root_iff (r : Fin (n + 1))
    (v : Vertex (n + 2) m) : vertexSplitCollapseVertex r v = Sum.inl r ↔
      ∃ c : Fin 2, Sum.inl (vertexSplitChild r c) = v := by
  cases v with
  | inr v => simp [vertexSplitCollapseVertex]
  | inl v =>
    obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv r).symm.surjective v
    cases s with
    | inl v =>
      simp only [vertexSplitSourceEquiv_symm_old]
      constructor
      · intro h
        have he : v.val = r := by simpa [vertexSplitCollapseVertex] using h
        exact (v.property he).elim
      · rintro ⟨c, h⟩
        exact (vertexSplitOld_ne_child r v.val v.property c (Sum.inl.inj h).symm).elim
    | inr c =>
      simp only [vertexSplitSourceEquiv_symm_child]
      exact ⟨fun _ ↦ ⟨c, rfl⟩, fun _ ↦ vertexSplitCollapseVertex_child r c⟩

/-- Outside that fibre, collapse followed by the old-vertex inclusion is identity. -/
theorem vertexSplitOldVertex_collapse (r : Fin (n + 1)) (v : Vertex (n + 2) m)
    (hv : vertexSplitCollapseVertex r v ≠ Sum.inl r) :
    vertexSplitOldVertex r (vertexSplitCollapseVertex r v) = v := by
  cases v with
  | inr v => rfl
  | inl v =>
    obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv r).symm.surjective v
    cases s with
    | inl v => simp [vertexSplitCollapseVertex, vertexSplitOldVertex]
    | inr c => exact (hv (vertexSplitCollapseVertex_child r c)).elim

namespace Graph
variable {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (r : Fin (n + 1)) (hq : q r = p)
variable (H : Graph (vertexSplitArity q qLocal r) m)
variable (leg : Fin p → Edge qLocal)

/-- Distinctness required only after actual contraction of the child fibre. -/
def SplitCoarseDistinct : Prop := ∀ (v : Fin (n + 1)) (hv : v ≠ r),
  Function.Injective (fun j : Fin (q v) ↦ vertexSplitCollapseVertex r
    (H.target (vertexSplitOutsideEdge q qLocal r ⟨⟨v, j⟩, hv⟩)))

/-- Every selected leg really leaves the two-child cluster. -/
def SplitLegsOutside : Prop := ∀ j, vertexSplitCollapseVertex r
  (H.target (vertexSplitLocalEdge q qLocal r (leg j))) ≠ Sum.inl r

/-- Distinct quotient targets of the actual selected exiting edges. -/
def SplitLegsDistinct : Prop := Function.Injective (fun j ↦ vertexSplitCollapseVertex r
  (H.target (vertexSplitLocalEdge q qLocal r (leg j))))

/-- Selected exiting edges exhaust actual outgoing targets of the cluster. -/
def SplitLegsComplete : Prop := ∀ e : Edge qLocal,
  vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q qLocal r e)) ≠ Sum.inl r →
  ∃ j, H.target (vertexSplitLocalEdge q qLocal r (leg j)) =
    H.target (vertexSplitLocalEdge q qLocal r e)

def contractedTarget (e : Edge q) : Vertex (n + 1) m :=
  Sum.elim (fun f : VertexSplitOutsideEdge q r ↦
    vertexSplitCollapseVertex r (H.target (vertexSplitOutsideEdge q qLocal r f)))
    (fun j ↦ vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q qLocal r (leg j))))
    (vertexSplitOldEdgeEquiv q r hq e)

@[simp] theorem contractedTarget_outside (e : VertexSplitOutsideEdge q r) :
    contractedTarget r hq H leg e.val =
      vertexSplitCollapseVertex r (H.target (vertexSplitOutsideEdge q qLocal r e)) := by
  simp [contractedTarget]

@[simp] theorem contractedTarget_root (j : Fin p) :
    contractedTarget r hq H leg ⟨r, Fin.cast hq.symm j⟩ =
      vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q qLocal r (leg j))) := by
  simp [contractedTarget]

/-- Genuine quotient graph, with all unaffected slots retained and the root
slots supplied by the actual exiting edge list. -/
def contractedGraph (hd : H.SplitCoarseDistinct r) (ho : H.SplitLegsOutside r leg)
    (hl : H.SplitLegsDistinct r leg) : Graph q m where
  target := contractedTarget r hq H leg
  noLoops v j h := by
    by_cases hv : v = r
    · subst v
      have hh := contractedTarget_root r hq H leg (Fin.cast hq j)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at hh
      exact ho (Fin.cast hq j) (hh.symm.trans h)
    · have hh := contractedTarget_outside r hq H leg ⟨⟨v, j⟩, hv⟩
      have hc : vertexSplitCollapseVertex r
          (H.target (vertexSplitOutsideEdge q qLocal r ⟨⟨v,j⟩,hv⟩)) = Sum.inl v := hh.symm.trans h
      have hn : vertexSplitCollapseVertex r
          (H.target (vertexSplitOutsideEdge q qLocal r ⟨⟨v,j⟩,hv⟩)) ≠ Sum.inl r := by
        rw [hc]; exact fun h ↦ hv (Sum.inl.inj h)
      have he := vertexSplitOldVertex_collapse r _ hn
      rw [hc] at he
      exact H.noLoops _ _ he.symm
  distinctTargets v j k h := by
    by_cases hv : v = r
    · subst v
      have hj := contractedTarget_root r hq H leg (Fin.cast hq j)
      have hk := contractedTarget_root r hq H leg (Fin.cast hq k)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at hj hk
      exact Fin.cast_injective hq (hl (hj.symm.trans (h.trans hk)))
    · exact hd v hv ((contractedTarget_outside r hq H leg ⟨⟨v,j⟩,hv⟩).symm.trans
        (h.trans (contractedTarget_outside r hq H leg ⟨⟨v,k⟩,hv⟩)))

variable (hd : H.SplitCoarseDistinct r) (ho : H.SplitLegsOutside r leg)
    (hl : H.SplitLegsDistinct r leg)

/-- Incoming choices are read from the original target child, never supplied. -/
def contractedChoices : (contractedGraph r hq H leg hd ho hl).VertexSplitChoices r := by
  intro e
  have hs := (contractedGraph r hq H leg hd ho hl).vertexSplit_incoming_source_ne r e.val e.property
  have ht : vertexSplitCollapseVertex r
      (H.target (vertexSplitOutsideEdge q qLocal r ⟨e.val, hs⟩)) = Sum.inl r :=
    (contractedTarget_outside r hq H leg ⟨e.val, hs⟩).symm.trans e.property
  exact ((vertexSplitCollapse_eq_root_iff r _).mp ht).choose

theorem contractedChoices_spec
    (e : {e : Edge q // (contractedGraph r hq H leg hd ho hl).target e = Sum.inl r})
    (hs : e.val.1 ≠ r) :
    Sum.inl (vertexSplitChild r (contractedChoices r hq H leg hd ho hl e)) =
      H.target (vertexSplitOutsideEdge q qLocal r ⟨e.val, hs⟩) := by
  exact ((vertexSplitCollapse_eq_root_iff r _).mp
    ((contractedTarget_outside r hq H leg ⟨e.val, hs⟩).symm.trans e.property)).choose_spec

variable (hc : H.SplitLegsComplete r leg)

/-- The local template is recovered by inspecting each original child edge. -/
def contractedTemplateTarget (e : Edge qLocal) : Vertex 2 p :=
  if h : vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q qLocal r e)) = Sum.inl r
  then Sum.inl (((vertexSplitCollapse_eq_root_iff r _).mp h).choose)
  else Sum.inr ((hc e h).choose)

theorem contractedTemplateTarget_spec (e : Edge qLocal) :
    (contractedGraph r hq H leg hd ho hl).vertexSplitTemplateVertex r hq
      (contractedTemplateTarget r H leg hc e) = H.target (vertexSplitLocalEdge q qLocal r e) := by
  by_cases h : vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q qLocal r e)) = Sum.inl r
  · rw [contractedTemplateTarget, dif_pos h, vertexSplitTemplateVertex_child]
    exact ((vertexSplitCollapse_eq_root_iff r _).mp h).choose_spec
  · rw [contractedTemplateTarget, dif_neg h, vertexSplitTemplateVertex_leg]
    change vertexSplitOldVertex r (contractedTarget r hq H leg _) = _
    rw [contractedTarget_root, (hc e h).choose_spec]
    exact vertexSplitOldVertex_collapse r _ h

/-- The actual local graph has the original child valencies, no loops and
distinct targets. These facts follow from the expanded graph. -/
def contractedTemplate : Graph qLocal p where
  target := contractedTemplateTarget r H leg hc
  noLoops v j h := by
    have ht := contractedTemplateTarget_spec r hq H leg hd ho hl hc ⟨v,j⟩
    rw [h, vertexSplitTemplateVertex_child] at ht
    exact H.noLoops _ _ ht.symm
  distinctTargets v j k h := by
    have ht : H.target (vertexSplitLocalEdge q qLocal r ⟨v,j⟩) =
        H.target (vertexSplitLocalEdge q qLocal r ⟨v,k⟩) :=
      (contractedTemplateTarget_spec r hq H leg hd ho hl hc ⟨v,j⟩).symm.trans
        ((congrArg ((contractedGraph r hq H leg hd ho hl).vertexSplitTemplateVertex r hq) h).trans
          (contractedTemplateTarget_spec r hq H leg hd ho hl hc ⟨v,k⟩))
    have hs := H.distinctTargets (vertexSplitChild r v) ht
    apply Fin.ext
    exact (vertexSplitLocalEdge_slot_val q qLocal r ⟨v,j⟩).symm.trans
      ((congrArg Fin.val hs).trans (vertexSplitLocalEdge_slot_val q qLocal r ⟨v,k⟩))

@[simp] theorem contractedTemplate_target_leg (j : Fin p) :
    (contractedTemplate r hq H leg hd ho hl hc).target (leg j) = Sum.inr j := by
  change contractedTemplateTarget r H leg hc (leg j) = Sum.inr j
  rw [contractedTemplateTarget, dif_neg (ho j)]
  apply congrArg Sum.inr
  apply hl
  exact congrArg (vertexSplitCollapseVertex r) (hc (leg j) (ho j)).choose_spec

theorem contractedTemplate_target_child (e : Edge qLocal) (c : Fin 2)
    (he : H.target (vertexSplitLocalEdge q qLocal r e) = Sum.inl (vertexSplitChild r c)) :
    (contractedTemplate r hq H leg hd ho hl hc).target e = Sum.inl c := by
  apply (contractedGraph r hq H leg hd ho hl).vertexSplitTemplateVertex_injective r hq
  exact (contractedTemplateTarget_spec r hq H leg hd ho hl hc e).trans he

/-- Splitting the extracted quotient by the extracted template with the
extracted incoming choices recovers the literal original target function. -/
theorem vertexSplit_contracted :
    (contractedGraph r hq H leg hd ho hl).vertexSplit
      (contractedTemplate r hq H leg hd ho hl hc) r hq
      (contractedChoices r hq H leg hd ho hl) = H := by
  apply Graph.ext
  funext e
  obtain ⟨e, rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  cases e with
  | inl e =>
    change ((contractedGraph r hq H leg hd ho hl).vertexSplit
      (contractedTemplate r hq H leg hd ho hl hc) r hq
      (contractedChoices r hq H leg hd ho hl)).target (vertexSplitOutsideEdge q qLocal r e) = _
    rw [vertexSplit_target_outside]
    by_cases he : (contractedGraph r hq H leg hd ho hl).target e.val = Sum.inl r
    · rw [vertexSplitOutsideTarget, dif_pos he]
      exact contractedChoices_spec r hq H leg hd ho hl ⟨e.val, he⟩ e.property
    · rw [vertexSplitOutsideTarget, dif_neg he]
      change vertexSplitOldVertex r (contractedTarget r hq H leg e.val) = _
      rw [contractedTarget_outside]
      apply vertexSplitOldVertex_collapse
      simpa only [contractedGraph, contractedTarget_outside] using he
  | inr e =>
    change ((contractedGraph r hq H leg hd ho hl).vertexSplit
      (contractedTemplate r hq H leg hd ho hl hc) r hq
      (contractedChoices r hq H leg hd ho hl)).target (vertexSplitLocalEdge q qLocal r e) = _
    rw [vertexSplit_target_local]
    exact contractedTemplateTarget_spec r hq H leg hd ho hl hc e

end Graph
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
