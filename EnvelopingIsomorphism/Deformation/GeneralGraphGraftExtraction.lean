import EnvelopingIsomorphism.Deformation.GeneralGraphGraftConstruction

/-! Actual extraction and reconstruction of a boundary graph graft.
The cluster is expressed in the explicit outer/inner label order and its
external block is the genuine consecutive graft block. Collapsed parallel
targets are excluded explicitly; their geometric face density vanishes in
the separate boundary-form theorem. -/

noncomputable section
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical

variable {a b m l : ℕ} {q : Fin a → ℕ} {p : Fin b → ℕ}

/-- Every expanded vertex is either in the cluster or an unaffected outer
vertex. The collapsed exterior slot is represented only by the inner side. -/
theorem graftVertex_cases (r : Fin (m + 1)) (v : Vertex (a + b) (m + l + 1)) :
    (∃ u : Vertex a (m + 1), u ≠ Sum.inr r ∧ graftOuterVertex r u = v) ∨
      ∃ u : Vertex b (l + 1), graftInnerVertex r u = v := by
  cases v with
  | inl v =>
    obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective v
    cases u with
    | inl u => exact Or.inl ⟨Sum.inl u, Sum.inl_ne_inr, rfl⟩
    | inr u => exact Or.inr ⟨Sum.inl u, rfl⟩
  | inr v =>
    obtain ⟨u, rfl⟩ := (graftBoundaryEquiv (l := l) r).symm.surjective v
    cases u with
    | inl u => exact Or.inr ⟨Sum.inr u, rfl⟩
    | inr u =>
      exact Or.inl ⟨Sum.inr u.val, fun h ↦ u.property (Sum.inr.inj h), rfl⟩

/-- The entire fibre of the collapsed exterior vertex is exactly the inner
graph's internal vertices and its ordered external block. -/
theorem graftCollapse_eq_slot_iff (r : Fin (m + 1))
    (v : Vertex (a + b) (m + l + 1)) :
    graftCollapse r v = Sum.inr r ↔ ∃ u : Vertex b (l + 1), graftInnerVertex r u = v := by
  constructor
  · intro h
    rcases graftVertex_cases r v with ⟨u, hu, he⟩ | hi
    · subst v
      exact (hu ((graftCollapse_outer r u).symm.trans h)).elim
    · exact hi
  · rintro ⟨u, rfl⟩
    exact graftCollapse_inner r u

/-- Outside the contracted fibre the original vertex is recovered uniquely. -/
theorem graftOuterVertex_collapse (r : Fin (m + 1))
    (v : Vertex (a + b) (m + l + 1)) (hv : graftCollapse r v ≠ Sum.inr r) :
    graftOuterVertex r (graftCollapse r v) = v := by
  rcases graftVertex_cases r v with ⟨u, hu, rfl⟩ | ⟨u, rfl⟩
  · rw [graftCollapse_outer]
  · exact (hv (graftCollapse_inner r u)).elim

namespace Graph

theorem edge_eq_of_source_target_eq {n m : ℕ} {q : Fin n → ℕ} (Γ : Graph q m)
    (e f : Edge q) (hs : e.1 = f.1) (ht : Γ.target e = Γ.target f) : e = f := by
  rcases e with ⟨v, j⟩
  rcases f with ⟨w, t⟩
  dsimp at hs
  subst w
  have he := Γ.distinctTargets v ht
  subst t
  rfl

variable (H : Graph (graftArity q p) (m + l + 1)) (r : Fin (m + 1))

/-- The actual no-outgoing condition on edges whose source belongs to the cluster. -/
def InnerClosed : Prop :=
  ∀ e : Edge p, ∃ v : Vertex b (l + 1), graftInnerVertex r v = H.target (graftInnerEdge q p e)

/-- Admissibility of the contracted outer graph. This condition is necessary:
distinct expanded targets may become parallel after collapsing the cluster. -/
def CoarseDistinct : Prop :=
  ∀ v : Fin a, Function.Injective
    (fun j : Fin (q v) ↦ graftCollapse r (H.target (graftOuterEdge q p ⟨v, j⟩)))

def extractedOuterTarget (e : Edge q) : Vertex a (m + 1) :=
  graftCollapse r (H.target (graftOuterEdge q p e))

def extractedInnerTarget (hc : H.InnerClosed r) (e : Edge p) : Vertex b (l + 1) :=
  Classical.choose (hc e)

theorem extractedInnerTarget_spec (hc : H.InnerClosed r) (e : Edge p) :
    graftInnerVertex r (H.extractedInnerTarget r hc e) = H.target (graftInnerEdge q p e) :=
  Classical.choose_spec (hc e)

/-- The actual inner graph, with every original ordered outgoing slot retained. -/
def extractedInner (hc : H.InnerClosed r) : Graph p (l + 1) where
  target := H.extractedInnerTarget r hc
  noLoops v j h := by
    have ht := H.extractedInnerTarget_spec r hc ⟨v, j⟩
    rw [h] at ht
    exact H.noLoops (graftInnerEdge q p ⟨v, j⟩).1 (graftInnerEdge q p ⟨v, j⟩).2 ht.symm
  distinctTargets v j t ht := by
    have he : H.target (graftInnerEdge q p ⟨v, j⟩) = H.target (graftInnerEdge q p ⟨v, t⟩) :=
      (H.extractedInnerTarget_spec r hc ⟨v, j⟩).symm.trans
        ((congrArg (graftInnerVertex r) ht).trans (H.extractedInnerTarget_spec r hc ⟨v, t⟩))
    have hee := H.edge_eq_of_source_target_eq (graftInnerEdge q p ⟨v, j⟩)
      (graftInnerEdge q p ⟨v, t⟩) rfl he
    have he' := (graftInnerEdge q p).injective hee
    exact Fin.ext (congrArg (fun e : Edge p ↦ e.2.val) he')

/-- The actual outer quotient graph, on its original ordered exterior labels
with the cluster contracted at the specified insertion slot. -/
def extractedOuter (hd : H.CoarseDistinct r) : Graph q (m + 1) where
  target := H.extractedOuterTarget r
  noLoops v j h := by
    change graftCollapse r (H.target (graftOuterEdge q p ⟨v, j⟩)) = Sum.inl v at h
    have hn : graftCollapse r (H.target (graftOuterEdge q p ⟨v, j⟩)) ≠ Sum.inr r := by
      rw [h]
      exact Sum.inl_ne_inr
    have he := graftOuterVertex_collapse r (H.target (graftOuterEdge q p ⟨v, j⟩)) hn
    rw [h] at he
    exact H.noLoops (graftOuterEdge q p ⟨v, j⟩).1 (graftOuterEdge q p ⟨v, j⟩).2 he.symm
  distinctTargets := hd

/-- The actual target of each outer edge entering the contracted cluster. -/
def extractedChoices (hd : H.CoarseDistinct r) :
    (H.extractedOuter r hd).GraftChoices (b := b) (l := l) r :=
  fun e ↦ Classical.choose ((graftCollapse_eq_slot_iff r (H.target (graftOuterEdge q p e.val))).mp e.property)

theorem extractedChoices_spec (hd : H.CoarseDistinct r)
    (e : {e : Edge q // (H.extractedOuter r hd).target e = Sum.inr r}) :
    graftInnerVertex r (H.extractedChoices r hd e) = H.target (graftOuterEdge q p e.val) :=
  Classical.choose_spec ((graftCollapse_eq_slot_iff r (H.target (graftOuterEdge q p e.val))).mp e.property)

/-- Reconstruct the original admissible graph from its actual extracted
quotient, inner graph and incoming-edge assignment. -/
theorem graft_extracted (hc : H.InnerClosed r) (hd : H.CoarseDistinct r) :
    (H.extractedOuter r hd).graft (H.extractedInner r hc) r (H.extractedChoices r hd) = H := by
  apply Graph.ext
  funext e
  obtain ⟨e, rfl⟩ := (graftEdgeEquiv q p).symm.surjective e
  cases e with
  | inl e =>
    change ((H.extractedOuter r hd).graft (H.extractedInner r hc) r (H.extractedChoices r hd)).target
      (graftOuterEdge q p e) = _
    rw [graft_target_outer]
    by_cases he : (H.extractedOuter r hd).target e = Sum.inr r
    · rw [graftOuterTarget, dif_pos he]
      exact H.extractedChoices_spec r hd ⟨e, he⟩
    · rw [graftOuterTarget, dif_neg he]
      exact graftOuterVertex_collapse r (H.target (graftOuterEdge q p e)) he
  | inr e =>
    change ((H.extractedOuter r hd).graft (H.extractedInner r hc) r (H.extractedChoices r hd)).target
      (graftInnerEdge q p e) = _
    rw [graft_target_inner]
    exact H.extractedInnerTarget_spec r hc e

theorem graft_innerClosed (Γ : Graph q (m + 1)) (Δ : Graph p (l + 1))
    (χ : Γ.GraftChoices (b := b) (l := l) r) : (Γ.graft Δ r χ).InnerClosed r := by
  intro e
  exact ⟨Δ.target e, (graft_target_inner Γ Δ r χ e).symm⟩

theorem graft_coarseDistinct (Γ : Graph q (m + 1)) (Δ : Graph p (l + 1))
    (χ : Γ.GraftChoices (b := b) (l := l) r) : (Γ.graft Δ r χ).CoarseDistinct r := by
  intro v j t h
  apply Γ.distinctTargets v
  simpa only [graft_target_outer, collapse_graftOuterTarget] using h

/-- Complete finite graft data, including the actual incoming-edge assignment. -/
abbrev GraftData (q : Fin a → ℕ) (p : Fin b → ℕ) (r : Fin (m + 1)) (l : ℕ) :=
  (Γ : Graph q (m + 1)) × (_ : Graph p (l + 1)) × Γ.GraftChoices (b := b) (l := l) r

def graftDataGraph (D : GraftData q p r l) : Graph (graftArity q p) (m + l + 1) :=
  D.1.graft D.2.1 r D.2.2

/-- With a fixed internal partition and external insertion block, the expanded
graph determines both factor graphs and every incoming-edge choice uniquely. -/
theorem graftDataGraph_injective : Function.Injective (graftDataGraph (q := q) (p := p) r (l := l)) := by
  rintro ⟨Γ, Δ, χ⟩ ⟨Γ', Δ', χ'⟩ h
  have ho : Γ = Γ' := by
    apply Graph.ext
    funext e
    have he := congrArg (fun G : Graph (graftArity q p) (m + l + 1) ↦
      graftCollapse r (G.target (graftOuterEdge q p e))) h
    simpa only [graftDataGraph, graft_target_outer, collapse_graftOuterTarget] using he
  have hi : Δ = Δ' := by
    apply Graph.ext
    funext e
    apply graftInnerVertex_injective r
    have he := congrArg (fun G : Graph (graftArity q p) (m + l + 1) ↦
      G.target (graftInnerEdge q p e)) h
    simpa only [graftDataGraph, graft_target_inner] using he
  subst Γ'
  subst Δ'
  have hc : χ = χ' := by
    funext e
    apply graftInnerVertex_injective r
    have he := congrArg (fun G : Graph (graftArity q p) (m + l + 1) ↦
      G.target (graftOuterEdge q p e.val)) h
    simpa only [graftDataGraph, graft_target_outer, graftOuterTarget, dif_pos e.property] using he
  subst χ'
  rfl

/-- Exact finite extraction/reconstruction bijection on the nonvanishing
combinatorial boundary class. No graft identity is supplied as a premise. -/
def graftExtractionEquiv (q : Fin a → ℕ) (p : Fin b → ℕ) (r : Fin (m + 1)) (l : ℕ) :
    GraftData q p r l ≃
      {H : Graph (graftArity q p) (m + l + 1) // H.InnerClosed r ∧ H.CoarseDistinct r} where
  toFun D := ⟨graftDataGraph r D, graft_innerClosed r D.1 D.2.1 D.2.2,
    graft_coarseDistinct r D.1 D.2.1 D.2.2⟩
  invFun H := ⟨H.val.extractedOuter r H.property.2, H.val.extractedInner r H.property.1,
    H.val.extractedChoices r H.property.2⟩
  left_inv D := by
    apply graftDataGraph_injective r
    exact (graftDataGraph r D).graft_extracted r
      (graft_innerClosed r D.1 D.2.1 D.2.2) (graft_coarseDistinct r D.1 D.2.1 D.2.2)
  right_inv H := Subtype.ext (H.val.graft_extracted r H.property.1 H.property.2)

/-- Extraction of an actual graft recovers the entire dependent datum,
including its original assignment, not only the two underlying graph targets. -/
theorem extract_graft_data (D : GraftData q p r l) :
    (graftExtractionEquiv q p r l).symm (graftExtractionEquiv q p r l D) = D :=
  (graftExtractionEquiv q p r l).symm_apply_apply D

end Graph
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
