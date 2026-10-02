import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLabels
import EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles

/-! Exact fibres of a fixed actual internal split template. The graph targets
recover the quotient and each incoming child assignment, so no multiplicity
is lost when a boundary graph is identified with its split data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
open scoped BigOperators Classical
open GraphCoefficientProfiles
variable {n m p : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (Θ : Graph qLocal p) (leg : Fin p → Edge qLocal)
variable (hleg : ∀ j, Θ.target (leg j) = Sum.inr j)
variable (r : Fin (n + 1)) (hq : q r = p)

/-- Collapse of the genuinely embedded old edge recovers its old target. -/
theorem collapse_vertexSplitOldEdge_target (Γ : Graph q m) (χ : Γ.VertexSplitChoices r)
    (e : Edge q) :
    vertexSplitCollapseVertex r
      ((Γ.vertexSplit Θ r hq χ).target (Θ.vertexSplitOldEdge leg hleg q r hq e)) =
      Γ.target e := by
  obtain ⟨s, rfl⟩ := (vertexSplitOldEdgeEquiv q r hq).symm.surjective e
  cases s with
  | inl e =>
    rw [vertexSplitOldEdgeEquiv_symm_outside, vertexSplitOldEdge_outside,
      vertexSplit_target_outside, collapse_vertexSplitOutsideTarget]
  | inr j =>
    rw [vertexSplitOldEdgeEquiv_symm_root, vertexSplitOldEdge_root,
      vertexSplit_target_local, hleg, vertexSplitTemplateVertex_leg,
      vertexSplitCollapseVertex_old]

abbrev VertexSplitData (q : Fin (n + 1) → ℕ) (m : ℕ) (r : Fin (n + 1)) :=
  (Γ : Graph q m) × Γ.VertexSplitChoices r

def vertexSplitDataGraph (D : VertexSplitData q m r) : Graph (vertexSplitArity q qLocal r) m :=
  D.1.vertexSplit Θ r hq D.2

include leg hleg

/-- A fixed template with a genuine edge at every leg has injective split data. -/
theorem vertexSplitDataGraph_injective :
    Function.Injective (vertexSplitDataGraph (m := m) Θ r hq) := by
  rintro ⟨Γ, χ⟩ ⟨Γ', χ'⟩ he
  have hg : Γ = Γ' := by
    apply Graph.ext
    funext e
    have ht := congrArg (fun H : Graph (vertexSplitArity q qLocal r) m =>
      vertexSplitCollapseVertex r (H.target (Θ.vertexSplitOldEdge leg hleg q r hq e))) he
    simpa only [vertexSplitDataGraph, collapse_vertexSplitOldEdge_target] using ht
  subst Γ'
  have hc : χ = χ' := by
    funext e
    have hs := Γ.vertexSplit_incoming_source_ne r e.val e.property
    have ht := congrArg (fun H : Graph (vertexSplitArity q qLocal r) m =>
      H.target (vertexSplitOutsideEdge q qLocal r ⟨e.val, hs⟩)) he
    simp only [vertexSplitDataGraph, vertexSplit_target_outside,
      vertexSplitOutsideTarget, dif_pos e.property] at ht
    exact vertexSplitChild_injective r (Sum.inl.inj ht)
  subst χ'
  rfl

variable {k : Type*} [CommRing k]

/-- The scalar fibre of any given quotient/choice pair contains exactly its weight. -/
theorem vertexSplitProfile_at_split (w : VertexSplitData q m r → k)
    (D : VertexSplitData q m r) :
    pushforward (vertexSplitDataGraph Θ r hq) w (vertexSplitDataGraph Θ r hq D) = w D := by
  have hinj := vertexSplitDataGraph_injective (m := m) Θ leg hleg r hq
  simp only [pushforward, hinj.eq_iff]
  simp

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
