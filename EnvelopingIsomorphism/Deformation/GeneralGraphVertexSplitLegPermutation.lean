import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitFibres
import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles

/-! Exact reindexing of quotient slots and external template legs, including
all incoming choices. This is an equivalence of actual split data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical
variable {n m p : ℕ} {q : Fin (n + 1) → ℕ}

/-- Permute only the outgoing slots of the contracted root. -/
def rootOutgoing (r : Fin (n + 1)) (hq : q r = p) (ρ : Equiv.Perm (Fin p))
    (v : Fin (n + 1)) : Equiv.Perm (Fin (q v)) :=
  if h : v = r then
    let e := finCongr ((congrArg q h).trans hq)
    e.trans (ρ.trans e.symm)
  else Equiv.refl _

@[simp] theorem rootOutgoing_root (r : Fin (n + 1)) (hq : q r = p)
    (ρ : Equiv.Perm (Fin p)) (j : Fin (q r)) :
    rootOutgoing r hq ρ r j = Fin.cast hq.symm (ρ (Fin.cast hq j)) := by
  simp [rootOutgoing]

@[simp] theorem rootOutgoing_other (r : Fin (n + 1)) (hq : q r = p)
    (ρ : Equiv.Perm (Fin p)) (v : Fin (n + 1)) (hv : v ≠ r) :
    rootOutgoing r hq ρ v = Equiv.refl _ := by simp [rootOutgoing, hv]

/-- A root-slot permutation retains precisely its own sign after transport
through the dependent arity equality; every other vertex contributes one. -/
theorem rootOutgoing_sign {R : Type*} [CommRing R] (r : Fin (n + 1)) (hq : q r = p)
    (ρ : Equiv.Perm (Fin p)) :
    (∏ v, permutationSign (R := R) (rootOutgoing r hq ρ v)) = permutationSign ρ := by
  have hs (v : Fin (n + 1)) : permutationSign (R := R) (rootOutgoing r hq ρ v) =
      if v = r then permutationSign ρ else 1 := by
    by_cases hv : v = r
    · subst v
      simp only [rootOutgoing, dif_pos rfl, if_pos rfl, permutationSign]
      congr 2
      exact Equiv.Perm.sign_trans_trans_symm ρ (finCongr hq)
    · simp [rootOutgoing_other r hq ρ v hv, hv, permutationSign]
  simp only [hs, Fintype.prod_ite_eq']

namespace Graph

/-- Any outgoing reordering transports incoming choice functions through the
literal edge permutation. -/
def splitDataOutgoingEquiv (r : Fin (n + 1))
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) :
    Equiv.Perm (VertexSplitData q m r) :=
  Equiv.sigmaCongr (outgoingGraphEquiv q m τ) (fun Γ ↦
    Equiv.arrowCongr (Equiv.subtypeEquiv (outgoingEdgePerm τ).symm
      (fun e ↦ by
        change Γ.target e = Sum.inl r ↔ Γ.target (outgoingEdgePerm τ ((outgoingEdgePerm τ).symm e)) = Sum.inl r
        rw [Equiv.apply_symm_apply])) (Equiv.refl _))

@[simp] theorem splitDataOutgoingEquiv_graph (r : Fin (n + 1))
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) (D : VertexSplitData q m r) :
    (splitDataOutgoingEquiv r τ D).1 = D.1.permuteOutgoing τ := rfl

@[simp] theorem splitDataOutgoingEquiv_choice (r : Fin (n + 1))
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) (D : VertexSplitData q m r)
    (e : {e : Edge q // (D.1.permuteOutgoing τ).target e = Sum.inl r}) :
    (splitDataOutgoingEquiv r τ D).2 e = D.2 ⟨outgoingEdgePerm τ e.val, e.property⟩ := rfl

theorem splitDataOutgoingEquiv_outsideTarget (r : Fin (n + 1))
    (τ : (v : Fin (n + 1)) → Equiv.Perm (Fin (q v))) (D : VertexSplitData q m r)
    (e : VertexSplitOutsideEdge q r) :
    (splitDataOutgoingEquiv r τ D).1.vertexSplitOutsideTarget r (splitDataOutgoingEquiv r τ D).2 e =
      D.1.vertexSplitOutsideTarget r D.2 ⟨outgoingEdgePerm τ e.val, e.property⟩ := by
  simp only [vertexSplitOutsideTarget, splitDataOutgoingEquiv_graph, permuteOutgoing]
  split_ifs with h
  · rfl
  · rfl

/-- External leg labels are permuted without altering template sources or slots. -/
def relabelLegs {qLocal : Fin 2 → ℕ} (Θ : Graph qLocal p) (ρ : Equiv.Perm (Fin p)) : Graph qLocal p where
  target e := Sum.map id ρ (Θ.target e)
  noLoops v j h := by
    have hh : Function.Injective (Sum.map (id : Fin 2 → Fin 2) ρ) :=
      Sum.map_injective.mpr ⟨Function.injective_id, ρ.injective⟩
    exact Θ.noLoops v j (hh h)
  distinctTargets v j k h := Θ.distinctTargets v
    ((Sum.map_injective.mpr ⟨Function.injective_id, ρ.injective⟩) h)

variable {qLocal : Fin 2 → ℕ} (r : Fin (n + 1)) (hq : q r = p)
    (Θ : Graph qLocal p) (ρ : Equiv.Perm (Fin p))

/-- Root slot relabelling and template leg relabelling produce exactly the
same expanded graph. All dependent incoming assignments are transported. -/
theorem vertexSplitDataGraph_rootOutgoing (D : VertexSplitData q m r) :
    vertexSplitDataGraph Θ r hq (splitDataOutgoingEquiv r (rootOutgoing r hq ρ) D) =
      vertexSplitDataGraph (Θ.relabelLegs ρ) r hq D := by
  apply Graph.ext
  funext e
  obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q qLocal r).symm.surjective e
  cases e with
  | inl e =>
    change ((D.1.permuteOutgoing (rootOutgoing r hq ρ)).vertexSplit Θ r hq _).target
      (vertexSplitOutsideEdge q qLocal r e) =
      (D.1.vertexSplit (Θ.relabelLegs ρ) r hq D.2).target (vertexSplitOutsideEdge q qLocal r e)
    rw [vertexSplit_target_outside, vertexSplit_target_outside]
    have he : outgoingEdgePerm (rootOutgoing r hq ρ) e.val = e.val := by
      rcases e with ⟨⟨v,j⟩,hv⟩
      simp [outgoingEdgePerm_apply, rootOutgoing_other r hq ρ v hv]
    simp only [vertexSplitOutsideTarget, Graph.permuteOutgoing, he]
    split_ifs with h
    · rw [splitDataOutgoingEquiv_choice]
      congr 2
      exact congrArg D.2 (Subtype.ext he)
    · rfl
  | inr e =>
    change ((D.1.permuteOutgoing (rootOutgoing r hq ρ)).vertexSplit Θ r hq _).target
      (vertexSplitLocalEdge q qLocal r e) =
      (D.1.vertexSplit (Θ.relabelLegs ρ) r hq D.2).target (vertexSplitLocalEdge q qLocal r e)
    rw [vertexSplit_target_local, vertexSplit_target_local]
    cases ht : Θ.target e with
    | inl c => simp [relabelLegs, ht, vertexSplitTemplateVertex]
    | inr j =>
      simp only [vertexSplitTemplateVertex, relabelLegs, ht, Sum.map_inr, Sum.elim_inr,
        Graph.permuteOutgoing, outgoingEdgePerm_apply, rootOutgoing_root, Fin.cast_cast, Fin.cast_eq_self]

end Graph
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
