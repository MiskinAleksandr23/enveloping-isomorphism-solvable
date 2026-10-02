import EnvelopingIsomorphism.Deformation.GeneralGraphSlotRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

/-! Actual dependent outgoing-slot covariance of grafts. Incoming assignments
are transported by the genuine outgoing-edge bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General
open scoped Classical BigOperators
variable {a b m l : ℕ} {q : Fin a → ℕ} {p : Fin b → ℕ}

def graftOutgoing (α : (v : Fin a) → Equiv.Perm (Fin (q v)))
    (β : (v : Fin b) → Equiv.Perm (Fin (p v))) :
    (v : Fin (a+b)) → Equiv.Perm (Fin (graftArity q p v)) :=
  Fin.addCases (fun v ↦ (finCongr (graftArity_outer q p v)).symm.permCongr (α v))
    (fun v ↦ (finCongr (graftArity_inner q p v)).symm.permCongr (β v))

theorem graftOutgoing_outer (α : (v : Fin a) → Equiv.Perm (Fin (q v)))
    (β : (v : Fin b) → Equiv.Perm (Fin (p v))) (e : Edge q) :
    outgoingEdgePerm (graftOutgoing α β) (graftOuterEdge q p e) =
      graftOuterEdge q p (outgoingEdgePerm α e) := by
  rcases e with ⟨v,j⟩
  rw [graftOuterEdge_mk, graftOuterEdge_mk]
  simp only [outgoingEdgePerm_apply]
  apply congrArg (Sigma.mk (Fin.castAdd b v))
  simp [graftOutgoing, outgoingEdgePerm, Equiv.permCongr_def]

theorem graftOutgoing_inner (α : (v : Fin a) → Equiv.Perm (Fin (q v)))
    (β : (v : Fin b) → Equiv.Perm (Fin (p v))) (e : Edge p) :
    outgoingEdgePerm (graftOutgoing α β) (graftInnerEdge q p e) =
      graftInnerEdge q p (outgoingEdgePerm β e) := by
  rcases e with ⟨v,j⟩
  rw [graftInnerEdge_mk, graftInnerEdge_mk]
  simp only [outgoingEdgePerm_apply]
  apply congrArg (Sigma.mk (Fin.natAdd a v))
  simp [graftOutgoing, outgoingEdgePerm, Equiv.permCongr_def]

theorem graftOutgoing_sign (α : (v : Fin a) → Equiv.Perm (Fin (q v)))
    (β : (v : Fin b) → Equiv.Perm (Fin (p v))) :
    (∏ v, permutationSign (R := ℝ) (graftOutgoing α β v)) =
      (∏ v, permutationSign (R := ℝ) (α v)) * (∏ v, permutationSign (R := ℝ) (β v)) := by
  rw [Fin.prod_univ_add]
  simp [graftOutgoing, permutationSign, Equiv.Perm.sign_permCongr]

def outerOutgoing (τ : (v : Fin (a+b)) → Equiv.Perm (Fin (graftArity q p v)))
    (v : Fin a) : Equiv.Perm (Fin (q v)) :=
  (finCongr (graftArity_outer q p v)).permCongr (τ (Fin.castAdd b v))

def innerOutgoing (τ : (v : Fin (a+b)) → Equiv.Perm (Fin (graftArity q p v)))
    (v : Fin b) : Equiv.Perm (Fin (p v)) :=
  (finCongr (graftArity_inner q p v)).permCongr (τ (Fin.natAdd a v))

theorem graftOutgoing_restrict (τ : (v : Fin (a+b)) → Equiv.Perm (Fin (graftArity q p v))) :
    graftOutgoing (outerOutgoing τ) (innerOutgoing τ) = τ := by
  funext v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v <;>
    apply Equiv.ext <;> intro j <;>
    simp [graftOutgoing, outerOutgoing, innerOutgoing, Equiv.permCongr_def]

namespace Graph

def outgoingIncomingEquiv (Γ : Graph q (m+1)) (r : Fin (m+1))
    (α : (v : Fin a) → Equiv.Perm (Fin (q v))) :
    {e : Edge q // (Γ.permuteOutgoing α).target e = Sum.inr r} ≃
      {e : Edge q // Γ.target e = Sum.inr r} :=
  Equiv.subtypeEquiv (outgoingEdgePerm α) (by intro e; rfl)

def outgoingGraftChoices (Γ : Graph q (m+1)) (r : Fin (m+1))
    (α : (v : Fin a) → Equiv.Perm (Fin (q v))) (χ : Γ.GraftChoices (b := b) (l := l) r) :
    (Γ.permuteOutgoing α).GraftChoices (b := b) (l := l) r := fun e ↦ χ (Γ.outgoingIncomingEquiv r α e)

theorem graft_permuteOutgoing (Γ : Graph q (m+1)) (Δ : Graph p (l+1))
    (r : Fin (m+1)) (χ : Γ.GraftChoices (b := b) (l := l) r)
    (α : (v : Fin a) → Equiv.Perm (Fin (q v))) (β : (v : Fin b) → Equiv.Perm (Fin (p v))) :
    (Γ.graft Δ r χ).permuteOutgoing (graftOutgoing α β) =
      (Γ.permuteOutgoing α).graft (Δ.permuteOutgoing β) r (Γ.outgoingGraftChoices r α χ) := by
  apply Graph.ext
  funext e
  obtain ⟨e,rfl⟩ := (graftEdgeEquiv q p).symm.surjective e
  cases e with
  | inl e =>
    change (Γ.graft Δ r χ).target (outgoingEdgePerm (graftOutgoing α β) (graftOuterEdge q p e)) =
      ((Γ.permuteOutgoing α).graft (Δ.permuteOutgoing β) r (Γ.outgoingGraftChoices r α χ)).target (graftOuterEdge q p e)
    rw [graftOutgoing_outer, graft_target_outer, graft_target_outer]
    unfold graftOuterTarget
    by_cases he : Γ.target (outgoingEdgePerm α e) = Sum.inr r
    · simp only [permuteOutgoing, dif_pos he]
      rfl
    · simp only [permuteOutgoing, dif_neg he]
  | inr e =>
    change (Γ.graft Δ r χ).target (outgoingEdgePerm (graftOutgoing α β) (graftInnerEdge q p e)) =
      ((Γ.permuteOutgoing α).graft (Δ.permuteOutgoing β) r (Γ.outgoingGraftChoices r α χ)).target (graftInnerEdge q p e)
    rw [graftOutgoing_inner, graft_target_inner, graft_target_inner]
    rfl
end Graph

namespace SlotRelabelling
variable {n N M : ℕ} {q : Fin n → ℕ} {p : Fin N → ℕ}
  {Γ : Graph q M} {Δ : Graph p M}

/-- Conjugate an actual outgoing family across the slot-preserving incidence
map. The displayed arity equality is the one supplied by the chart carrier. -/
def pullOutgoing (F : SlotRelabelling Γ Δ) (h : ∀ v, q v = p (F.vertices v))
    (τ : (v : Fin N) → Equiv.Perm (Fin (p v))) (v : Fin n) : Equiv.Perm (Fin (q v)) :=
  (finCongr (h v)).symm.permCongr (τ (F.vertices v))

theorem pullOutgoing_edges (F : SlotRelabelling Γ Δ) (h : ∀ v, q v = p (F.vertices v))
    (τ : (v : Fin N) → Equiv.Perm (Fin (p v))) (e : Edge q) :
    F.edges (outgoingEdgePerm (F.pullOutgoing h τ) e) = outgoingEdgePerm τ (F.edges e) := by
  apply edge_eq_of_source_slot
  · rw [F.source]
    exact (F.source e).symm
  · rw [F.slot]
    rcases e with ⟨v,j⟩
    have he : F.edges ⟨v,j⟩ = ⟨F.vertices v, Fin.cast (h v) j⟩ :=
      edge_eq_of_source_slot (F.source _) (F.slot _)
    rw [he]
    simp [outgoingEdgePerm_apply, pullOutgoing, Equiv.permCongr_def]

def permuteOutgoing (F : SlotRelabelling Γ Δ) (h : ∀ v, q v = p (F.vertices v))
    (τ : (v : Fin N) → Equiv.Perm (Fin (p v))) :
    SlotRelabelling (Γ.permuteOutgoing (F.pullOutgoing h τ)) (Δ.permuteOutgoing τ) where
  vertices := F.vertices
  edges := F.edges
  source := F.source
  slot := F.slot
  target e := by
    change Δ.target (outgoingEdgePerm τ (F.edges e)) = _
    rw [← F.pullOutgoing_edges h τ, F.target]
    rfl

theorem pullOutgoing_sign (F : SlotRelabelling Γ Δ) (h : ∀ v, q v = p (F.vertices v))
    (τ : (v : Fin N) → Equiv.Perm (Fin (p v))) :
    (∏ v, permutationSign (R := ℝ) (F.pullOutgoing h τ v)) =
      ∏ v, permutationSign (R := ℝ) (τ v) := by
  simp only [pullOutgoing, permutationSign, Equiv.Perm.sign_permCongr]
  exact F.vertices.prod_comp (fun v ↦ permutationSign (R := ℝ) (τ v))

end SlotRelabelling
end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
