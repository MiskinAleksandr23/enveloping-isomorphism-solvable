import EnvelopingIsomorphism.Deformation.UniformCurvatureOutgoing
import EnvelopingIsomorphism.Deformation.GeneralGraphSlotRelabelling

/-! Outgoing covariance of a binary two-child split with arbitrary outside
arities. The quotient root has three slots; outside vertices may include the
retained vector of the mixed correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.BinarySplitOutgoingCovariance
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open BinaryVertexContraction UniformCurvatureOutgoing
open scoped Classical BigOperators
variable {n m : ℕ} {q : Fin (n + 1) → ℕ} (r : Fin (n + 1)) (hq : q r = 3)

/-- Conjugation through an actual equality of slot counts. -/
def slotCast {b c : ℕ} (h : b = c) (τ : Equiv.Perm (Fin c)) : Equiv.Perm (Fin b) :=
  (finCongr h).trans (τ.trans (finCongr h).symm)

@[simp] theorem slotCast_apply {b c : ℕ} (h : b = c) (τ : Equiv.Perm (Fin c)) (j : Fin b) :
    slotCast h τ j = Fin.cast h.symm (τ (Fin.cast h j)) := rfl

theorem slotCast_sign {R : Type*} [CommRing R] {b c : ℕ} (h : b = c) (τ : Equiv.Perm (Fin c)) :
    permutationSign (R := R) (slotCast h τ) = permutationSign τ := by
  unfold permutationSign slotCast
  congr 2
  exact Equiv.Perm.sign_trans_trans_symm τ (finCongr h)

variable (τ : (v : Fin (n + 2)) → Equiv.Perm (Fin (vertexSplitArity q bivectorArity r v)))

def childOutgoing (c : Fin 2) : Equiv.Perm (Fin 2) :=
  slotCast (vertexSplitArity_child q bivectorArity r c).symm (τ (vertexSplitChild r c))

def outsideOutgoing (v : Fin (n + 1)) (hv : v ≠ r) : Equiv.Perm (Fin (q v)) :=
  slotCast (vertexSplitArity_old q bivectorArity r v hv).symm (τ (vertexSplitOldEmbedding r v))

def quotientOutgoing (a : Fin 2) (v : Fin (n + 1)) : Equiv.Perm (Fin (q v)) :=
  if hv : v = r then
    slotCast ((congrArg q hv).trans hq) (receiverPermutation (childOutgoing r τ (receiver a)))
  else outsideOutgoing r τ v hv

@[simp] theorem quotientOutgoing_root (a : Fin 2) (j : Fin 3) :
    quotientOutgoing r hq τ a r (Fin.cast hq.symm j) =
      Fin.cast hq.symm (receiverPermutation (childOutgoing r τ (receiver a)) j) := by
  simp [quotientOutgoing]

@[simp] theorem quotientOutgoing_outside (a : Fin 2) (v : Fin (n + 1)) (hv : v ≠ r) :
    quotientOutgoing r hq τ a v = outsideOutgoing r τ v hv := by simp [quotientOutgoing,hv]

/-- The actual expanded outgoing permutation acts on a local edge through
its conjugated two-slot child permutation. -/
theorem outgoing_localEdge (e : Edge bivectorArity) :
    outgoingEdgePerm τ (vertexSplitLocalEdge q bivectorArity r e) =
      vertexSplitLocalEdge q bivectorArity r (outgoingEdgePerm (childOutgoing r τ) e) := by
  rcases e with ⟨c,j⟩
  apply SlotRelabelling.edge_eq_of_source_slot
  · simp only [outgoingEdgePerm_apply,vertexSplitLocalEdge_source]
    rfl
  · change (τ (vertexSplitChild r c) (vertexSplitLocalEdge q bivectorArity r ⟨c,j⟩).2).val = _
    rw [vertexSplitLocalEdge_slot_val]
    have hj : (vertexSplitLocalEdge q bivectorArity r ⟨c,j⟩).2 =
        Fin.cast (vertexSplitArity_child q bivectorArity r c).symm j := by
      apply Fin.ext
      exact vertexSplitLocalEdge_slot_val q bivectorArity r ⟨c,j⟩
    rw [hj]
    rfl

theorem outgoing_outsideEdge (a : Fin 2) (e : VertexSplitOutsideEdge q r) :
    outgoingEdgePerm τ (vertexSplitOutsideEdge q bivectorArity r e) =
      vertexSplitOutsideEdge q bivectorArity r
        ⟨outgoingEdgePerm (quotientOutgoing r hq τ a) e.val,e.property⟩ := by
  rcases e with ⟨⟨v,j⟩,hv⟩
  apply SlotRelabelling.edge_eq_of_source_slot
  · simp only [outgoingEdgePerm_apply,vertexSplitOutsideEdge_source]
    rfl
  · change (τ (vertexSplitOldEmbedding r v) (vertexSplitOutsideEdge q bivectorArity r ⟨⟨v,j⟩,hv⟩).2).val = _
    rw [vertexSplitOutsideEdge_slot_val]
    have hj : (vertexSplitOutsideEdge q bivectorArity r ⟨⟨v,j⟩,hv⟩).2 =
        Fin.cast (vertexSplitArity_old q bivectorArity r v hv).symm j := by
      apply Fin.ext
      exact vertexSplitOutsideEdge_slot_val q bivectorArity r ⟨⟨v,j⟩,hv⟩
    rw [hj]
    simp only [outgoingEdgePerm_apply]
    rw [quotientOutgoing_outside r hq τ a v hv]
    rfl

def dataEquiv (a : Fin 2) : Equiv.Perm (VertexSplitData q m r) :=
  splitDataOutgoingEquiv r (quotientOutgoing r hq τ a)

/-- Exact graph covariance with arbitrary outside valencies. -/
theorem dataGraph_outgoing (a : Fin 2) (hτ : childOutgoing r τ a = Equiv.refl _)
    (D : VertexSplitData q m r) :
    vertexSplitDataGraph (canonicalTemplate a) r hq (dataEquiv r hq τ a D) =
      (vertexSplitDataGraph (canonicalTemplate a) r hq D).permuteOutgoing τ := by
  apply Graph.ext
  funext e
  obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q bivectorArity r).symm.surjective e
  cases e with
  | inl e =>
    change ((dataEquiv r hq τ a D).1.vertexSplit (canonicalTemplate a) r hq _).target
      (vertexSplitOutsideEdge q bivectorArity r e) =
      (D.1.vertexSplit (canonicalTemplate a) r hq D.2).target
        (outgoingEdgePerm τ (vertexSplitOutsideEdge q bivectorArity r e))
    rw [outgoing_outsideEdge r hq τ a,vertexSplit_target_outside,vertexSplit_target_outside]
    exact splitDataOutgoingEquiv_outsideTarget r (quotientOutgoing r hq τ a) D e
  | inr e =>
    change ((dataEquiv r hq τ a D).1.vertexSplit (canonicalTemplate a) r hq _).target
      (vertexSplitLocalEdge q bivectorArity r e) =
      (D.1.vertexSplit (canonicalTemplate a) r hq D.2).target
        (outgoingEdgePerm τ (vertexSplitLocalEdge q bivectorArity r e))
    rw [outgoing_localEdge,vertexSplit_target_local,vertexSplit_target_local]
    rcases e with ⟨c,j⟩
    change Fin 2 at j
    by_cases hc : c = a
    · subst c
      simp only [outgoingEdgePerm_apply,hτ,Equiv.refl_apply]
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with hj | hj
      · rw [hj,canonicalTemplate_sender_zero]
        rfl
      · rw [hj,canonicalTemplate_sender_one,vertexSplitTemplateVertex_leg,vertexSplitTemplateVertex_leg]
        change vertexSplitOldVertex r (D.1.target ⟨r,quotientOutgoing r hq τ a r (Fin.cast hq.symm 2)⟩) = _
        rw [quotientOutgoing_root,receiverPermutation_last]
    · have hca : c = receiver a := by fin_cases a <;> fin_cases c <;> simp_all [receiver]
      subst c
      simp only [outgoingEdgePerm_apply,canonicalTemplate_receiver,
        vertexSplitTemplateVertex_leg]
      change vertexSplitOldVertex r (D.1.target ⟨r,quotientOutgoing r hq τ a r (Fin.cast hq.symm j.castSucc)⟩) = _
      rw [quotientOutgoing_root,receiverPermutation_first]

theorem quotientOutgoing_sign {R : Type*} [CommRing R] (a : Fin 2)
    (hτ : childOutgoing r τ a = Equiv.refl _) :
    (∏ v, permutationSign (R := R) (quotientOutgoing r hq τ a v)) =
      ∏ v, permutationSign (R := R) (τ v) := by
  have hs (v : Fin (n + 1)) : permutationSign (R := R) (quotientOutgoing r hq τ a v) =
      if v = r then permutationSign (childOutgoing r τ (receiver a))
      else permutationSign (τ (vertexSplitOldEmbedding r v)) := by
    by_cases hv : v = r
    · subst v
      simp [quotientOutgoing,slotCast_sign,receiverPermutation_sign]
    · simp [quotientOutgoing,hv,outsideOutgoing,slotCast_sign]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin (n + 1) ↦ v = r)]
  simp only [hs]
  have hp (x : {v : Fin (n + 1) // v = r}) :
      (if x.val = r then permutationSign (R := R) (childOutgoing r τ (receiver a))
      else permutationSign (τ (vertexSplitOldEmbedding r x.val))) =
        permutationSign (childOutgoing r τ (receiver a)) := if_pos x.property
  have hn (x : {v : Fin (n + 1) // v ≠ r}) :
      (if x.val = r then permutationSign (R := R) (childOutgoing r τ (receiver a))
      else permutationSign (τ (vertexSplitOldEmbedding r x.val))) =
        permutationSign (τ (vertexSplitOldEmbedding r x.val)) := if_neg x.property
  simp only [hp,hn,Finset.prod_const,Finset.card_univ,Fintype.card_subtype_eq,pow_one]
  rw [← Equiv.prod_comp (vertexSplitSourceEquiv r).symm (fun v ↦ permutationSign (R := R) (τ v))]
  simp only [Fintype.prod_sum_type,vertexSplitSourceEquiv_symm_old,vertexSplitSourceEquiv_symm_child]
  have hc (c : Fin 2) : permutationSign (R := R) (τ (vertexSplitChild r c)) =
      permutationSign (childOutgoing r τ c) := (slotCast_sign _ _).symm
  simp only [hc]
  have hprod : (∏ c : Fin 2, permutationSign (R := R) (childOutgoing r τ c)) =
      permutationSign (childOutgoing r τ (receiver a)) := by
    fin_cases a <;> simp_all [Fin.prod_univ_two,receiver,permutationSign]
  rw [hprod]
  exact mul_comm _ _

end EnvelopingIsomorphism.Deformation.BinarySplitOutgoingCovariance
