import EnvelopingIsomorphism.Deformation.UniformCurvatureTargets
import EnvelopingIsomorphism.Deformation.BinaryVertexContraction
import EnvelopingIsomorphism.Deformation.GraphCurvatureCyclicFibres

/-! Actual outgoing covariance of normalized two-child curvature splits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.UniformCurvatureOutgoing
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits UniformCurvatureTargets
open BinaryVertexContraction GraphCurvatureProfiles
open scoped Classical BigOperators

/-- Reorder the receiver's two legs, keeping the sender's last leg fixed. -/
def receiverPermutation (β : Equiv.Perm (Fin 2)) : Equiv.Perm (Fin 3) :=
  ((finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm.trans
    (Equiv.sumCongr β (Equiv.refl _))).trans finSumFinEquiv

@[simp] theorem receiverPermutation_first (β : Equiv.Perm (Fin 2)) (j : Fin 2) :
    receiverPermutation β j.castSucc = (β j).castSucc := by
  change receiverPermutation β ((finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) (Sum.inl j)) =
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) (Sum.inl (β j))
  simp only [receiverPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]

@[simp] theorem receiverPermutation_last (β : Equiv.Perm (Fin 2)) : receiverPermutation β 2 = 2 := by
  change receiverPermutation β (finSumFinEquiv (Sum.inr (0 : Fin 1))) = finSumFinEquiv (Sum.inr (0 : Fin 1))
  simp only [receiverPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

theorem receiverPermutation_sign {R : Type*} [CommRing R] (β : Equiv.Perm (Fin 2)) :
    permutationSign (R := R) (receiverPermutation β) = permutationSign β := by
  have h : Equiv.Perm.sign (receiverPermutation β) = Equiv.Perm.sign β := by
    exact (Equiv.Perm.sign_symm_trans_trans (Equiv.sumCongr β (Equiv.refl (Fin 1)))
      (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)).trans (by simp)
  simp only [permutationSign, h]

private theorem permutationSign_cast {R : Type*} [CommRing R] {b c : ℕ} (h : b = c)
    (ρ : Equiv.Perm (Fin c)) :
    permutationSign (R := R) ((finCongr h).trans (ρ.trans (finCongr h).symm)) = permutationSign ρ := by
  unfold permutationSign
  congr 2
  exact Equiv.Perm.sign_trans_trans_symm ρ (finCongr h)

variable {n : ℕ} (i : Fin (n + 1)) (a : Fin 2)
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2))

abbrev receiver : Fin 2 := Equiv.swap 0 1 a

/-- The actual quotient permutation: every outside row is retained, the
receiver's two slots become root slots zero and one, and root slot two stays fixed. -/
def quotientOutgoing (v : Fin (n + 1)) : Equiv.Perm (Fin (UniformCurvatureTargets.Arity i v)) :=
  if hv : v = i then
    let e := finCongr ((congrArg (UniformCurvatureTargets.Arity i) hv).trans (selectedArity i).symm)
    e.trans ((receiverPermutation (τ (vertexSplitChild i (receiver a)))).trans e.symm)
  else
    let e := finCongr (outsideArity i v hv)
    e.trans ((τ (vertexSplitOldEmbedding i v)).trans e.symm)

@[simp] theorem quotientOutgoing_root (j : Fin 3) :
    quotientOutgoing i a τ i (Fin.cast (selectedArity i) j) =
      Fin.cast (selectedArity i) (receiverPermutation (τ (vertexSplitChild i (receiver a))) j) := by
  simp [quotientOutgoing]

@[simp] theorem quotientOutgoing_outside (v : Fin (n + 1)) (hv : v ≠ i) (j : Fin 2) :
    quotientOutgoing i a τ v (Fin.cast (outsideArity i v hv).symm j) =
      Fin.cast (outsideArity i v hv).symm (τ (vertexSplitOldEmbedding i v) j) := by
  simp [quotientOutgoing, hv]

/-- The induced quotient has exactly the full expanded outgoing sign when
the sender's already-normalized internal slot is fixed. -/
theorem quotientOutgoing_sign {R : Type*} [CommRing R]
    (hτ : τ (vertexSplitChild i a) = Equiv.refl _) :
    (∏ v, permutationSign (R := R) (quotientOutgoing i a τ v)) =
      ∏ v, permutationSign (R := R) (τ v) := by
  have hs (v : Fin (n + 1)) : permutationSign (R := R) (quotientOutgoing i a τ v) =
      if v = i then permutationSign (τ (vertexSplitChild i (receiver a)))
      else permutationSign (τ (vertexSplitOldEmbedding i v)) := by
    by_cases hv : v = i
    · subst v
      simp only [quotientOutgoing, dif_pos rfl, if_pos rfl, dite_true, ite_true]
      rw [permutationSign_cast, receiverPermutation_sign]
    · simp only [quotientOutgoing, dif_neg hv, if_neg hv]
      exact permutationSign_cast _ _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin (n + 1) ↦ v = i)]
  simp only [hs]
  have hp (x : {v : Fin (n + 1) // v = i}) :
      (if x.val = i then permutationSign (R := R) (τ (vertexSplitChild i (receiver a)))
      else permutationSign (τ (vertexSplitOldEmbedding i x.val))) =
        permutationSign (τ (vertexSplitChild i (receiver a))) := if_pos x.property
  have hn (x : {v : Fin (n + 1) // v ≠ i}) :
      (if x.val = i then permutationSign (R := R) (τ (vertexSplitChild i (receiver a)))
      else permutationSign (τ (vertexSplitOldEmbedding i x.val))) =
        permutationSign (τ (vertexSplitOldEmbedding i x.val)) := if_neg x.property
  simp only [hp, hn, Finset.prod_const, Finset.card_univ, Fintype.card_subtype_eq, pow_one]
  rw [← Equiv.prod_comp (vertexSplitSourceEquiv i).symm (fun v ↦ permutationSign (R := R) (τ v))]
  simp only [Fintype.prod_sum_type, vertexSplitSourceEquiv_symm_old, vertexSplitSourceEquiv_symm_child]
  have hc : (∏ c : Fin 2, permutationSign (R := R) (τ (vertexSplitChild i c))) =
      permutationSign (τ (vertexSplitChild i (receiver a))) := by
    fin_cases a <;> simp_all [Fin.prod_univ_two, receiver, permutationSign]
  rw [hc]
  exact mul_comm (G := R) _ _

/-- The template has one internal arrow in sender slot zero. -/
theorem canonicalTemplate_sender_zero : (canonicalTemplate a).target ⟨a,0⟩ = Sum.inl (receiver a) := by
  fin_cases a <;> rfl

/-- The sender's remaining arrow is always the last quotient leg. -/
theorem canonicalTemplate_sender_one : (canonicalTemplate a).target ⟨a,1⟩ = Sum.inr 2 := by
  fin_cases a <;> rfl

/-- The receiver carries the first two quotient legs in its actual slot order. -/
theorem canonicalTemplate_receiver (j : Fin 2) :
    (canonicalTemplate a).target ⟨receiver a,j⟩ = Sum.inr j.castSucc := by
  fin_cases a <;> fin_cases j <;> rfl

def outgoingDataEquiv : Equiv.Perm (CurvatureSplitData i) :=
  splitDataOutgoingEquiv i (quotientOutgoing i a τ)

def canonicalDataGraph (D : CurvatureSplitData i) : BinaryGraph (n + 2) 3 :=
  uniformSplit i D.1 (canonicalTemplate a) D.2

/-- Root target evaluation after the actual outgoing relabelling. -/
theorem quotient_root_target (D : CurvatureSplitData i) (j : Fin 3) :
    (outgoingDataEquiv i a τ D).1.target ⟨i,Fin.cast (selectedArity i) j⟩ =
      D.1.target ⟨i,Fin.cast (selectedArity i)
        (receiverPermutation (τ (vertexSplitChild i (receiver a))) j)⟩ := by
  change D.1.target ⟨i,quotientOutgoing i a τ i (Fin.cast (selectedArity i) j)⟩ = _
  rw [quotientOutgoing_root]

/-- Arbitrary outgoing permutations fixing the sender's internal slot are
realized by an actual equivalence of quotient graphs and incoming choices. -/
theorem canonicalDataGraph_outgoing (hτ : τ (vertexSplitChild i a) = Equiv.refl _)
    (D : CurvatureSplitData i) :
    canonicalDataGraph i a (outgoingDataEquiv i a τ D) = (canonicalDataGraph i a D).permuteOutgoing τ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,s⟩
  change Fin 2 at s
  obtain ⟨v,rfl⟩ := (vertexSplitSourceEquiv i).symm.surjective v
  cases v with
  | inl v =>
    change (uniformSplit i _ _ _).target ⟨vertexSplitOldEmbedding i v.val,s⟩ =
      (uniformSplit i D.1 (canonicalTemplate a) D.2).target
        ⟨vertexSplitOldEmbedding i v.val,τ (vertexSplitOldEmbedding i v.val) s⟩
    rw [target_outside i _ _ _ v.val v.property, target_outside i _ _ _ v.val v.property]
    change (splitDataOutgoingEquiv i (quotientOutgoing i a τ) D).1.vertexSplitOutsideTarget i
      (splitDataOutgoingEquiv i (quotientOutgoing i a τ) D).2 _ = _
    rw [splitDataOutgoingEquiv_outsideTarget]
    congr 2
    exact congrArg (fun j : Fin (UniformCurvatureTargets.Arity i v.val) ↦
      (⟨v.val,j⟩ : Edge (UniformCurvatureTargets.Arity i)))
      (quotientOutgoing_outside i a τ v.val v.property s)
  | inr c =>
    change Fin 2 at s
    change (uniformSplit i _ _ _).target ⟨vertexSplitChild i c,s⟩ =
      (uniformSplit i D.1 (canonicalTemplate a) D.2).target
        ⟨vertexSplitChild i c,τ (vertexSplitChild i c) s⟩
    rw [target_child, target_child]
    by_cases hc : c = a
    · subst c
      rw [hτ]
      change _ = D.1.vertexSplitTemplateVertex i (selectedArity i).symm ((canonicalTemplate a).target ⟨a,s⟩)
      have hs : s = 0 ∨ s = 1 := by omega
      rcases hs with hs | hs
      · rw [hs, canonicalTemplate_sender_zero]
        rfl
      · rw [hs, canonicalTemplate_sender_one, vertexSplitTemplateVertex_leg, vertexSplitTemplateVertex_leg,
          quotient_root_target, receiverPermutation_last]
    · have hca : c = receiver a := by fin_cases a <;> fin_cases c <;> simp_all [receiver]
      subst c
      rw [canonicalTemplate_receiver, canonicalTemplate_receiver,
        vertexSplitTemplateVertex_leg, vertexSplitTemplateVertex_leg, quotient_root_target,
        receiverPermutation_first]

end EnvelopingIsomorphism.Deformation.UniformCurvatureOutgoing
