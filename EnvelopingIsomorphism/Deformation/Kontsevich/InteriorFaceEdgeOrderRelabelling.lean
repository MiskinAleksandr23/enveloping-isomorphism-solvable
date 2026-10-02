import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceFactorization

/-! Native edge partition ordering depends only on the internal-edge
predicate, including after the genuine dimension casts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeOrderRelabelling
open InteriorGraphFaceCoordinates
open scoped Classical

private def enumIndex {D k : ℕ} (P : Fin D → Prop)
    (hc : Fintype.card {j // P j} = k) (j : Fin k) : Fin D :=
  ((Fintype.equivFinOfCardEq hc).symm j).val

private theorem enumIndex_eq {D k : ℕ} (P Q : Fin D → Prop) (hp : P = Q)
    (hc : Fintype.card {j // P j} = k) (hd : Fintype.card {j // Q j} = k) (j : Fin k) :
    enumIndex P hc j = enumIndex Q hd j := by
  subst Q
  rfl

private def complementIndex {D k : ℕ} (P : Fin D → Prop)
    (hc : Fintype.card {j // ¬P j} = k) (j : Fin k) : Fin D :=
  ((Fintype.equivFinOfCardEq hc).symm j).val

private theorem complementIndex_eq {D k : ℕ} (P Q : Fin D → Prop) (hp : P = Q)
    (hc : Fintype.card {j // ¬P j} = k) (hd : Fintype.card {j // ¬Q j} = k) (j : Fin k) :
    complementIndex P hc j = complementIndex Q hd j := by
  subst Q
  rfl

private theorem complement_card {r s : ℕ} (P : Fin (r+s) → Prop)
    (hc : Fintype.card {j // P j} = r) : Fintype.card {j // ¬P j} = s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hc]
  omega

private def blockOrder {r s : ℕ} (P : Fin (r+s) → Prop)
    (hc : Fintype.card {j // P j} = r) : Equiv.Perm (Fin (r+s)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Fintype.equivFinOfCardEq hc).symm
      (Fintype.equivFinOfCardEq (complement_card P hc)).symm).trans (Equiv.sumCompl P))

private theorem blockOrder_eq {r s : ℕ} (P Q : Fin (r+s) → Prop) (hp : P = Q)
    (hc : Fintype.card {j // P j} = r) (hd : Fintype.card {j // Q j} = r) :
    blockOrder (s := s) P hc = blockOrder Q hd := by
  subst Q
  rfl

variable {r s r' s' n m n' m' : ℕ}
    {S : Finset (Fin n)} {T : Finset (Fin n')}
    (es : Fin (r+s) → Edge n m) (fs : Fin (r'+s') → Edge n' m')
    (hr : r' = r) (hs : s' = s) (ht : r'+s' = r+s)
    (he : ∀ j, IsInternal T (fs j) ↔ IsInternal S (es (finCongr ht j)))
    (hc : Fintype.card {j // IsInternal S (es j)} = r)

include hr hs ht he hc in
theorem card_internal_transport : Fintype.card {j // IsInternal T (fs j)} = r' := by
  let e : {j // IsInternal T (fs j)} ≃ {j // IsInternal S (es j)} :=
    Equiv.subtypeEquiv (finCongr ht) he
  exact (Fintype.card_congr e).trans (hc.trans hr.symm)

include hr hs ht he in
theorem internalIndex_transport
    (hc' : Fintype.card {j // IsInternal T (fs j)} = r') (j : Fin r') :
    internalIndex es hc (finCongr hr j) = finCongr ht (internalIndex fs hc' j) := by
  subst r'
  subst s'
  have hp : (fun j ↦ IsInternal S (es j)) = (fun j ↦ IsInternal T (fs j)) :=
    funext (fun j ↦ propext (he j).symm)
  change enumIndex (fun j ↦ IsInternal S (es j)) hc j =
    enumIndex (fun j ↦ IsInternal T (fs j)) hc' j
  exact enumIndex_eq _ _ hp hc hc' j

include hr hs ht he in
theorem externalIndex_transport
    (hc' : Fintype.card {j // IsInternal T (fs j)} = r') (j : Fin s') :
    externalIndex es hc (finCongr hs j) = finCongr ht (externalIndex fs hc' j) := by
  subst r'
  subst s'
  have hp : (fun j ↦ IsInternal S (es j)) = (fun j ↦ IsInternal T (fs j)) :=
    funext (fun j ↦ propext (he j).symm)
  change complementIndex (fun j ↦ IsInternal S (es j)) (external_card es hc) j =
    complementIndex (fun j ↦ IsInternal T (fs j)) (external_card fs hc') j
  exact complementIndex_eq _ _ hp (external_card es hc) (external_card fs hc') j

include hr hs ht he in
theorem edgeBlockPermutation_sign_transport
    (hc' : Fintype.card {j // IsInternal T (fs j)} = r') :
    (edgeBlockPermutation fs hc').sign = (edgeBlockPermutation es hc).sign := by
  subst r'
  subst s'
  have hp : (fun j ↦ IsInternal S (es j)) = (fun j ↦ IsInternal T (fs j)) :=
    funext (fun j ↦ propext (he j).symm)
  change (blockOrder (fun j ↦ IsInternal T (fs j)) hc').sign =
    (blockOrder (fun j ↦ IsInternal S (es j)) hc).sign
  exact congrArg Equiv.Perm.sign (blockOrder_eq _ _ hp hc hc').symm

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceEdgeOrderRelabelling
