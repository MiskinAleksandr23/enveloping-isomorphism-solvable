import EnvelopingIsomorphism.Deformation.BinarySplitOutgoingCovariance
import EnvelopingIsomorphism.Deformation.MixedGraphSourceFibres

/-! Genuine outgoing covariance for a vector-bivector split. The forward
template permits all binary receiver permutations; the backward template
retains precisely the stabilizer of its binary sender row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.VectorSplitOutgoingCovariance
open scoped Classical BigOperators
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open BinarySplitOutgoingCovariance (slotCast slotCast_sign)
variable {n m : ℕ} {q : Fin (n+1) → ℕ} (r : Fin (n+1)) (hq : q r = 2)

def template (a : Fin 2) : Graph vectorBivectorArity 2 :=
  if a = 0 then vectorBivectorForward else vectorBivectorBackward 1

variable (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (vertexSplitArity q vectorBivectorArity r v)))

def childOutgoing (c : Fin 2) : Equiv.Perm (Fin (vectorBivectorArity c)) :=
  slotCast (vertexSplitArity_child q vectorBivectorArity r c).symm (τ (vertexSplitChild r c))

theorem childOutgoing_vector : childOutgoing r τ 0 = Equiv.refl _ := by
  change (childOutgoing r τ 0 : Equiv.Perm (Fin 1)) = Equiv.refl _
  exact @Subsingleton.elim (Equiv.Perm (Fin 1)) inferInstance _ _

def outsideOutgoing (v : Fin (n+1)) (hv : v ≠ r) : Equiv.Perm (Fin (q v)) :=
  slotCast (vertexSplitArity_old q vectorBivectorArity r v hv).symm (τ (vertexSplitOldEmbedding r v))

def rootPermutation (a : Fin 2) : Equiv.Perm (Fin 2) :=
  if a = 0 then childOutgoing r τ 1 else Equiv.refl _

def quotientOutgoing (a : Fin 2) (v : Fin (n+1)) : Equiv.Perm (Fin (q v)) :=
  if hv : v = r then slotCast ((congrArg q hv).trans hq) (rootPermutation r τ a)
  else outsideOutgoing r τ v hv

@[simp] theorem quotientOutgoing_root (a : Fin 2) (j : Fin 2) :
    quotientOutgoing r hq τ a r (Fin.cast hq.symm j) =
      Fin.cast hq.symm (rootPermutation r τ a j) := by
  simp [quotientOutgoing]

@[simp] theorem quotientOutgoing_outside (a : Fin 2) (v : Fin (n+1)) (hv : v ≠ r) :
    quotientOutgoing r hq τ a v = outsideOutgoing r τ v hv := by
  simp [quotientOutgoing, hv]

theorem outgoing_localEdge (e : Edge vectorBivectorArity) :
    outgoingEdgePerm τ (vertexSplitLocalEdge q vectorBivectorArity r e) =
      vertexSplitLocalEdge q vectorBivectorArity r (outgoingEdgePerm (childOutgoing r τ) e) := by
  rcases e with ⟨c,j⟩
  apply SlotRelabelling.edge_eq_of_source_slot
  · simp only [outgoingEdgePerm_apply, vertexSplitLocalEdge_source]
    rfl
  · change (τ (vertexSplitChild r c) (vertexSplitLocalEdge q vectorBivectorArity r ⟨c,j⟩).2).val = _
    rw [vertexSplitLocalEdge_slot_val]
    have hj : (vertexSplitLocalEdge q vectorBivectorArity r ⟨c,j⟩).2 =
        Fin.cast (vertexSplitArity_child q vectorBivectorArity r c).symm j :=
      Fin.ext (vertexSplitLocalEdge_slot_val q vectorBivectorArity r ⟨c,j⟩)
    rw [hj]
    rfl

theorem outgoing_outsideEdge (a : Fin 2) (e : VertexSplitOutsideEdge q r) :
    outgoingEdgePerm τ (vertexSplitOutsideEdge q vectorBivectorArity r e) =
      vertexSplitOutsideEdge q vectorBivectorArity r
        ⟨outgoingEdgePerm (quotientOutgoing r hq τ a) e.val,e.property⟩ := by
  rcases e with ⟨⟨v,j⟩,hv⟩
  apply SlotRelabelling.edge_eq_of_source_slot
  · simp only [outgoingEdgePerm_apply, vertexSplitOutsideEdge_source]
    rfl
  · change (τ (vertexSplitOldEmbedding r v)
      (vertexSplitOutsideEdge q vectorBivectorArity r ⟨⟨v,j⟩,hv⟩).2).val = _
    rw [vertexSplitOutsideEdge_slot_val]
    have hj : (vertexSplitOutsideEdge q vectorBivectorArity r ⟨⟨v,j⟩,hv⟩).2 =
        Fin.cast (vertexSplitArity_old q vectorBivectorArity r v hv).symm j :=
      Fin.ext (vertexSplitOutsideEdge_slot_val q vectorBivectorArity r ⟨⟨v,j⟩,hv⟩)
    rw [hj]
    simp only [outgoingEdgePerm_apply]
    rw [quotientOutgoing_outside r hq τ a v hv]
    rfl

theorem template_outgoing (a : Fin 2)
    (hτ : a ≠ 0 → childOutgoing r τ 1 = Equiv.refl _) (e : Edge vectorBivectorArity) :
    (template a).target (outgoingEdgePerm (childOutgoing r τ) e) =
      Sum.map id (rootPermutation r τ a) ((template a).target e) := by
  rcases e with ⟨c,j⟩
  fin_cases a
  · fin_cases c
    · simp only [outgoingEdgePerm_apply, childOutgoing_vector, Equiv.refl_apply]
      rfl
    · rfl
  · have ht := hτ (by decide)
    have hh : childOutgoing r τ = fun c ↦ Equiv.refl (Fin (vectorBivectorArity c)) := by
      funext c
      fin_cases c
      · exact childOutgoing_vector r τ
      · exact ht
    rw [hh]
    change (template 1).target ⟨c,j⟩ = Sum.map id id ((template 1).target ⟨c,j⟩)
    simp

def dataEquiv (a : Fin 2) : Equiv.Perm (VertexSplitData q m r) :=
  splitDataOutgoingEquiv r (quotientOutgoing r hq τ a)

theorem dataGraph_outgoing (a : Fin 2)
    (hτ : a ≠ 0 → childOutgoing r τ 1 = Equiv.refl _)
    (D : VertexSplitData q m r) :
    vertexSplitDataGraph (template a) r hq (dataEquiv r hq τ a D) =
      (vertexSplitDataGraph (template a) r hq D).permuteOutgoing τ := by
  apply Graph.ext
  funext e
  obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q vectorBivectorArity r).symm.surjective e
  cases e with
  | inl e =>
    change ((dataEquiv r hq τ a D).1.vertexSplit (template a) r hq _).target
      (vertexSplitOutsideEdge q vectorBivectorArity r e) =
      (D.1.vertexSplit (template a) r hq D.2).target
        (outgoingEdgePerm τ (vertexSplitOutsideEdge q vectorBivectorArity r e))
    rw [outgoing_outsideEdge, vertexSplit_target_outside, vertexSplit_target_outside]
    exact splitDataOutgoingEquiv_outsideTarget r (quotientOutgoing r hq τ a) D e
  | inr e =>
    change ((dataEquiv r hq τ a D).1.vertexSplit (template a) r hq _).target
      (vertexSplitLocalEdge q vectorBivectorArity r e) =
      (D.1.vertexSplit (template a) r hq D.2).target
        (outgoingEdgePerm τ (vertexSplitLocalEdge q vectorBivectorArity r e))
    rw [outgoing_localEdge, vertexSplit_target_local, vertexSplit_target_local,
      template_outgoing r τ a hτ]
    cases (template a).target e with
    | inl c => rfl
    | inr j =>
      simp only [Sum.map_inr, vertexSplitTemplateVertex_leg]
      change vertexSplitOldVertex r (D.1.target ⟨r, quotientOutgoing r hq τ a r (Fin.cast hq.symm j)⟩) = _
      rw [quotientOutgoing_root]

theorem quotientOutgoing_sign {R : Type*} [CommRing R] (a : Fin 2)
    (hτ : a ≠ 0 → childOutgoing r τ 1 = Equiv.refl _) :
    (∏ v, permutationSign (R := R) (quotientOutgoing r hq τ a v)) =
      ∏ v, permutationSign (R := R) (τ v) := by
  have hr : rootPermutation r τ a = childOutgoing r τ 1 := by
    by_cases ha : a = 0
    · simp [rootPermutation, ha]
    · exact (show rootPermutation r τ a = Equiv.refl _ from if_neg ha).trans (hτ ha).symm
  have hs (v : Fin (n+1)) : permutationSign (R := R) (quotientOutgoing r hq τ a v) =
      if v = r then permutationSign (childOutgoing r τ 1)
      else permutationSign (τ (vertexSplitOldEmbedding r v)) := by
    by_cases hv : v = r
    · subst v
      simp [quotientOutgoing, slotCast_sign, hr]
    · simp [quotientOutgoing, hv, outsideOutgoing, slotCast_sign]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin (n+1) ↦ v = r)]
  simp only [hs]
  have hp (x : {v : Fin (n+1) // v = r}) :
      (if x.val = r then permutationSign (R := R) (childOutgoing r τ 1)
      else permutationSign (τ (vertexSplitOldEmbedding r x.val))) =
        permutationSign (childOutgoing r τ 1) := if_pos x.property
  have hn (x : {v : Fin (n+1) // v ≠ r}) :
      (if x.val = r then permutationSign (R := R) (childOutgoing r τ 1)
      else permutationSign (τ (vertexSplitOldEmbedding r x.val))) =
        permutationSign (τ (vertexSplitOldEmbedding r x.val)) := if_neg x.property
  simp only [hp, hn, Finset.prod_const, Finset.card_univ, Fintype.card_subtype_eq, pow_one]
  rw [← Equiv.prod_comp (vertexSplitSourceEquiv r).symm (fun v ↦ permutationSign (R := R) (τ v))]
  simp only [Fintype.prod_sum_type, vertexSplitSourceEquiv_symm_old, vertexSplitSourceEquiv_symm_child]
  have hc (c : Fin 2) : permutationSign (R := R) (τ (vertexSplitChild r c)) =
      permutationSign (childOutgoing r τ c) := (slotCast_sign _ _).symm
  simp only [hc, Fin.prod_univ_two, childOutgoing_vector]
  rw [show permutationSign (R := R) (Equiv.refl (Fin (vectorBivectorArity 0))) = 1 by
    simp [permutationSign], one_mul]
  exact mul_comm _ _

end EnvelopingIsomorphism.Deformation.VectorSplitOutgoingCovariance
