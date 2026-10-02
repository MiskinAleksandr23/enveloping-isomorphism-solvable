import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility
import EnvelopingIsomorphism.Deformation.BinarySplitOutgoingCovariance

/-! Actual binary-child faces are outgoing permutations of fixed canonical
templates, with arbitrary outside valencies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BinaryTemplateOrbitReconstruction
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction BinaryVertexContraction
open TwoPointSplitFaceContraction
open scoped Classical
variable {n m : ℕ} {q : Fin (n + 1) → ℕ} (r : Fin (n + 1))

def senderSwap (c s : Fin 2) (w : Fin (n + 2)) :
    Equiv.Perm (Fin (vertexSplitArity q bivectorArity r w)) :=
  if hw : w = vertexSplitChild r c then
    BinarySplitOutgoingCovariance.slotCast
      ((congrArg (vertexSplitArity q bivectorArity r) hw).trans (vertexSplitArity_child q bivectorArity r c))
      (Equiv.swap 0 s)
  else Equiv.refl _

def localSwap (c s : Fin 2) (a : Fin 2) : Equiv.Perm (Fin (bivectorArity a)) :=
  if a = c then Equiv.swap 0 s else Equiv.refl _

theorem senderSwap_local (c s : Fin 2) (e : KontsevichGraph.General.Edge bivectorArity) :
    outgoingEdgePerm (senderSwap (q := q) r c s) (vertexSplitLocalEdge q bivectorArity r e) =
      vertexSplitLocalEdge q bivectorArity r (outgoingEdgePerm (localSwap c s) e) := by
  rcases e with ⟨a,j⟩
  apply SlotRelabelling.edge_eq_of_source_slot
  · simp only [outgoingEdgePerm_apply, vertexSplitLocalEdge_source]
    rfl
  · have hj : (vertexSplitLocalEdge q bivectorArity r ⟨a,j⟩).2 =
        Fin.cast (vertexSplitArity_child q bivectorArity r a).symm j := by
      apply Fin.ext
      exact vertexSplitLocalEdge_slot_val q bivectorArity r ⟨a,j⟩
    change ((senderSwap (q := q) r c s (vertexSplitChild r a))
      (vertexSplitLocalEdge q bivectorArity r ⟨a,j⟩).2).val = _
    rw [hj]
    by_cases ha : a = c
    · subst a
      simp [senderSwap, BinarySplitOutgoingCovariance.slotCast_apply, localSwap,
        outgoingEdgePerm_apply, vertexSplitLocalEdge_slot_val]
    · have hne : vertexSplitChild r a ≠ vertexSplitChild r c := fun he => ha (vertexSplitChild_injective r he)
      simp [senderSwap, hne, localSwap, ha, outgoingEdgePerm_apply, vertexSplitLocalEdge_slot_val]

theorem senderSwap_outside (c s : Fin 2) (e : VertexSplitOutsideEdge q r) :
    outgoingEdgePerm (senderSwap (q := q) r c s) (vertexSplitOutsideEdge q bivectorArity r e) =
      vertexSplitOutsideEdge q bivectorArity r e := by
  apply SlotRelabelling.edge_eq_of_source_slot
  · rfl
  · change ((senderSwap (q := q) r c s (vertexSplitOldEmbedding r e.val.1))
      (vertexSplitOutsideEdge q bivectorArity r e).2).val = _
    simp only [senderSwap, dif_neg (vertexSplitOld_ne_child r e.val.1 e.property c), Equiv.refl_apply]

theorem localSwap_internal (c s : Fin 2) :
    outgoingEdgePerm (localSwap c s) ⟨c,0⟩ = ⟨c,s⟩ := by
  simp [outgoingEdgePerm_apply, localSwap]

theorem senderSwap_involutive (c s : Fin 2) (w : Fin (n + 2)) :
    Function.Involutive (senderSwap (q := q) r c s w) := by
  intro j
  by_cases hw : w = vertexSplitChild r c
  · simp [senderSwap, hw, BinarySplitOutgoingCovariance.slotCast_apply]
  · simp [senderSwap, hw]

variable (H : Graph (vertexSplitArity q bivectorArity r) m) (D : Data r H)
    (c s : Fin 2)
    (hu : ∀ e : KontsevichGraph.General.Edge bivectorArity,
      vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q bivectorArity r e)) = Sum.inl r ↔ e = ⟨c,s⟩)

def normalized : Graph (vertexSplitArity q bivectorArity r) m := H.permuteOutgoing (senderSwap r c s)

include hu in
theorem normalized_unique : UniqueInternal r (normalized r H c s) c := by
  intro e
  change vertexSplitCollapseVertex r (H.target
    (outgoingEdgePerm (senderSwap r c s) (vertexSplitLocalEdge q bivectorArity r e))) = Sum.inl r ↔ _
  rw [senderSwap_local, hu]
  rw [← localSwap_internal c s, (outgoingEdgePerm (localSwap c s)).injective.eq_iff]

include D in
theorem normalized_coarse : (normalized r H c s).SplitCoarseDistinct r := by
  intro w hw j k he
  apply D.coarse w hw
  change vertexSplitCollapseVertex r (H.target (outgoingEdgePerm (senderSwap r c s)
    (vertexSplitOutsideEdge q bivectorArity r ⟨⟨w,j⟩,hw⟩))) =
    vertexSplitCollapseVertex r (H.target (outgoingEdgePerm (senderSwap r c s)
      (vertexSplitOutsideEdge q bivectorArity r ⟨⟨w,k⟩,hw⟩))) at he
  simpa only [senderSwap_outside] using he

include D hu in
theorem normalized_exits : ExitsDistinct r (normalized r H c s) c := by
  intro e f he hf h
  apply (outgoingEdgePerm (localSwap c s)).injective
  apply D.exits
  · intro hh
    have hh' := (hu _).mp hh
    exact he ((outgoingEdgePerm (localSwap c s)).injective (hh'.trans (localSwap_internal c s).symm))
  · intro hh
    have hh' := (hu _).mp hh
    exact hf ((outgoingEdgePerm (localSwap c s)).injective (hh'.trans (localSwap_internal c s).symm))
  · change vertexSplitCollapseVertex r (H.target (outgoingEdgePerm (senderSwap r c s)
      (vertexSplitLocalEdge q bivectorArity r e))) =
      vertexSplitCollapseVertex r (H.target (outgoingEdgePerm (senderSwap r c s)
        (vertexSplitLocalEdge q bivectorArity r f))) at h
    simpa only [senderSwap_local, TwoPointSplitFaceAdmissibility.localTarget] using h

include D in
/-- Every actual admissible binary-child face is a fixed canonical split
after only the sender-slot normalization. All incoming choices are extracted. -/
theorem exists_canonical_split (hq : q r = 3) :
    ∃ (c s : Fin 2) (Γ : Graph q m) (χ : Γ.VertexSplitChoices r),
      Γ.vertexSplit (canonicalTemplate c) r hq χ = H.permuteOutgoing (senderSwap r c s) := by
  obtain ⟨⟨c,s⟩,he,hu⟩ := D.unique
  have hi : ∀ e : KontsevichGraph.General.Edge bivectorArity,
      vertexSplitCollapseVertex r (H.target (vertexSplitLocalEdge q bivectorArity r e)) = Sum.inl r ↔ e = ⟨c,s⟩ := by
    intro e
    exact ⟨hu e, fun h => h ▸ he⟩
  refine ⟨c,s,
    BinaryVertexContraction.quotient r hq (normalized r H c s) c (normalized_unique r H c s hi)
      (normalized_coarse r H D c s) (normalized_exits r H D c s hi),
    BinaryVertexContraction.choices r hq (normalized r H c s) c (normalized_unique r H c s hi)
      (normalized_coarse r H D c s) (normalized_exits r H D c s hi), ?_⟩
  exact BinaryVertexContraction.reconstruct r hq (normalized r H c s) c
    (normalized_unique r H c s hi) (normalized_coarse r H D c s) (normalized_exits r H D c s hi)

end EnvelopingIsomorphism.Deformation.Kontsevich.BinaryTemplateOrbitReconstruction
