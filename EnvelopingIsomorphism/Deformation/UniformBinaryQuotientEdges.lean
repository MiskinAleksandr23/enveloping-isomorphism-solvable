import EnvelopingIsomorphism.Deformation.UniformBinaryContraction

/-! The genuine ordered quotient edges are exactly the noninternal edges of
the original binary graph, with its original internal slot retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.UniformBinaryQuotientEdges
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction UniformBinaryGraphs UniformCurvatureSplits
open UniformBinaryContraction BinaryVertexContraction
open scoped Classical
variable {n : ℕ} (v : Fin (n + 1)) (H : BinaryGraph (n + 2) 3) (c s : Fin 2)
  (hi : UniqueInternalAt v H c s) (hd : CoarseDistinct v H) (hx : ExitsDistinctAt v H c s)

abbrev split := splitGraph v (normalized v H c s)
abbrev template := localTemplate v (selectedArity v).symm (split v H c s) c
  (normalized_unique v H c s hi) (normalized_coarse v H c s hd) (normalized_exits v H c s hx)

def splitInternal : Edge (vertexSplitArity (Arity v) bivectorArity v) :=
  vertexSplitLocalEdge (Arity v) bivectorArity v ⟨c,0⟩

/-- Canonical quotient root slots are the receiver's two slots followed by
the sender's remaining slot, exactly as in native binary contraction. -/
def splitEmbedding : Edge (Arity v) ↪ Edge (vertexSplitArity (Arity v) bivectorArity v) :=
  (template v H c s hi hd hx).vertexSplitOldEdge (canonicalLeg c)
    (localTemplate_leg v (selectedArity v).symm (split v H c s) c
      (normalized_unique v H c s hi) (normalized_coarse v H c s hd) (normalized_exits v H c s hx))
    (Arity v) v (selectedArity v).symm

@[simp] theorem splitEmbedding_outside (e : VertexSplitOutsideEdge (Arity v) v) :
    splitEmbedding v H c s hi hd hx e.val = vertexSplitOutsideEdge (Arity v) bivectorArity v e :=
  Graph.vertexSplitOldEdge_outside _ _ _ e

@[simp] theorem splitEmbedding_root (j : Fin 3) :
    splitEmbedding v H c s hi hd hx ⟨v, Fin.cast (selectedArity v) j⟩ =
      vertexSplitLocalEdge (Arity v) bivectorArity v (canonicalLeg c j) :=
  Graph.vertexSplitOldEdge_root _ _ _ j

theorem splitEmbedding_ne_internal (e : Edge (Arity v)) :
    splitEmbedding v H c s hi hd hx e ≠ splitInternal v c := by
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv (Arity v) v (selectedArity v).symm).symm.surjective e
  rcases e with e | j
  · simp only [vertexSplitOldEdgeEquiv_symm_outside, splitEmbedding_outside, splitInternal]
    exact vertexSplitOutsideEdge_ne_local (Arity v) bivectorArity v e ⟨c,0⟩
  · simp only [vertexSplitOldEdgeEquiv_symm_root, splitEmbedding_root, splitInternal]
    exact (vertexSplitLocalEdge (Arity v) bivectorArity v).injective.ne (canonicalLeg_ne c j)

theorem splitEmbedding_covers (e : Edge (vertexSplitArity (Arity v) bivectorArity v))
    (he : e ≠ splitInternal v c) : ∃ f, splitEmbedding v H c s hi hd hx f = e := by
  obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv (Arity v) bivectorArity v).symm.surjective e
  rcases e with e | e
  · exact ⟨e.val, splitEmbedding_outside v H c s hi hd hx e⟩
  · have he' : e ≠ ⟨c,0⟩ := fun h => he (congrArg (vertexSplitLocalEdge (Arity v) bivectorArity v) h)
    obtain ⟨j,rfl⟩ := canonicalLeg_complete c e he'
    exact ⟨⟨v, Fin.cast (selectedArity v) j⟩, splitEmbedding_root v H c s hi hd hx j⟩

def splitExternalEquiv : Edge (Arity v) ≃
    {e : Edge (vertexSplitArity (Arity v) bivectorArity v) // e ≠ splitInternal v c} :=
  Equiv.ofBijective (fun e => ⟨splitEmbedding v H c s hi hd hx e,
    splitEmbedding_ne_internal v H c s hi hd hx e⟩) ⟨by
      intro e f h
      exact (splitEmbedding v H c s hi hd hx).injective (congrArg Subtype.val h), by
      intro e
      obtain ⟨f,hf⟩ := splitEmbedding_covers v H c s hi hd hx e.val e.property
      exact ⟨f, Subtype.ext hf⟩⟩

/-- Undo the arity cast and original outgoing-slot normalization on all slots. -/
def originalSlots : Edge (vertexSplitArity (Arity v) bivectorArity v) ≃
    Edge (fun _ : Fin (n + 2) => 2) :=
  (Equiv.sigmaCongrRight (fun w => finCongr (congrFun (vertexSplitArity_two v) w))).trans
    (outgoingEdgePerm (slotPermutation v c s))

theorem originalSlots_local (e : Edge bivectorArity) :
    originalSlots v c s (vertexSplitLocalEdge (Arity v) bivectorArity v e) =
      ⟨vertexSplitChild v (localEdgePermutation c s e).1, (localEdgePermutation c s e).2⟩ := by
  rcases e with ⟨w,j⟩
  apply Sigma.ext
  · exact vertexSplitLocalEdge_source (Arity v) bivectorArity v ⟨w,j⟩
  · apply heq_of_eq
    change (slotPermutation v c s (vertexSplitLocalEdge (Arity v) bivectorArity v ⟨w,j⟩).1)
      (Fin.cast (congrFun (vertexSplitArity_two v)
        (vertexSplitLocalEdge (Arity v) bivectorArity v ⟨w,j⟩).1)
        (vertexSplitLocalEdge (Arity v) bivectorArity v ⟨w,j⟩).2) = _
    have hslot : Fin.cast (congrFun (vertexSplitArity_two v)
        (vertexSplitLocalEdge (Arity v) bivectorArity v ⟨w,j⟩).1)
        (vertexSplitLocalEdge (Arity v) bivectorArity v ⟨w,j⟩).2 = j := by
      apply Fin.ext
      exact vertexSplitLocalEdge_slot_val (Arity v) bivectorArity v ⟨w,j⟩
    rw [hslot, vertexSplitLocalEdge_source]
    simp [slotPermutation, localEdgePermutation, outgoingEdgePerm_apply,
      (vertexSplitChild_injective v).eq_iff]

@[simp] theorem originalSlots_internal : originalSlots v c s (splitInternal v c) = ⟨vertexSplitChild v c,s⟩ := by
  rw [splitInternal, originalSlots_local]
  have he : localEdgePermutation c s (⟨c,0⟩ : Edge bivectorArity) = ⟨c,s⟩ :=
    (localEdgePermutation_internal_iff c s _).mpr rfl
  rw [he]

def embedding : Edge (Arity v) ↪ Edge (fun _ : Fin (n + 2) => 2) :=
  (splitEmbedding v H c s hi hd hx).trans (originalSlots v c s).toEmbedding

def originalExternalEquiv : Edge (Arity v) ≃
    {e : Edge (fun _ : Fin (n + 2) => 2) // e ≠ ⟨vertexSplitChild v c,s⟩} :=
  (splitExternalEquiv v H c s hi hd hx).trans
    ((originalSlots v c s).subtypeEquiv (fun e => by
      rw [← originalSlots_internal v c s]
      exact (originalSlots v c s).injective.ne_iff.symm))

@[simp] theorem originalSlots_source (e : Edge (vertexSplitArity (Arity v) bivectorArity v)) :
    (originalSlots v c s e).1 = e.1 := by cases e; rfl

theorem originalSlots_target (e : Edge (vertexSplitArity (Arity v) bivectorArity v)) :
    (split v H c s).target e = H.target (originalSlots v c s e) := by
  rcases e with ⟨w,j⟩
  rw [split, splitGraph, castGraph_target]
  rfl

/-- The quotient target is literally the collapsed target of its actual
retained original arrow. -/
theorem quotient_target (e : Edge (Arity v)) :
    (curvatureGraph v H c s hi hd hx).target e =
      vertexSplitCollapseVertex v (H.target (embedding v H c s hi hd hx e)) := by
  change contractedTarget v (selectedArity v).symm (split v H c s) (canonicalLeg c) e =
    vertexSplitCollapseVertex v (H.target (originalSlots v c s (splitEmbedding v H c s hi hd hx e)))
  rw [← originalSlots_target]
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv (Arity v) v (selectedArity v).symm).symm.surjective e
  rcases e with e | j
  · simp only [vertexSplitOldEdgeEquiv_symm_outside, splitEmbedding_outside, contractedTarget_outside]
  · simp only [vertexSplitOldEdgeEquiv_symm_root, splitEmbedding_root, contractedTarget_root]

/-- Collapsing the source of each retained original arrow gives its quotient
source, including every one of the three root slots. -/
theorem embedding_source (e : Edge (Arity v)) :
    vertexSplitCollapse v (embedding v H c s hi hd hx e).1 = e.1 := by
  change vertexSplitCollapse v (originalSlots v c s (splitEmbedding v H c s hi hd hx e)).1 = e.1
  rw [originalSlots_source]
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv (Arity v) v (selectedArity v).symm).symm.surjective e
  rcases e with e | j
  · simp only [vertexSplitOldEdgeEquiv_symm_outside, splitEmbedding_outside, vertexSplitOutsideEdge_source]
    exact splitExternalCollapse_embedding v e.val.1
  · simp only [vertexSplitOldEdgeEquiv_symm_root, splitEmbedding_root, vertexSplitLocalEdge_source]
    exact splitExternalCollapse_vertex v (canonicalLeg c j).1

end EnvelopingIsomorphism.Deformation.UniformBinaryQuotientEdges
