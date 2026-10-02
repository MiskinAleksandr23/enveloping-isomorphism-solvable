import EnvelopingIsomorphism.Deformation.GraphCurvatureOutgoingAverage

/-! The actual range of normalized curvature splitting satisfies exactly the
combinatorial admissibility used by quotient extraction. Outgoing relabelling
preserves that class, including the original internal-arrow slot. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.UniformBinaryContraction
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits UniformCurvatureTargets UniformCurvatureOutgoing
open GraphCurvatureProfiles BinaryVertexContraction
open scoped Classical
variable {n : ℕ} (i : Fin (n + 1))

def AdmissiblePair (H : BinaryGraph (n + 2) 3) : Prop :=
  ∃ a s, UniqueInternalAt i H a s ∧ CoarseDistinct i H ∧ ExitsDistinctAt i H a s

private theorem canonicalTemplate_leg (a : Fin 2) (j : Fin 3) :
    (canonicalTemplate a).target (canonicalLeg a j) = Sum.inr j := by
  fin_cases a <;> fin_cases j <;> rfl

theorem canonicalDataGraph_unique (a : Fin 2) (D : CurvatureSplitData i) :
    UniqueInternalAt i (canonicalDataGraph i a D) a 0 := by
  intro e
  change vertexSplitCollapseVertex i ((uniformSplit i D.1 (canonicalTemplate a) D.2).target
    ⟨vertexSplitChild i e.1,e.2⟩) = Sum.inl i ↔ e = ⟨a,0⟩
  rw [target_child]
  by_cases he : e = ⟨a,0⟩
  · rw [he, canonicalTemplate_sender_zero, vertexSplitTemplateVertex_child, vertexSplitCollapseVertex_child]
    simp
  · obtain ⟨j,rfl⟩ := canonicalLeg_complete a e he
    rw [canonicalTemplate_leg, vertexSplitTemplateVertex_leg, vertexSplitCollapseVertex_old]
    exact iff_of_false (D.1.noLoops i _) he

theorem canonicalDataGraph_coarse (a : Fin 2) (D : CurvatureSplitData i) :
    CoarseDistinct i (canonicalDataGraph i a D) := by
  intro v hv j k h
  change vertexSplitCollapseVertex i ((uniformSplit i D.1 (canonicalTemplate a) D.2).target
    ⟨vertexSplitOldEmbedding i v,j⟩) = vertexSplitCollapseVertex i
      ((uniformSplit i D.1 (canonicalTemplate a) D.2).target ⟨vertexSplitOldEmbedding i v,k⟩) at h
  rw [target_outside i _ _ _ v hv, target_outside i _ _ _ v hv,
    collapse_vertexSplitOutsideTarget, collapse_vertexSplitOutsideTarget] at h
  exact Fin.cast_injective _ (D.1.distinctTargets v h)

theorem canonicalDataGraph_exits (a : Fin 2) (D : CurvatureSplitData i) :
    ExitsDistinctAt i (canonicalDataGraph i a D) a 0 := by
  intro e f he hf h
  obtain ⟨j,rfl⟩ := canonicalLeg_complete a e he
  obtain ⟨k,rfl⟩ := canonicalLeg_complete a f hf
  change vertexSplitCollapseVertex i ((uniformSplit i D.1 (canonicalTemplate a) D.2).target
    ⟨vertexSplitChild i (canonicalLeg a j).1,(canonicalLeg a j).2⟩) =
    vertexSplitCollapseVertex i ((uniformSplit i D.1 (canonicalTemplate a) D.2).target
    ⟨vertexSplitChild i (canonicalLeg a k).1,(canonicalLeg a k).2⟩) at h
  rw [target_child, target_child, canonicalTemplate_leg, canonicalTemplate_leg,
    vertexSplitTemplateVertex_leg, vertexSplitTemplateVertex_leg,
    vertexSplitCollapseVertex_old, vertexSplitCollapseVertex_old] at h
  exact congrArg (canonicalLeg a) (Fin.cast_injective _ (D.1.distinctTargets i h))

theorem canonicalDataGraph_admissible (a : Fin 2) (D : CurvatureSplitData i) :
    AdmissiblePair i (canonicalDataGraph i a D) :=
  ⟨a,0,canonicalDataGraph_unique i a D,canonicalDataGraph_coarse i a D,canonicalDataGraph_exits i a D⟩

def localOutgoing (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) : Equiv.Perm (Edge bivectorArity) :=
  outgoingEdgePerm (fun c ↦ τ (vertexSplitChild i c))

theorem localTarget_permuteOutgoing (H : BinaryGraph (n + 2) 3)
    (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) (e : Edge bivectorArity) :
    localTarget i (H.permuteOutgoing τ) e = localTarget i H (localOutgoing i τ e) := rfl

theorem localOutgoing_internal_iff (τ : Fin (n + 2) → Equiv.Perm (Fin 2))
    (a s : Fin 2) (e : Edge bivectorArity) :
    localOutgoing i τ e = ⟨a,s⟩ ↔ e = ⟨a,(τ (vertexSplitChild i a)).symm s⟩ :=
  (localOutgoing i τ).apply_eq_iff_eq_symm_apply

/-- Every actual outgoing relabelling preserves the extracted quotient class. -/
theorem admissiblePair_permuteOutgoing (H : BinaryGraph (n + 2) 3)
    (hH : AdmissiblePair i H) (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) :
    AdmissiblePair i (H.permuteOutgoing τ) := by
  obtain ⟨a,s,hi,hd,hx⟩ := hH
  refine ⟨a,(τ (vertexSplitChild i a)).symm s,?_,?_,?_⟩
  · intro e
    rw [localTarget_permuteOutgoing, hi]
    exact localOutgoing_internal_iff i τ a s e
  · intro v hv j k h
    exact (τ (vertexSplitOldEmbedding i v)).injective (hd v hv h)
  · intro e f he hf h
    rw [localTarget_permuteOutgoing,localTarget_permuteOutgoing] at h
    apply (localOutgoing i τ).injective
    exact hx _ _ (fun hh ↦ he ((localOutgoing_internal_iff i τ a s e).mp hh))
      (fun hh ↦ hf ((localOutgoing_internal_iff i τ a s f).mp hh)) h

end EnvelopingIsomorphism.Deformation.UniformBinaryContraction
