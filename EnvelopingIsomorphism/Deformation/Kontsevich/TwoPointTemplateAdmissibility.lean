import EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointTemplateWeight

/-! A genuine quotient split by a one-arrow template automatically has
admissible two-point contraction data. No nonzero-density witness is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open TwoPointSplitFaceAdmissibility TwoPointSplitFaceContraction
open TwoPointBinaryFaceAdmissibility InteriorGraphFaceCoordinates
open MixedTwoPointTemplateWeight
variable {n m p : ℕ} {q : Fin (n+1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (v : Fin (n+1)) (hq : q v = p)
  (Γ : Graph q m) (Θ : Graph qLocal p) (χ : Γ.VertexSplitChoices v)

theorem local_collapse_internal_iff (e : KontsevichGraph.General.Edge qLocal) :
    vertexSplitCollapseVertex v (localTarget v (Γ.vertexSplit Θ v hq χ) e) = Sum.inl v ↔
      ∃ a, Θ.target e = Sum.inl a := by
  unfold localTarget
  rw [vertexSplit_target_local]
  cases ht : Θ.target e with
  | inl a => simp [vertexSplitTemplateVertex_child, vertexSplitCollapseVertex_child]
  | inr j =>
    rw [vertexSplitTemplateVertex_leg, vertexSplitCollapseVertex_old]
    simp only [Γ.noLoops, false_iff, reduceCtorEq, exists_false, not_false_eq_true]

theorem split_coarseDistinct : (Γ.vertexSplit Θ v hq χ).SplitCoarseDistinct v := by
  intro w hw j k ht
  simp only [vertexSplit_target_outside, collapse_vertexSplitOutsideTarget] at ht
  exact Γ.distinctTargets w ht

theorem split_exitsDistinct
    (L : Fin p → KontsevichGraph.General.Edge qLocal)
    (hL : ∀ e j, Θ.target e = Sum.inr j ↔ L j = e)
    (e f : KontsevichGraph.General.Edge qLocal)
    (he : vertexSplitCollapseVertex v (localTarget v (Γ.vertexSplit Θ v hq χ) e) ≠ Sum.inl v)
    (hf : vertexSplitCollapseVertex v (localTarget v (Γ.vertexSplit Θ v hq χ) f) ≠ Sum.inl v)
    (ht : vertexSplitCollapseVertex v (localTarget v (Γ.vertexSplit Θ v hq χ) e) =
      vertexSplitCollapseVertex v (localTarget v (Γ.vertexSplit Θ v hq χ) f)) : e = f := by
  have he' : ¬ ∃ a, Θ.target e = Sum.inl a :=
    fun h ↦ he ((local_collapse_internal_iff v hq Γ Θ χ e).mpr h)
  have hf' : ¬ ∃ a, Θ.target f = Sum.inl a :=
    fun h ↦ hf ((local_collapse_internal_iff v hq Γ Θ χ f).mpr h)
  cases heq : Θ.target e with
  | inl a => exact (he' ⟨a,heq⟩).elim
  | inr j =>
    cases hfq : Θ.target f with
    | inl a => exact (hf' ⟨a,hfq⟩).elim
    | inr k =>
      simp only [localTarget, vertexSplit_target_local, heq, hfq,
        vertexSplitTemplateVertex_leg, vertexSplitCollapseVertex_old] at ht
      have hjk : j = k := Fin.cast_injective hq.symm (Γ.distinctTargets v ht)
      subst k
      exact ((hL e j).mp heq).symm.trans ((hL f j).mp hfq)

/-- The contraction data follow from the actual quotient and template
incidence, including every original incoming-edge assignment. -/
theorem data_of_template
    (L : Fin p → KontsevichGraph.General.Edge qLocal)
    (hL : ∀ e j, Θ.target e = Sum.inr j ↔ L j = e)
    (hi : ∃! e : KontsevichGraph.General.Edge qLocal, ∃ a, Θ.target e = Sum.inl a) :
    Data v (Γ.vertexSplit Θ v hq χ) := by
  refine ⟨?_, split_coarseDistinct v hq Γ Θ χ, split_exitsDistinct v hq Γ Θ χ L hL⟩
  obtain ⟨e,he,hu⟩ := hi
  exact ⟨e, (local_collapse_internal_iff v hq Γ Θ χ e).mpr he,
    fun f hf ↦ hu f ((local_collapse_internal_iff v hq Γ Θ χ f).mp hf)⟩

theorem source_uniqueInternal (c : Fin 3) :
    ∃! e : KontsevichGraph.General.Edge vectorBivectorArity,
      ∃ a, (sourceTemplate c).target e = Sum.inl a := by
  unfold ExistsUnique
  fin_cases c <;> decide

theorem correction_uniqueInternal (c : Fin 2) :
    ∃! e : KontsevichGraph.General.Edge bivectorArity,
      ∃ a, (BinaryVertexContraction.canonicalTemplate c).target e = Sum.inl a := by
  unfold ExistsUnique
  fin_cases c <;> decide

theorem source_data (Γ : Graph (fun _ : Fin (n+1) ↦ 2) m)
    (v : Fin (n+1)) (c : Fin 3) (χ : Γ.VertexSplitChoices v) :
    Data v (Γ.vertexSplit (sourceTemplate c) v rfl χ) :=
  data_of_template v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
    (source_uniqueInternal c)

theorem correction_data (p : MixedGraphCorrectionProfiles.Placement n)
    (Γ : Graph (twoOddArity p.1 p.2) m) (c : Fin 2) (χ : Γ.VertexSplitChoices p.2) :
    Data p.2.val (Γ.vertexSplit (BinaryVertexContraction.canonicalTemplate c)
      p.2.val (MixedGraphCorrectionProfiles.selectedArity p).symm χ) :=
  data_of_template p.2.val (MixedGraphCorrectionProfiles.selectedArity p).symm Γ
    (BinaryVertexContraction.canonicalTemplate c) χ (BinaryVertexContraction.canonicalLeg c)
    (correction_leg c) (correction_uniqueInternal c)

open scoped Classical

/-- Any original edge enumeration sees the same unique internal arrow. -/
theorem internal_count_of_data (H : Graph (vertexSplitArity q qLocal v) m) (D : Data v H)
    {d : ℕ} (order : Fin d ≃ KontsevichGraph.General.Edge (vertexSplitArity q qLocal v)) :
    Fintype.card {j // IsInternal (cluster v) (orderedEdges v H order j)} = 1 := by
  classical
  obtain ⟨e,he,hu⟩ := D.unique
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨localIndex v order e, (local_isInternal_iff v H order e).mpr he⟩, ?_⟩
  intro j
  apply Subtype.ext
  obtain ⟨f,hf⟩ := internal_has_localIndex v H order j.val j.property
  have hf' : vertexSplitCollapseVertex v (localTarget v H f) = Sum.inl v :=
    (local_isInternal_iff v H order f).mp (hf.symm ▸ j.property)
  exact hf.symm.trans (congrArg (localIndex v order) (hu f hf'))

theorem count_shape_of_data (H : Graph (vertexSplitArity q qLocal v) m) (D : Data v H)
    {i a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m) ≃
      KontsevichGraph.General.Edge (vertexSplitArity q qLocal v)) :
    Fintype.card {j // IsInternal (cluster v) (orderedEdges v H order j)} =
      shapeDegree a b (cluster v) := by
  rw [internal_count_of_data v H D order, shapeDegree_eq ha hb hba, cluster_card]

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility
