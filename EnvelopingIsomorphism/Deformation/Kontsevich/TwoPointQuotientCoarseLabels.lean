import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceAdmissibility

/-! The actual simple-chart coarse label enumeration is an explicit bijective
relabeling of the native binary-contraction quotient labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientCoarseLabels
open KontsevichGraph.General InteriorGraphFaceCoordinates ClusterFreeCoordinates
open TwoPointBinaryFaceAdmissibility
open scoped Classical
variable {n : ℕ} (v : Fin (n + 1)) {i a : Fin (n + 2)}
  (ha : a ∈ cluster v) (hanchor : i ∈ cluster v → a = i)

def quotientLabel (w : Fin (n + 1)) : Fin (coarseN i a (cluster v) + 1) :=
  coarseLabel (vertexSplitOldEmbedding v w)

include ha in
theorem collapse_representative (j : Fin (n + 2)) :
    vertexSplitCollapse v (representative (cluster v) a j) = vertexSplitCollapse v j := by
  by_cases hj : j ∈ cluster v
  · obtain ⟨c,hc⟩ := (mem_cluster v a).mp ha
    obtain ⟨e,he⟩ := (mem_cluster v j).mp hj
    rw [representative, if_pos hj, ← hc, ← he]
    simp
  · rw [representative, if_neg hj]

theorem coarseLabel_eq_quotientLabel (j : Fin (n + 2)) :
    coarseLabel (i := i) (a := a) (S := cluster v) j = quotientLabel (i := i) (a := a) v (vertexSplitCollapse v j) := by
  have ht := coarseTarget_eq_of_collapse_eq (i := i) (a := a) (m := 0) v
    (Sum.inl j) (Sum.inl (vertexSplitOldEmbedding v (vertexSplitCollapse v j))) (by simp [vertexSplitCollapseVertex])
  exact Sum.inl.inj ht

include ha in
theorem quotientLabel_injective : Function.Injective (quotientLabel (i := i) (a := a) v) := by
  intro j k h
  have hr := coarseLabel_eq_imp (vertexSplitOldEmbedding v j) (vertexSplitOldEmbedding v k) h
  have hc := congrArg (vertexSplitCollapse v) hr
  simpa only [collapse_representative v ha, splitExternalCollapse_embedding] using hc

include ha hanchor in
theorem coarseLabel_surjective : Function.Surjective (coarseLabel (i := i) (a := a) (S := cluster v)) := by
  intro q
  induction q using Fin.cases with
  | zero =>
    refine ⟨i, ?_⟩
    have hr : representative (cluster v) a i = i := by
      by_cases hi : i ∈ cluster v
      · rw [representative, if_pos hi, hanchor hi]
      · rw [representative, if_neg hi]
    simp [coarseLabel, hr]
  | succ q =>
    let j := (coarseEnum (i := i) (a := a) (S := cluster v)).symm q
    have hr : representative (cluster v) a j.val = j.val := by
      rcases j.property.1 with hj | hj
      · rw [hj, representative, if_pos ha]
      · rw [representative, if_neg hj]
    refine ⟨j.val, ?_⟩
    simp only [coarseLabel, hr, dif_neg j.property.2]
    change (coarseEnum j).succ = q.succ
    exact congrArg Fin.succ ((coarseEnum (i := i) (a := a) (S := cluster v)).apply_symm_apply q)

include ha hanchor in
theorem quotientLabel_surjective : Function.Surjective (quotientLabel (i := i) (a := a) v) := by
  intro q
  obtain ⟨j,hj⟩ := coarseLabel_surjective v ha hanchor q
  exact ⟨vertexSplitCollapse v j, (coarseLabel_eq_quotientLabel v j).symm.trans hj⟩

def quotientLabelEquiv : Fin (n + 1) ≃ Fin (coarseN i a (cluster v) + 1) :=
  Equiv.ofBijective (quotientLabel v) ⟨quotientLabel_injective v ha, quotientLabel_surjective v ha hanchor⟩

@[simp] theorem quotientLabelEquiv_apply (j : Fin (n + 1)) :
    quotientLabelEquiv v ha hanchor j = quotientLabel v j := rfl

include ha hanchor in
theorem coarseN_eq : coarseN i a (cluster v) = n := by
  rw [coarseN, card_clusterCoarseIndex i a (cluster v) ha hanchor, cluster_card]
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientCoarseLabels
