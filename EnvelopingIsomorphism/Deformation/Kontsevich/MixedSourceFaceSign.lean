import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceCanonicalOrder

/-! Cancellation of extracted leg enumeration signs in actual source faces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceFaceSign
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open MixedTwoPointTemplateWeight TwoPointSplitCanonicalQuotient
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientCoarseLabels
open scoped Classical BigOperators

private theorem rootEdge_sign {N p : ℕ} {q : Fin (N + 1) → ℕ}
    (v : Fin (N + 1)) (hv : q v = p) (ρ : Equiv.Perm (Fin p)) :
    (Equiv.Perm.sign (outgoingEdgePerm (rootOutgoing v hv ρ)) : ℝ) = permutationSign (R := ℝ) ρ := by
  rw [GeometricWeightOutgoing.outgoingEdgePerm_sign]
  let f : ℤˣ →* ℝ := (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)
  change f (∏ w, Equiv.Perm.sign (rootOutgoing v hv ρ w)) = _
  rw [map_prod]
  exact rootOutgoing_sign v hv ρ

private theorem sign_comp_conjugates {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq A] [DecidableEq B] [DecidableEq X]
    (E : A ≃ B) (P : Equiv.Perm A) (T : Equiv.Perm X) (Z : B ≃ X) :
    Equiv.Perm.sign ((E.permCongr P).trans ((Z.trans T).trans Z.symm)) = T.sign * P.sign := by
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_trans_trans_symm]

private theorem block_sign {r q N : ℕ} (hr : r = 1) (hq : q = N)
    (ht : r + q = N + 1) (B : Equiv.Perm (Fin (r + q)))
    (C : Equiv.Perm (Fin (N + 1))) (Q : Fin q ≃ Fin N)
    (hl : ∀ j : Fin r, finCongr ht (B (finSumFinEquiv (Sum.inl j))) = C 0)
    (he : ∀ j : Fin q, finCongr ht (B (finSumFinEquiv (Sum.inr j))) = C (Q j).succ) :
    B.sign = C.sign * Equiv.Perm.sign ((finCongr hq).symm.trans Q) := by
  subst r
  subst q
  change B.sign = C.sign * Equiv.Perm.sign Q
  let E := finCongr ht
  let Z : Fin 1 ⊕ Fin N ≃ Fin (N + 1) := finSumFinEquiv.trans E
  have hz0 (j : Fin 1) : Z (Sum.inl j) = 0 := by
    apply Fin.ext
    have hj := j.isLt
    change j.val = 0
    omega
  have hzs (j : Fin N) : Z (Sum.inr j) = j.succ := by
    apply Fin.ext
    change 1 + j.val = j.val + 1
    omega
  have hh : E.permCongr B = (Z.permCongr (Equiv.sumCongr (Equiv.refl (Fin 1)) Q)).trans C := by
    apply Equiv.ext
    intro x
    obtain ⟨z,rfl⟩ := Z.surjective x
    change E (B (E.symm (Z z))) =
      C (Z ((Equiv.sumCongr (Equiv.refl (Fin 1)) Q) (Z.symm (Z z))))
    rw [Equiv.symm_apply_apply]
    have hEZ : E.symm (Z z) = finSumFinEquiv z := by
      change E.symm (E (finSumFinEquiv z)) = _
      exact E.symm_apply_apply _
    rw [hEZ]
    rcases z with z | z
    · change E (B (finSumFinEquiv (Sum.inl z))) = C (Z (Sum.inl z))
      rw [hz0]
      exact hl z
    · change E (B (finSumFinEquiv (Sum.inr z))) = C (Z (Sum.inr (Q z)))
      rw [hzs]
      exact he z
  have hs := congrArg Equiv.Perm.sign hh
  simpa only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_refl, one_mul] using hs

variable {n : ℕ} (Γ : Graph (fun _ : Fin (n + 1) => 2) 2)
    (v : Fin (n + 1)) (c : Fin 3) (χ : Γ.VertexSplitChoices v)
    (D : Data v (Γ.vertexSplit (sourceTemplate c) v rfl χ))

def rootPermutation : Equiv.Perm (Fin 2) :=
  slotPermutation v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
    MixedTwoPointFaceWeight.vectorBivector_edgeCount D

theorem embedding_eq_template (e : KontsevichGraph.General.Edge (fun _ : Fin (n + 1) => 2)) :
    embedding v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
      MixedTwoPointFaceWeight.vectorBivector_edgeCount D e =
    MixedSourceCanonicalOrder.templateEmbedding v c
      (outgoingEdgePerm (rootOutgoing v rfl (rootPermutation Γ v c χ D)) e) := by
  obtain ⟨f,rfl⟩ := (vertexSplitOldEdgeEquiv (fun _ : Fin (n + 1) => 2) v rfl).symm.surjective e
  rcases f with f | j
  · rw [vertexSplitOldEdgeEquiv_symm_outside, embedding_outside]
    have hf : outgoingEdgePerm (rootOutgoing v rfl (rootPermutation Γ v c χ D)) f.val = f.val := by
      rcases f with ⟨⟨w,s⟩,hw⟩
      simp [outgoingEdgePerm_apply, rootOutgoing_other v rfl _ w hw]
    rw [hf, MixedSourceCanonicalOrder.templateEmbedding_outside]
  · rw [vertexSplitOldEdgeEquiv_symm_root, embedding_root,
      leg_slotPermutation v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)]
    simp only [outgoingEdgePerm_apply, rootOutgoing_root, Fin.cast_eq_self]
    exact (MixedSourceCanonicalOrder.templateEmbedding_root v c _).symm

theorem isInternal_iff_internalEdge (e : KontsevichGraph.General.Edge (MixedSourceCanonicalOrder.splitArity v)) :
    IsInternal (cluster v) (e.1, (Γ.vertexSplit (sourceTemplate c) v rfl χ).target e) ↔
      e = vertexSplitLocalEdge _ _ v (MixedSourceCanonicalOrder.internalEdge c) := by
  obtain ⟨f,rfl⟩ := (vertexSplitEdgeEquiv (fun _ : Fin (n + 1) => 2) vectorBivectorArity v).symm.surjective e
  rcases f with f | e
  · change IsInternal (cluster v) ((vertexSplitOutsideEdge _ _ v f).1,
      (Γ.vertexSplit (sourceTemplate c) v rfl χ).target (vertexSplitOutsideEdge _ _ v f)) ↔ _
    constructor
    · rintro ⟨t,ht,hs,hm⟩
      exact (old_not_mem_cluster v f.val.1 f.property hs).elim
    · intro he
      have hs := congrArg Sigma.fst he
      simp only [vertexSplitOutsideEdge_source, vertexSplitLocalEdge_source] at hs
      exact (vertexSplitOld_ne_child v f.val.1 f.property _ hs).elim
  · change IsInternal (cluster v) ((vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity v e).1,
      (Γ.vertexSplit (sourceTemplate c) v rfl χ).target (vertexSplitLocalEdge _ _ v e)) ↔ _
    rw [vertexSplit_target_local]
    constructor
    · rintro ⟨t,ht,hs,hm⟩
      have hi : ∃ a, (sourceTemplate c).target e = Sum.inl a := by
        cases h : (sourceTemplate c).target e with
        | inl a => exact ⟨a,rfl⟩
        | inr j =>
          rw [h, vertexSplitTemplateVertex_leg] at ht
          obtain ⟨a,ha⟩ := (mem_cluster v t).mp hm
          have hc := congrArg (vertexSplitCollapseVertex v) ht
          rw [vertexSplitCollapseVertex_old, ← ha, vertexSplitCollapseVertex_child] at hc
          exact (Γ.noLoops v j hc).elim
      exact congrArg (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity v)
        ((MixedSourceCanonicalOrder.source_internal_iff c e).mp hi)
    · intro he
      have he' := (vertexSplitLocalEdge (fun _ : Fin (n + 1) => 2) vectorBivectorArity v).injective he
      obtain ⟨a,ha⟩ := (MixedSourceCanonicalOrder.source_internal_iff c e).mpr he'
      refine ⟨vertexSplitChild v a, ?_, child_mem_cluster v e.1, child_mem_cluster v a⟩
      rw [ha, vertexSplitTemplateVertex_child]

variable {i a b : Fin (n + 2)}
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (hanchor : i ∈ cluster v → a = i)

include ha hb hba hanchor in
theorem nativeDegree_eq :
    shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 2 = (2 * n + 2) + 1 := by
  rw [shapeDegree_eq ha hb hba, cluster_card]
  change 1 + GraphForms.dimension (coarseN i a (cluster v)) 2 = _
  rw [coarseN_eq v ha hanchor]
  dsimp [GraphForms.dimension]
  omega

def sourceMajorOrder : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 2) ≃
    KontsevichGraph.General.Edge (MixedSourceCanonicalOrder.splitArity v) :=
  (finCongr (nativeDegree_eq v ha hb hba hanchor)).trans (MixedSourceCanonicalOrder.splitOrder v)

variable
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 2) ≃
      KontsevichGraph.General.Edge (MixedSourceCanonicalOrder.splitArity v))
    (hc : Fintype.card {j // IsInternal (cluster v)
      (TwoPointSplitFaceAdmissibility.orderedEdges v (Γ.vertexSplit (sourceTemplate c) v rfl χ) order j)} =
      shapeDegree a b (cluster v))

def originalQuotientOrder : Fin (coarseDegree i a (cluster v) 2) ≃ Fin (2 * n + 2) :=
  ((TwoPointSplitFaceWeight.quotientOrder v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
    MixedTwoPointFaceWeight.vectorBivector_edgeCount D order hc).trans
    (outgoingEdgePerm (rootOutgoing v rfl (rootPermutation Γ v c χ D)))).trans
    MixedSourceCanonicalOrder.quotientOrder.symm

theorem blockSign_original (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    let hq : coarseDegree i a (cluster v) 2 = 2 * n + 2 := by
      change GraphForms.dimension (coarseN i a (cluster v)) 2 = _
      rw [coarseN_eq v ha hanchor]
      dsimp [GraphForms.dimension]
      omega
    (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v
      (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) hc).sign =
      (MixedSourceCanonicalOrder.canonicalPermutation v c).sign *
      Equiv.Perm.sign ((finCongr hq).symm.trans (originalQuotientOrder Γ v c χ D order hc)) := by
  dsimp only
  let B := edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v
    (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) hc
  let C := MixedSourceCanonicalOrder.canonicalPermutation v c
  let Q := originalQuotientOrder Γ v c χ D order hc
  have hr : shapeDegree a b (cluster v) = 1 := by rw [shapeDegree_eq ha hb hba, cluster_card]
  have hq : coarseDegree i a (cluster v) 2 = 2 * n + 2 := by
    change GraphForms.dimension (coarseN i a (cluster v)) 2 = _
    rw [coarseN_eq v ha hanchor]
    dsimp [GraphForms.dimension]
    omega
  apply block_sign hr hq (nativeDegree_eq v ha hb hba hanchor) B C Q
  · intro j
    apply (MixedSourceCanonicalOrder.splitOrder v).injective
    have ho (k) : order k = MixedSourceCanonicalOrder.splitOrder v
        (finCongr (nativeDegree_eq v ha hb hba hanchor) k) := by rw [horder]; rfl
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inl j))) =
      MixedSourceCanonicalOrder.splitOrder v (MixedSourceCanonicalOrder.canonicalPermutation v c 0)
    rw [edgeBlockPermutation_inl, MixedSourceCanonicalOrder.canonicalPermutation_zero]
    simp only [MixedSourceCanonicalOrder.internalIndex, Equiv.apply_symm_apply]
    exact (isInternal_iff_internalEdge Γ v c χ _).mp
      ((internalEnum (TwoPointSplitFaceAdmissibility.orderedEdges v
        (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) hc).symm j).property
  · intro j
    apply (MixedSourceCanonicalOrder.splitOrder v).injective
    have ho (k) : order k = MixedSourceCanonicalOrder.splitOrder v
        (finCongr (nativeDegree_eq v ha hb hba hanchor) k) := by rw [horder]; rfl
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inr j))) =
      MixedSourceCanonicalOrder.splitOrder v (MixedSourceCanonicalOrder.canonicalPermutation v c (Q j).succ)
    rw [edgeBlockPermutation_inr, MixedSourceCanonicalOrder.canonicalPermutation_embedding]
    simp only [Q, originalQuotientOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [← embedding_eq_template Γ v c χ D]
    exact (embedding_quotientOrder v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
      MixedTwoPointFaceWeight.vectorBivector_edgeCount D order hc j).symm

theorem originalQuotientOrder_sign
    (hq : coarseDegree i a (cluster v) 2 = 2 * n + 2) :
    (Equiv.Perm.sign ((finCongr hq).symm.trans (originalQuotientOrder Γ v c χ D order hc)) : ℝ) =
      (Equiv.Perm.sign (quotientOrderPermutation v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
        MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hanchor order hc) : ℝ) *
      permutationSign (R := ℝ) (rootPermutation Γ v c χ D) := by
  let hd : GraphForms.dimension n 2 = 2 * n + 2 := by dsimp [GraphForms.dimension]; omega
  let E := finCongr hd
  let P := quotientOrderPermutation v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
    MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hanchor order hc
  let T : Equiv.Perm (KontsevichGraph.General.Edge (fun _ : Fin (n + 1) => 2)) :=
    outgoingEdgePerm (rootOutgoing v rfl (rootPermutation Γ v c χ D))
  let A := MixedSourceCanonicalOrder.quotientOrder (n := n)
  have he : (finCongr hq).symm.trans (originalQuotientOrder Γ v c χ D order hc) =
      (E.permCongr P).trans ((A.trans T).trans A.symm) := by
    apply Equiv.ext
    intro j
    simp only [originalQuotientOrder, E, P, A, T, quotientOrderPermutation, inducedOrder,
      Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply,
      GeometricWeights.canonicalOrder, MixedSourceCanonicalOrder.quotientOrder,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
      Equiv.apply_symm_apply]
  have hsign := (congrArg Equiv.Perm.sign he).trans (sign_comp_conjugates E P T A)
  have hT : (T.sign : ℝ) = permutationSign (R := ℝ) (rootPermutation Γ v c χ D) := by
    exact rootEdge_sign (q := fun _ : Fin (n + 1) => 2) v rfl (rootPermutation Γ v c χ D)
  have hh := congrArg (fun z : ℤˣ => (z : ℝ)) hsign
  simp only [Units.val_mul, Int.cast_mul] at hh
  rw [hT] at hh
  exact hh.trans (mul_comm _ _)

/-- The native source-face sign is exactly the Schouten sign. The arbitrary
extracted quotient-leg order has cancelled completely. -/
theorem faceSign_sourceMajor (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    faceSign v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
      MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hanchor order hc *
      permutationSign (R := ℝ) (rootPermutation Γ v c χ D) = if c = 1 then -1 else 1 := by
  have hq : coarseDegree i a (cluster v) 2 = 2 * n + 2 := by
    change GraphForms.dimension (coarseN i a (cluster v)) 2 = _
    rw [coarseN_eq v ha hanchor]
    dsimp [GraphForms.dimension]
    omega
  let B := edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges v
    (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) hc
  let Q := (finCongr hq).symm.trans (originalQuotientOrder Γ v c χ D order hc)
  have hB := blockSign_original Γ v c χ D ha hb hba hanchor order hc horder
  change B.sign = (MixedSourceCanonicalOrder.canonicalPermutation v c).sign * Equiv.Perm.sign Q at hB
  have hQ := originalQuotientOrder_sign Γ v c χ D ha hanchor order hc hq
  have hs : (Equiv.Perm.sign Q : ℝ) * (Equiv.Perm.sign Q : ℝ) = 1 := by
    simp [← Int.cast_mul, ← Units.val_mul]
  unfold faceSign
  rw [Equiv.Perm.sign_symm]
  change (B.sign : ℝ) * _ * _ = _
  rw [mul_assoc, ← hQ, hB]
  rw [show (((MixedSourceCanonicalOrder.canonicalPermutation v c).sign * Equiv.Perm.sign Q : ℤˣ) : ℝ) =
      ((MixedSourceCanonicalOrder.canonicalPermutation v c).sign : ℝ) * (Equiv.Perm.sign Q : ℝ) by simp,
    mul_assoc, hs, mul_one, MixedSourceCanonicalOrder.canonicalPermutation_sign]
  split_ifs <;> norm_num

/-- The three actual source-face integrals now have exactly the numerical
Schouten coefficients +1, -1, +1, with the original quotient weight. -/
theorem normalized_sourceMajor
    (y : RealProductCoordinates i a b (cluster v) 2)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) 2)
    (hne : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v
      (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) y ≠ 0)
    (horder : order = sourceMajorOrder v ha hb hba hanchor) :
    normalizedIntegral v (Γ.vertexSplit (sourceTemplate c) v rfl χ) order =
      (if c = 1 then (-1 : ℝ) else 1) * GraphCanonicalBinaryWeights.rawBinaryWeight (n + 1) Γ := by
  rw [normalized_source_template Γ v c χ ha hb hba hanchor order y hy hne]
  let D' := ofNonzero v (Γ.vertexSplit (sourceTemplate c) v rfl χ) order ha hb hba y hy hne
  let hc' := count_of_nonzero v (Γ.vertexSplit (sourceTemplate c) v rfl χ) ha order hb hba y hy hne
  change (faceSign v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
    MixedTwoPointFaceWeight.vectorBivector_edgeCount D' ha hanchor order hc' *
    permutationSign (R := ℝ) (rootPermutation Γ v c χ D')) * _ = _
  rw [faceSign_sourceMajor Γ v c χ D' ha hb hba hanchor order hc' horder]

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceFaceSign
