import EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionCanonicalOrder
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCanonicalSignAlgebra
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility

/-! Exact correction face signs, including the retained vector placement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionFaceSign
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction MixedGraphCorrectionProfiles
open BinaryVertexContraction
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight TwoPointSplitCanonicalQuotient
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientCoarseLabels
open TwoPointCanonicalSignAlgebra
open scoped Classical BigOperators
variable {n : ℕ} (p : Placement n) (Γ : Graph (twoOddArity p.1 p.2) 2)
    (c : Fin 2) (χ : Γ.VertexSplitChoices p.2)
    (D : Data p.2.val (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ))

def rootPermutation : Equiv.Perm (Fin 3) :=
  slotPermutation p.2.val (selectedArity p).symm Γ (canonicalTemplate c) χ (canonicalLeg c)
    (MixedTwoPointTemplateWeight.correction_leg c) MixedTwoPointFaceWeight.bivector_edgeCount D

theorem embedding_eq_template (e : KontsevichGraph.General.Edge (twoOddArity p.1 p.2)) :
    embedding p.2.val (selectedArity p).symm
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
      MixedTwoPointFaceWeight.bivector_edgeCount D e =
    MixedCorrectionCanonicalOrder.templateEmbedding p c
      (outgoingEdgePerm (rootOutgoing p.2.val (selectedArity p).symm (rootPermutation p Γ c χ D)) e) := by
  obtain ⟨f,rfl⟩ := (vertexSplitOldEdgeEquiv (twoOddArity p.1 p.2) p.2.val (selectedArity p).symm).symm.surjective e
  rcases f with f | j
  · rw [vertexSplitOldEdgeEquiv_symm_outside, TwoPointSplitFaceContraction.embedding_outside]
    have hf : outgoingEdgePerm (rootOutgoing p.2.val (selectedArity p).symm (rootPermutation p Γ c χ D)) f.val = f.val := by
      rcases f with ⟨⟨w,s⟩,hw⟩
      simp [outgoingEdgePerm_apply, rootOutgoing_other p.2.val (selectedArity p).symm _ w hw]
    rw [hf, MixedCorrectionCanonicalOrder.templateEmbedding_outside]
  · rw [vertexSplitOldEdgeEquiv_symm_root, TwoPointSplitFaceContraction.embedding_root,
      leg_slotPermutation p.2.val (selectedArity p).symm Γ (canonicalTemplate c) χ (canonicalLeg c)
        (MixedTwoPointTemplateWeight.correction_leg c)]
    simp only [outgoingEdgePerm_apply, rootOutgoing_root, Fin.cast_cast, Fin.cast_eq_self]
    exact (MixedCorrectionCanonicalOrder.templateEmbedding_root p c _).symm

theorem template_internal_iff (e : KontsevichGraph.General.Edge bivectorArity) :
    (∃ a, (canonicalTemplate c).target e = Sum.inl a) ↔ e = ⟨c,0⟩ := by
  rcases e with ⟨w,s⟩
  fin_cases c <;> fin_cases w <;> fin_cases s <;> decide

theorem isInternal_iff_internalEdge
    (e : KontsevichGraph.General.Edge (MixedCorrectionCanonicalOrder.expandedArity p)) :
    IsInternal (cluster p.2.val) (e.1, (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ).target e) ↔
      e = vertexSplitLocalEdge _ _ p.2.val ⟨c,0⟩ := by
  obtain ⟨f,rfl⟩ := (vertexSplitEdgeEquiv (twoOddArity p.1 p.2) bivectorArity p.2.val).symm.surjective e
  rcases f with f | e
  · change IsInternal (cluster p.2.val) ((vertexSplitOutsideEdge _ _ p.2.val f).1,
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ).target (vertexSplitOutsideEdge _ _ p.2.val f)) ↔ _
    constructor
    · rintro ⟨t,ht,hs,hm⟩
      exact (old_not_mem_cluster p.2.val f.val.1 f.property hs).elim
    · intro he
      have hs := congrArg Sigma.fst he
      simp only [vertexSplitOutsideEdge_source, vertexSplitLocalEdge_source] at hs
      exact (vertexSplitOld_ne_child p.2.val f.val.1 f.property _ hs).elim
  · change IsInternal (cluster p.2.val) ((vertexSplitLocalEdge (twoOddArity p.1 p.2) bivectorArity p.2.val e).1,
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ).target
        (vertexSplitLocalEdge (twoOddArity p.1 p.2) bivectorArity p.2.val e)) ↔ _
    rw [vertexSplit_target_local]
    constructor
    · rintro ⟨t,ht,hs,hm⟩
      have hi : ∃ a, (canonicalTemplate c).target e = Sum.inl a := by
        cases h : (canonicalTemplate c).target e with
        | inl a => exact ⟨a,rfl⟩
        | inr j =>
          rw [h, vertexSplitTemplateVertex_leg] at ht
          obtain ⟨a,ha⟩ := (mem_cluster p.2.val t).mp hm
          have hc := congrArg (vertexSplitCollapseVertex p.2.val) ht
          rw [vertexSplitCollapseVertex_old, ← ha, vertexSplitCollapseVertex_child] at hc
          exact (Γ.noLoops p.2.val (Fin.cast (selectedArity p) j) hc).elim
      exact congrArg (vertexSplitLocalEdge (twoOddArity p.1 p.2) bivectorArity p.2.val)
        ((template_internal_iff c e).mp hi)
    · intro he
      have he' := (vertexSplitLocalEdge (twoOddArity p.1 p.2) bivectorArity p.2.val).injective he
      obtain ⟨a,ha⟩ := (template_internal_iff c e).mpr he'
      refine ⟨vertexSplitChild p.2.val a, ?_, child_mem_cluster p.2.val e.1, child_mem_cluster p.2.val a⟩
      rw [ha, vertexSplitTemplateVertex_child]

variable {i a b : Fin (n + 3)}
    (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val) (hba : b ≠ a)
    (hanchor : i ∈ cluster p.2.val → a = i)

include ha hb hba hanchor in
theorem nativeDegree_eq :
    shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2 =
      MixedCorrectionCanonicalOrder.dim (n := n) + 1 := by
  rw [shapeDegree_eq ha hb hba, cluster_card]
  change 1 + GraphForms.dimension (coarseN i a (cluster p.2.val)) 2 = _
  rw [coarseN_eq p.2.val ha hanchor]
  dsimp [MixedCorrectionCanonicalOrder.dim]
  omega

def sourceMajorOrder : Fin (shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2) ≃
    KontsevichGraph.General.Edge (MixedCorrectionCanonicalOrder.expandedArity p) :=
  (finCongr (nativeDegree_eq p ha hb hba hanchor)).trans (MixedCorrectionCanonicalOrder.splitOrder p)

variable
    (order : Fin (shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2) ≃
      KontsevichGraph.General.Edge (MixedCorrectionCanonicalOrder.expandedArity p))
    (hc : Fintype.card {j // IsInternal (cluster p.2.val)
      (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
        (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ) order j)} =
      shapeDegree a b (cluster p.2.val))

def originalQuotientOrder : Fin (coarseDegree i a (cluster p.2.val) 2) ≃ Fin (MixedCorrectionCanonicalOrder.dim (n := n)) :=
  ((TwoPointSplitFaceWeight.quotientOrder p.2.val (selectedArity p).symm
    (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
    MixedTwoPointFaceWeight.bivector_edgeCount D order hc).trans
    (outgoingEdgePerm (rootOutgoing p.2.val (selectedArity p).symm (rootPermutation p Γ c χ D)))).trans
    (MixedCorrectionCanonicalOrder.quotientOrder p).symm

theorem blockSign_original (horder : order = sourceMajorOrder p ha hb hba hanchor) :
    let hq := congrArg (fun t => GraphForms.dimension t 2) (coarseN_eq p.2.val ha hanchor)
    (edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ) order) hc).sign =
      (MixedCorrectionCanonicalOrder.canonicalPermutation p c).sign *
      Equiv.Perm.sign ((finCongr hq).symm.trans (originalQuotientOrder p Γ c χ D order hc)) := by
  dsimp only
  let B := edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
    (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ) order) hc
  let C := MixedCorrectionCanonicalOrder.canonicalPermutation p c
  let Q := originalQuotientOrder p Γ c χ D order hc
  have hr : shapeDegree a b (cluster p.2.val) = 1 := by rw [shapeDegree_eq ha hb hba, cluster_card]
  have hq := congrArg (fun t => GraphForms.dimension t 2) (coarseN_eq p.2.val ha hanchor)
  apply block_sign hr hq (nativeDegree_eq p ha hb hba hanchor) B C Q
  · intro j
    apply (MixedCorrectionCanonicalOrder.splitOrder p).injective
    have ho (k) : order k = MixedCorrectionCanonicalOrder.splitOrder p
        (finCongr (nativeDegree_eq p ha hb hba hanchor) k) := by rw [horder]; rfl
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inl j))) =
      MixedCorrectionCanonicalOrder.splitOrder p (MixedCorrectionCanonicalOrder.canonicalPermutation p c 0)
    rw [edgeBlockPermutation_inl, MixedCorrectionCanonicalOrder.canonicalPermutation_zero]
    simp only [MixedCorrectionCanonicalOrder.internalIndex, Equiv.apply_symm_apply]
    exact (isInternal_iff_internalEdge p Γ c χ _).mp
      ((internalEnum (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
        (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ) order) hc).symm j).property
  · intro j
    apply (MixedCorrectionCanonicalOrder.splitOrder p).injective
    have ho (k) : order k = MixedCorrectionCanonicalOrder.splitOrder p
        (finCongr (nativeDegree_eq p ha hb hba hanchor) k) := by rw [horder]; rfl
    rw [← ho]
    change order (edgeBlockPermutation _ _ (finSumFinEquiv (Sum.inr j))) =
      MixedCorrectionCanonicalOrder.splitOrder p (MixedCorrectionCanonicalOrder.canonicalPermutation p c (Q j).succ)
    rw [edgeBlockPermutation_inr, MixedCorrectionCanonicalOrder.canonicalPermutation_embedding]
    simp only [Q, originalQuotientOrder, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [← embedding_eq_template p Γ c χ D]
    exact (embedding_quotientOrder p.2.val (selectedArity p).symm
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
      MixedTwoPointFaceWeight.bivector_edgeCount D order hc j).symm

theorem originalQuotientOrder_sign :
    let hq := congrArg (fun t => GraphForms.dimension t 2) (coarseN_eq p.2.val ha hanchor)
    (Equiv.Perm.sign ((finCongr hq).symm.trans (originalQuotientOrder p Γ c χ D order hc)) : ℝ) =
      (Equiv.Perm.sign (quotientOrderPermutation p.2.val (selectedArity p).symm
        (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
        MixedTwoPointFaceWeight.bivector_edgeCount D ha hanchor order hc) : ℝ) *
      permutationSign (R := ℝ) (rootPermutation p Γ c χ D) := by
  dsimp only
  let hq := congrArg (fun t => GraphForms.dimension t 2) (coarseN_eq p.2.val ha hanchor)
  let P := quotientOrderPermutation p.2.val (selectedArity p).symm
    (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
    MixedTwoPointFaceWeight.bivector_edgeCount D ha hanchor order hc
  let T : Equiv.Perm (KontsevichGraph.General.Edge (twoOddArity p.1 p.2)) :=
    outgoingEdgePerm (rootOutgoing p.2.val (selectedArity p).symm (rootPermutation p Γ c χ D))
  let A := MixedCorrectionCanonicalOrder.quotientOrder p
  have he : (finCongr hq).symm.trans (originalQuotientOrder p Γ c χ D order hc) =
      ((Equiv.refl _).permCongr P).trans ((A.trans T).trans A.symm) := by
    apply Equiv.ext
    intro j
    simp only [originalQuotientOrder, P, A, T, quotientOrderPermutation, inducedOrder,
      Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.refl_apply,
      Equiv.refl_symm, GeometricWeights.canonicalOrder, MixedCorrectionCanonicalOrder.quotientOrder,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have hsign := (congrArg Equiv.Perm.sign he).trans (sign_comp_conjugates (Equiv.refl _) P T A)
  have hT : (T.sign : ℝ) = permutationSign (R := ℝ) (rootPermutation p Γ c χ D) :=
    rootEdge_sign (q := twoOddArity p.1 p.2) p.2.val (selectedArity p).symm (rootPermutation p Γ c χ D)
  have hh := congrArg (fun z : ℤˣ => (z : ℝ)) hsign
  simp only [Units.val_mul, Int.cast_mul] at hh
  rw [hT] at hh
  exact hh.trans (mul_comm _ _)

/-- The actual correction-face ordering retains minus the two-odd placement
sign, after all arbitrary extraction-order signs cancel. -/
theorem faceSign_sourceMajor (horder : order = sourceMajorOrder p ha hb hba hanchor) :
    faceSign p.2.val (selectedArity p).symm
      (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
      MixedTwoPointFaceWeight.bivector_edgeCount D ha hanchor order hc *
      permutationSign (R := ℝ) (rootPermutation p Γ c χ D) = -(placementSign p : ℝ) := by
  let hq := congrArg (fun t => GraphForms.dimension t 2) (coarseN_eq p.2.val ha hanchor)
  let B := edgeBlockPermutation (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
    (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ) order) hc
  let Q := (finCongr hq).symm.trans (originalQuotientOrder p Γ c χ D order hc)
  have hB := blockSign_original p Γ c χ D ha hb hba hanchor order hc horder
  change B.sign = (MixedCorrectionCanonicalOrder.canonicalPermutation p c).sign * Equiv.Perm.sign Q at hB
  have hQ := originalQuotientOrder_sign p Γ c χ D ha hanchor order hc
  have hs : (Equiv.Perm.sign Q : ℝ) * (Equiv.Perm.sign Q : ℝ) = 1 := by
    simp [← Int.cast_mul, ← Units.val_mul]
  unfold faceSign
  rw [Equiv.Perm.sign_symm]
  change (B.sign : ℝ) * _ * _ = _
  rw [mul_assoc, ← hQ, hB]
  rw [show (((MixedCorrectionCanonicalOrder.canonicalPermutation p c).sign * Equiv.Perm.sign Q : ℤˣ) : ℝ) =
      ((MixedCorrectionCanonicalOrder.canonicalPermutation p c).sign : ℝ) * (Equiv.Perm.sign Q : ℝ) by simp,
    mul_assoc, hs, mul_one, MixedCorrectionCanonicalOrder.canonicalPermutation_sign]
  simp [placementSign]

/-- Unconditional fixed-template correction integral, with the derived
negative two-odd placement coefficient and outgoing factor 3/2. -/
theorem normalized_sourceMajor :
    normalizedIntegral p.2.val (Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ)
      (sourceMajorOrder p ha hb hba hanchor) =
      -(3 / 2 : ℝ) * placementSign p *
        MixedGraphPhysicalPairSums.rawCorrectionQuotientWeight ⟨p,Γ⟩ := by
  let H := Γ.vertexSplit (canonicalTemplate c) p.2.val (selectedArity p).symm χ
  let order := sourceMajorOrder p ha hb hba hanchor
  let D' := TwoPointTemplateAdmissibility.correction_data p Γ c χ
  let hc' := TwoPointTemplateAdmissibility.count_shape_of_data p.2.val H D' ha hb hba order
  have h := normalized_integral_original p.2.val (selectedArity p).symm Γ (canonicalTemplate c) χ (canonicalLeg c)
    (MixedTwoPointTemplateWeight.correction_leg c) MixedTwoPointFaceWeight.bivector_edgeCount D'
    ha hb hba hanchor order hc'
  have hf : GeometricWeights.outgoingFactor (twoOddArity p.1 p.2) ≠ 0 := by
    unfold GeometricWeights.outgoingFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (twoOddArity p.1 p.2 w))
  rw [VertexSplitOutgoingFactor.bivector_split_factor _ p.2.val (selectedArity p).symm,
    mul_div_cancel_right₀ _ hf] at h
  have hs := faceSign_sourceMajor p Γ c χ D' ha hb hba hanchor order hc' rfl
  change faceSign p.2.val (selectedArity p).symm H MixedTwoPointFaceWeight.bivector_edgeCount D'
    ha hanchor order hc' * permutationSign (R := ℝ)
      (slotPermutation p.2.val (selectedArity p).symm Γ (canonicalTemplate c) χ (canonicalLeg c)
        (MixedTwoPointTemplateWeight.correction_leg c) MixedTwoPointFaceWeight.bivector_edgeCount D') = _ at hs
  rw [mul_assoc (3 / 2 : ℝ), hs] at h
  simpa only [neg_mul, mul_neg, mul_assoc, MixedGraphPhysicalPairSums.rawCorrectionQuotientWeight,
    order] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedCorrectionFaceSign
