import EnvelopingIsomorphism.Deformation.MixedSourcePhysicalCoefficient
import EnvelopingIsomorphism.Deformation.MixedGraphSourceExtraction

/-! Every admissible adjacent source face belongs to an actual outgoing
orbit of one of the two canonical source templates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateOrbit
open scoped Classical
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open TwoPointSplitFaceAdmissibility TwoPointSplitFaceContraction
open MixedGraphActionSplits MixedGraphProfileCarrier UniformBinaryGraphs SchoutenGraphContraction
open VectorSplitOutgoingCovariance
variable {n : ℕ} (i : Fin (n+1))
abbrev Arity := vertexSplitArity (fun _ : Fin (n+1) ↦ 2) vectorBivectorArity i
variable (H : Graph (Arity i) 2)

theorem localTarget_permuteOutgoing
    (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v))) (e : Edge vectorBivectorArity) :
    localTarget i (H.permuteOutgoing τ) e =
      localTarget i H (outgoingEdgePerm (childOutgoing i τ) e) := by
  change H.target (outgoingEdgePerm τ (vertexSplitLocalEdge _ _ i e)) = _
  rw [outgoing_localEdge]
  rfl

theorem data_permuteOutgoing (D : Data i H)
    (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v))) : Data i (H.permuteOutgoing τ) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e,he,hu⟩ := D.unique
    refine ⟨(outgoingEdgePerm (childOutgoing i τ)).symm e, ?_, ?_⟩
    · dsimp only
      rw [localTarget_permuteOutgoing, Equiv.apply_symm_apply]
      exact he
    · intro f hf
      rw [localTarget_permuteOutgoing] at hf
      exact (outgoingEdgePerm (childOutgoing i τ)).apply_eq_iff_eq_symm_apply.mp (hu _ hf)
  · intro w hw j k ht
    change vertexSplitCollapseVertex i (H.target (outgoingEdgePerm τ
      (vertexSplitOutsideEdge _ _ i ⟨⟨w,j⟩,hw⟩))) =
      vertexSplitCollapseVertex i (H.target (outgoingEdgePerm τ
      (vertexSplitOutsideEdge _ _ i ⟨⟨w,k⟩,hw⟩))) at ht
    rw [outgoing_outsideEdge i rfl τ 0, outgoing_outsideEdge i rfl τ 0] at ht
    exact (quotientOutgoing i rfl τ 0 w).injective (D.coarse w hw ht)
  · intro e f he hf ht
    simp only [localTarget_permuteOutgoing] at he hf ht
    exact (outgoingEdgePerm (childOutgoing i τ)).injective (D.exits _ _ he hf ht)

theorem data_permuteOutgoing_iff
    (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v))) :
    Data i (H.permuteOutgoing τ) ↔ Data i H := by
  constructor
  · intro h
    have hh := data_permuteOutgoing i (H.permuteOutgoing τ) h (fun v ↦ (τ v).symm)
    have he : (H.permuteOutgoing τ).permuteOutgoing (fun v ↦ (τ v).symm) = H :=
      (Graph.outgoingGraphEquiv (Arity i) 2 τ).left_inv H
    rwa [he] at hh
  · exact fun h ↦ data_permuteOutgoing i H h τ

theorem local_internal_target (e : Edge vectorBivectorArity)
    (he : vertexSplitCollapseVertex i (localTarget i H e) = Sum.inl i) :
    localTarget i H e = Sum.inl (vertexSplitChild i (VectorSplitOutgoingAverage.receiver e.1)) := by
  obtain ⟨c,hc⟩ := (vertexSplitCollapse_eq_root_iff i _).mp he
  have hn : c ≠ e.1 := by
    intro h
    have hh := H.noLoops (vertexSplitLocalEdge _ _ i e).1 (vertexSplitLocalEdge _ _ i e).2
    apply hh
    exact hc.symm.trans (congrArg Sum.inl
      ((congrArg (vertexSplitChild i) h).trans (vertexSplitLocalEdge_source _ _ i e).symm))
  have hr : c = VectorSplitOutgoingAverage.receiver e.1 := by
    have hh (a b : Fin 2) (hab : a ≠ b) : a = VectorSplitOutgoingAverage.receiver b := by
      fin_cases a <;> fin_cases b <;> simp_all [VectorSplitOutgoingAverage.receiver]
    exact hh c e.1 hn
  exact hc.symm.trans (congrArg (fun v ↦ Sum.inl (vertexSplitChild i v)) hr)

theorem forward_exists (D : Data i H) (hi : forwardInternal i H) :
    ∃ E : SourceSplitData i, VectorSplitOutgoingAverage.splitGraph i rfl 0 E = H := by
  have h0 : vertexSplitCollapseVertex i (localTarget i H ⟨0,0⟩) = Sum.inl i := by
    change vertexSplitCollapseVertex i (H.target _) = _
    rw [hi, vertexSplitCollapseVertex_child]
  have hu (e : Edge vectorBivectorArity)
      (he : vertexSplitCollapseVertex i (localTarget i H e) = Sum.inl i) : e = ⟨0,0⟩ :=
    (ExistsUnique.unique D.unique he h0)
  have ho : H.SplitLegsOutside i vectorBivectorForwardLeg := by
    intro j hj
    have hh := congrArg Sigma.fst (hu _ hj)
    change (1 : Fin 2) = 0 at hh
    exact (by decide : (1 : Fin 2) ≠ 0) hh
  have hl : H.SplitLegsDistinct i vectorBivectorForwardLeg := by
    intro j k hjk
    have hh := D.exits _ _ (ho j) (ho k) hjk
    exact eq_of_heq (Sigma.mk.inj hh).2
  let Γ := H.contractedGraph i rfl vectorBivectorForwardLeg D.coarse ho hl
  let χ := H.contractedChoices i rfl vectorBivectorForwardLeg D.coarse ho hl
  refine ⟨⟨Γ,χ⟩, ?_⟩
  have he := H.vertexSplit_contracted i rfl vectorBivectorForwardLeg D.coarse ho hl
    (forwardLegsComplete i H hi)
  rw [contractedTemplate_forward i H D.coarse hi ho hl] at he
  exact he

theorem backward_exists (D : Data i H) (hi : backwardInternal i H) :
    ∃ E : SourceSplitData i, VectorSplitOutgoingAverage.splitGraph i rfl 1 E = H := by
  have h0 : vertexSplitCollapseVertex i (localTarget i H ⟨1,0⟩) = Sum.inl i := by
    change vertexSplitCollapseVertex i (H.target _) = _
    rw [hi, vertexSplitCollapseVertex_child]
  have hu (e : Edge vectorBivectorArity)
      (he : vertexSplitCollapseVertex i (localTarget i H e) = Sum.inl i) : e = ⟨1,0⟩ :=
    (ExistsUnique.unique D.unique he h0)
  have ho : H.SplitLegsOutside i (vectorBivectorBackwardLeg 1) := by
    intro j hj
    have hh := hu _ hj
    fin_cases j
    · have hh' := congrArg Sigma.fst hh
      exact (by decide : (0 : Fin 2) ≠ 1) hh'
    · have hh' := congrArg (fun e : Edge vectorBivectorArity ↦ e.2.val) hh
      exact (by decide : (1 : ℕ) ≠ 0) hh'
  have hl : H.SplitLegsDistinct i (vectorBivectorBackwardLeg 1) := by
    intro j k hjk
    have hh := D.exits _ _ (ho j) (ho k) hjk
    have hleg : Function.Injective (vectorBivectorBackwardLeg (1 : Equiv.Perm (Fin 2))) := by
      intro a b hab
      have h := congrArg (vectorBivectorBackward 1).target hab
      have ha := (MixedTwoPointTemplateWeight.vectorBackward_leg 1 _ a).mpr rfl
      have hb := (MixedTwoPointTemplateWeight.vectorBackward_leg 1 _ b).mpr rfl
      rw [ha,hb] at h
      exact Sum.inr.inj h
    exact hleg hh
  let Γ := H.contractedGraph i rfl (vectorBivectorBackwardLeg 1) D.coarse ho hl
  let χ := H.contractedChoices i rfl (vectorBivectorBackwardLeg 1) D.coarse ho hl
  refine ⟨⟨Γ,χ⟩, ?_⟩
  have he := H.vertexSplit_contracted i rfl (vectorBivectorBackwardLeg 1) D.coarse ho hl
    (backwardLegsComplete i H 1 hi)
  rw [contractedTemplate_backward i H D.coarse 1 hi ho hl] at he
  exact he

def senderSwap : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v)) :=
  rootOutgoing (vertexSplitChild i 1) (vertexSplitArity_child _ vectorBivectorArity i 1) (Equiv.swap 0 1)

theorem senderSwap_child : childOutgoing i (senderSwap i) 1 = Equiv.swap 0 1 := by
  apply Equiv.ext
  intro j
  change Fin.cast (vertexSplitArity_child _ vectorBivectorArity i 1)
    (rootOutgoing (vertexSplitChild i 1) (vertexSplitArity_child _ vectorBivectorArity i 1)
      (Equiv.swap 0 1) (vertexSplitChild i 1)
      (Fin.cast (vertexSplitArity_child _ vectorBivectorArity i 1).symm j)) = _
  rw [rootOutgoing_root]
  simp

/-- Every admissible original graph is an outgoing image of a genuine
canonical split, including a binary internal arrow in its second slot. -/
theorem exists_template_outgoing (D : Data i H) :
    ∃ a : Fin 2, ∃ E : SourceSplitData i,
      ∃ τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v)),
        H = (VectorSplitOutgoingAverage.splitGraph i rfl a E).permuteOutgoing τ := by
  obtain ⟨⟨c,s⟩,he,_⟩ := D.unique
  have ht := local_internal_target i H ⟨c,s⟩ he
  fin_cases c
  · fin_cases s
    obtain ⟨E,hE⟩ := forward_exists i H D ht
    refine ⟨0,E,fun _ ↦ Equiv.refl _, ?_⟩
    rw [hE]
    rfl
  · fin_cases s
    · obtain ⟨E,hE⟩ := backward_exists i H D ht
      refine ⟨1,E,fun _ ↦ Equiv.refl _, ?_⟩
      rw [hE]
      rfl
    · have hi : backwardInternal i (H.permuteOutgoing (senderSwap i)) := by
        change localTarget i (H.permuteOutgoing (senderSwap i)) ⟨1,0⟩ = _
        rw [localTarget_permuteOutgoing]
        simp only [outgoingEdgePerm_apply, senderSwap_child, Equiv.swap_apply_left]
        exact ht
      obtain ⟨E,hE⟩ := backward_exists i (H.permuteOutgoing (senderSwap i))
        (data_permuteOutgoing i H D (senderSwap i)) hi
      refine ⟨1,E,fun v ↦ (senderSwap i v).symm, ?_⟩
      rw [hE]
      exact ((Graph.outgoingGraphEquiv (Arity i) 2 (senderSwap i)).left_inv H).symm

theorem split_data (a : Fin 2) (E : SourceSplitData i) :
    Data i (VectorSplitOutgoingAverage.splitGraph i rfl a E) := by
  fin_cases a
  · exact TwoPointTemplateAdmissibility.source_data E.1 i 0 E.2
  · exact TwoPointTemplateAdmissibility.source_data E.1 i 1 E.2

theorem data_iff_exists_template_outgoing :
    Data i H ↔ ∃ a : Fin 2, ∃ E : SourceSplitData i,
      ∃ τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v)),
        H = (VectorSplitOutgoingAverage.splitGraph i rfl a E).permuteOutgoing τ := by
  constructor
  · exact exists_template_outgoing i H
  · rintro ⟨a,E,τ,rfl⟩
    exact data_permuteOutgoing i _ (split_data i a E) τ

open MixedSourcePhysicalCoefficient MixedGraphOutgoingPairNormalization

/-- The physical coefficient transforms with its true full outgoing sign,
including the one-slot vector row. -/
theorem physicalCoefficient_permuteOutgoing
    (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v))) :
    sourcePhysicalCoefficient
        (ofProfile (vertexSplitChild i 0) (actionSplitArity i) (H.permuteOutgoing τ)) (sourceChildPair i) =
      GeneralGraphOutgoingAverage.sign τ *
        sourcePhysicalCoefficient
          (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) (sourceChildPair i) := by
  rw [sourcePhysicalCoefficient_eq_nativeAverage, sourcePhysicalCoefficient_eq_nativeAverage,
    GeneralGraphOutgoingAverage.average_permuteOutgoing]

theorem profile_zero_of_not_data (w : BinaryGraph (n+1) 2 → ℝ) (a : Fin 2) (hD : ¬ Data i H) :
    VectorSplitOutgoingAverage.profile i rfl w a H = 0 := by
  apply Finset.sum_eq_zero
  intro E _
  apply if_neg
  intro he
  exact hD (he ▸ split_data i a E)

theorem pairProfile_zero_of_not_data (w : BinaryGraph (n+1) 2 → ℝ) (hD : ¬ Data i H) :
    VectorSplitOutgoingAverage.pairProfile i rfl w H = 0 := by
  simp only [VectorSplitOutgoingAverage.pairProfile, Pi.sub_apply, Pi.smul_apply,
    profile_zero_of_not_data i H w _ hD, smul_zero, sub_self]

/-- Every nonzero contribution to the finite source fibre has the actual
discrete two-point data. Thus no scalar support assumption is needed. -/
theorem physicalCoefficient_zero_of_not_data (hD : ¬ Data i H) :
    sourcePhysicalCoefficient
      (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) (sourceChildPair i) = 0 := by
  rw [sourcePhysicalCoefficient_eq_nativeAverage, GeneralGraphOutgoingAverage.average]
  have hz (τ : (v : Fin (n+2)) → Equiv.Perm (Fin (Arity i v))) :
      VectorSplitOutgoingAverage.pairProfile i rfl (GraphCanonicalBinaryWeights.rawBinaryWeight (n+1))
        (H.permuteOutgoing (fun v ↦ (τ v).symm)) = 0 :=
    pairProfile_zero_of_not_data i _ _ (fun h ↦
      hD ((data_permuteOutgoing_iff i H (fun v ↦ (τ v).symm)).mp h))
  simp only [hz, mul_zero, Finset.sum_const_zero]

/-- The geometric integral also vanishes outside the same discrete support,
since a nonzero density would construct the missing contraction data. -/
theorem normalizedIntegral_zero_of_not_data (hD : ¬ Data i H)
    {anchor a b : Fin (n+2)}
    (ha : a ∈ TwoPointBinaryFaceAdmissibility.cluster i)
    (hb : b ∈ TwoPointBinaryFaceAdmissibility.cluster i) (hba : b ≠ a)
    (order : Fin (InteriorGraphFaceCoordinates.shapeDegree a b (TwoPointBinaryFaceAdmissibility.cluster i) +
      InteriorGraphFaceCoordinates.coarseDegree anchor a (TwoPointBinaryFaceAdmissibility.cluster i) 2) ≃
      Edge (Arity i)) :
    TwoPointSplitFaceWeight.normalizedIntegral i H order = 0 := by
  unfold TwoPointSplitFaceWeight.normalizedIntegral
  have hz : ∀ y ∈ InteriorFiberAngleSplit.integrationRegion
      (InteriorGraphFaceCoordinates.shapeN a b (TwoPointBinaryFaceAdmissibility.cluster i)) ×ˢ
      GeometricWeights.realDomain
        (InteriorGraphFaceCoordinates.coarseN anchor a (TwoPointBinaryFaceAdmissibility.cluster i)) 2,
      InteriorGraphFaceCoordinates.realFaceDensity (orderedEdges i H order) y = 0 := by
    intro y hy
    by_contra hn
    exact hD (ofNonzero i H order ha hb hba y hy hn)
  rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hz, mul_zero, mul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateOrbit
