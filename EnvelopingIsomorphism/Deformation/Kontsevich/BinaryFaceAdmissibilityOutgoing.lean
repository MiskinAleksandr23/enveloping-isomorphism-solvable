import EnvelopingIsomorphism.Deformation.Kontsevich.BinaryTemplateOrbitReconstruction

/-! Admissibility of actual binary-child faces under every outgoing permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BinaryFaceAdmissibilityOutgoing
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open TwoPointSplitFaceContraction TwoPointSplitFaceAdmissibility BinarySplitOutgoingCovariance
open scoped Classical
variable {n m : ℕ} {q : Fin (n + 1) → ℕ} (r : Fin (n + 1)) (hq : q r = 3)
    (H : Graph (vertexSplitArity q bivectorArity r) m)
    (τ : (w : Fin (n + 2)) → Equiv.Perm (Fin (vertexSplitArity q bivectorArity r w)))

theorem localTarget_permuteOutgoing (e : KontsevichGraph.General.Edge bivectorArity) :
    localTarget r (H.permuteOutgoing τ) e =
      localTarget r H (outgoingEdgePerm (childOutgoing r τ) e) := by
  change H.target (outgoingEdgePerm τ (vertexSplitLocalEdge q bivectorArity r e)) = _
  exact congrArg H.target (outgoing_localEdge r τ e)

include hq in
theorem data_permuteOutgoing (D : Data r H) : Data r (H.permuteOutgoing τ) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e,he,hu⟩ := D.unique
    refine ⟨(outgoingEdgePerm (childOutgoing r τ)).symm e, ?_, ?_⟩
    · dsimp only
      rw [localTarget_permuteOutgoing, Equiv.apply_symm_apply]
      exact he
    · intro f hf
      apply (outgoingEdgePerm (childOutgoing r τ)).injective
      rw [Equiv.apply_symm_apply]
      apply hu
      simpa only [localTarget_permuteOutgoing] using hf
  · intro w hw j k he
    apply (quotientOutgoing r hq τ 0 w).injective
    apply D.coarse w hw
    change vertexSplitCollapseVertex r (H.target (outgoingEdgePerm τ
      (vertexSplitOutsideEdge q bivectorArity r ⟨⟨w,j⟩,hw⟩))) =
      vertexSplitCollapseVertex r (H.target (outgoingEdgePerm τ
        (vertexSplitOutsideEdge q bivectorArity r ⟨⟨w,k⟩,hw⟩))) at he
    simpa only [outgoing_outsideEdge r hq τ 0, outgoingEdgePerm_apply] using he
  · intro e f he hf h
    apply (outgoingEdgePerm (childOutgoing r τ)).injective
    apply D.exits
    · simpa only [localTarget_permuteOutgoing] using he
    · simpa only [localTarget_permuteOutgoing] using hf
    · simpa only [localTarget_permuteOutgoing] using h

include hq in
theorem data_permuteOutgoing_iff : Data r (H.permuteOutgoing τ) ↔ Data r H := by
  constructor
  · intro h
    have hh := data_permuteOutgoing r hq (H.permuteOutgoing τ) (fun w => (τ w).symm) h
    have he : (H.permuteOutgoing τ).permuteOutgoing (fun w => (τ w).symm) = H := by
      apply Graph.ext
      funext e
      rcases e with ⟨w,j⟩
      change H.target ⟨w,τ w ((τ w).symm j)⟩ = H.target ⟨w,j⟩
      rw [Equiv.apply_symm_apply]
    rwa [he] at hh
  · exact data_permuteOutgoing r hq H τ

end EnvelopingIsomorphism.Deformation.Kontsevich.BinaryFaceAdmissibilityOutgoing
