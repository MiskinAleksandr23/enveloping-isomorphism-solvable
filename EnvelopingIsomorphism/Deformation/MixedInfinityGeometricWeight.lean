import EnvelopingIsomorphism.Deformation.MixedInfinityPhysicalAssembly
import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching
import EnvelopingIsomorphism.Deformation.InfinityProfileShapeOrderSign

/-! Actual normalized mixed infinity integrals, including outgoing-target
vanishing, in the literal extracted shape graph and transported edge order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace EnvelopingIsomorphism.Deformation.MixedInfinityGeometricWeight
open Kontsevich MixedGraphProfileCarrier MixedScalarBoundaryAssembly
open MixedInfinityPhysicalFace MixedInfinityPhysicalAssembly
open InfinityBoundaryGraphMatching InfinityBoundaryGraphIntegral
open MeasureTheory OrientedFormChangeVariables
open scoped Classical
variable {N : ℕ} (H : VectorGraph N 2) (F : FaceData)

def edgeOrder : Fin (Degree (0 : Fin (N+1)) F.l F.u) ≃
    KontsevichGraph.General.Edge (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex) :=
  (finCongr (degree_eq (mixed_dimension N) F)).trans
    (GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex))

def InnerClosed : Prop :=
  ∀ e, boundaryAnchoredInfinityCollapses F.l F.u (Sum.inl (H.graph.target e))

def shapeWeight : ℝ :=
  if hin : InnerClosed H F then
    GeometricWeights.geometricWeight (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
      (shapeOrder (edgeOrder H F)) else 0

theorem shapeOrder_sign :
    Equiv.Perm.sign ((shapeOrder (edgeOrder H F)).trans
      (GeometricWeights.canonicalOrder (shapeDegree (edgeOrder H F))).symm) = 1 := by
  apply InfinityProfileShapeOrderSign.reindex_sign_of_even_off
    (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex)
    (InfinityBoundaryGraphCoordinates.sourceEquiv (a := (0 : Fin (N+1)))).symm
    ((Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex).trans
      (degree_eq (mixed_dimension N) F).symm)
    (shapeDegree (edgeOrder H F)) H.vertex
  intro w hw
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities,hw]

theorem geometricWeight_eq_canonical (hin : InnerClosed H F) :
    GeometricWeights.geometricWeight (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
      (shapeOrder (edgeOrder H F)) =
    GeometricWeights.canonicalWeight (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
      (shapeDegree (edgeOrder H F)) := by
  let order := shapeOrder (edgeOrder H F)
  let canon := GeometricWeights.canonicalOrder (shapeDegree (edgeOrder H F))
  have he : (order.trans canon.symm).trans canon = order := by
    apply Equiv.ext
    intro j
    simp
  have h := GeometricWeights.geometricWeight_permute (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
    canon (order.trans canon.symm)
  rw [he] at h
  change GeometricWeights.geometricWeight _ _ = _ * _ at h
  rw [shapeOrder_sign,Units.val_one,Int.cast_one,one_mul] at h
  exact h

theorem shapeWeight_eq_canonical :
    shapeWeight H F = if hin : InnerClosed H F then
      GeometricWeights.canonicalWeight (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
        (shapeDegree (edgeOrder H F)) else 0 := by
  unfold shapeWeight
  split_ifs with hin
  · exact geometricWeight_eq_canonical H F hin
  · rfl

theorem canonicalShapeWeight_eq_originalLabels (hin : InnerClosed H F)
    (G : KontsevichGraph.General.Graph
      (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex) 1)
    (hG : ∀ e, G.target e = Sum.map id (fun _ : Fin 2 ↦ (0 : Fin 1)) (H.graph.target e)) :
    GeometricWeights.canonicalWeight (shapeGraph (a := (0 : Fin (N+1))) H.graph hin)
        (shapeDegree (edgeOrder H F)) =
      GeometricWeights.canonicalWeight G (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex) := by
  have hM : InfinityBoundaryGraphFactorization.shapeM F.l F.u = 1 :=
    (Fintype.card_coe _).trans F.card_eq
  have hN : InfinityBoundaryGraphFactorization.shapeN (0 : Fin (N+1)) = N := by
    simp [InfinityBoundaryGraphFactorization.shapeN,card_boundaryAnchoredInfinityFreeInterior]
  let e := (InfinityBoundaryGraphCoordinates.sourceEquiv (a := (0 : Fin (N+1)))).symm
  have he : shapeGraph (a := (0 : Fin (N+1))) H.graph hin = G.reindex e (finCongr hM) := by
    apply KontsevichGraph.General.Graph.ext
    funext ⟨v,j⟩
    rw [KontsevichGraph.General.Graph.reindex_target,hG]
    have lift : ∀ w : Fin (N+1) ⊕ Fin 2,
        ∀ hw : boundaryAnchoredInfinityCollapses F.l F.u (Sum.inl w),
        InfinityBoundaryGraphFactorization.shapeTarget (a := (0 : Fin (N+1))) w hw =
          (Equiv.sumCongr e.symm (finCongr hM).symm)
            (Sum.map id (fun _ : Fin 2 ↦ (0 : Fin 1)) w) := by
      intro w hw
      cases w with
      | inl w => rfl
      | inr w =>
        apply congrArg Sum.inr
        apply (finCongr hM).injective
        exact Subsingleton.elim _ _
    exact lift _ _
  rw [he]
  apply InfinityProfileShapeOrderSign.canonicalWeight_reindex_of_even_off G hN hM e (finCongr hM)
    (fun _ ↦ rfl) _ _ H.vertex
  intro w hw
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities,hw]

theorem nativeEdges_eq_originalEdges :
    nativeEdges (mixed_dimension N) F (mixedEdges H) = originalEdges H.graph (edgeOrder H F) := rfl

theorem normalization_mul_integral :
    MixedPairedEdgeRelabelling.normalization H *
      (∫ y in region (mixed_dimension N) F,
        density (form (mixed_dimension N) F (mixedEdges H)) y) = shapeWeight H F := by
  rw [integral_eq_neg_outwardIntegral,nativeEdges_eq_originalEdges]
  have hn : (∏ v : Fin (N+1),
      ((Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex v).factorial : ℝ)⁻¹) *
      ((2*Real.pi)^Degree (0 : Fin (N+1)) F.l F.u)⁻¹ =
      MixedPairedEdgeRelabelling.normalization H := by
    rw [degree_eq (mixed_dimension N) F]
    rfl
  unfold shapeWeight
  split_ifs with hin
  · have h := normalized_outwardIntegral_eq_shapeWeight H.graph hin F.outside F.all_inside
      F.ordered (edgeOrder H F)
    rw [hn] at h
    simpa only [mul_neg,neg_neg] using congrArg Neg.neg h
  · have hz : outwardIntegral F.outside F.all_inside (originalEdges H.graph (edgeOrder H F)) = 0 := by
      unfold outwardIntegral
      rw [neg_eq_zero]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      by_contra hne
      exact hin (graph_noOutgoing_of_nonzero H.graph F.outside F.all_inside (edgeOrder H F) y hy hne)
    rw [hz,neg_zero,mul_zero]

variable {H} (P : MixedPartition H)

/-- Both genuine infinity input slots carry the negative physical sign.
These are the two nullary binary-subset input terms. -/
theorem normalization_mul_nativeKind_infinity :
    MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .infinity =
      -shapeWeight H (face 0) - shapeWeight H (face 1) := by
  rw [nativeKind_infinity_eq_integrals,mul_sub,mul_neg,
    normalization_mul_integral,normalization_mul_integral]

end EnvelopingIsomorphism.Deformation.MixedInfinityGeometricWeight
