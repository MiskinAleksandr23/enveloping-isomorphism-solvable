import EnvelopingIsomorphism.Deformation.MainRealUnconditionalWeight
import EnvelopingIsomorphism.Deformation.MixedRealPhysicalFaces
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedRealForestOrderedSlotSign
import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestProfileRowSign

/-! All-graph real-face matching for the actual one-vector arity profile.
Incidence conditions are consequences of a nonempty admissible graft fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.MixedRealUnconditionalWeight
open Kontsevich KontsevichGraph.General MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
open BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection BoundaryGraphCanonicalFibreMatching
open BoundaryGraphExtractedOrders BoundaryGraphNativeTransport
open scoped Classical BigOperators

section General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m+1)} {q : Fin n → ℕ}

theorem noOutgoing_of_innerClosed (G : Graph q m)
    (ha : a ∈ S) (hi : i ∉ S) (hlt : l < u)
    (hclosed : (orderedGraph G ha hi hlt).InnerClosed (centerSlot hlt.le)) :
    ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S →
      boundaryClusterCollapses S l u (Sum.inl (G.target e)) := by
  intro e he
  obtain ⟨⟨v,j⟩,hv⟩ := (innerSlotEquiv (q := q) ha hi).surjective ⟨e,he⟩
  have hv' := congrArg Subtype.val hv
  rw [innerSlotEquiv_val] at hv'
  have hc := hclosed ⟨v,j⟩
  have hh := (graftCollapse_eq_slot_iff _ _).mpr hc
  rw [orderedGraph, Graph.reindexForGraft_target_inner] at hh
  change collapsedVertex ha hi hlt (G.target _) = _ at hh
  rw [hv'] at hh
  exact (MainRealUnconditionalWeight.collapsedVertex_eq_slot_iff ha hi hlt _).mp hh

theorem normalized_integral_eq_signed_graftProfile_all (G : Graph q m)
    (ha : a ∈ S) (hi : i ∉ S) (hlt : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hc : Fintype.card {j // (graphEdges G order j).1 ∈ S} = shapeDegree a S l u) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2*Real.pi)^(shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u+1),
        orderedRealDensity (graphEdges G order) hlt.le z ∂volume.prod volume) =
      fibreSign G ha hi order hc hlt *
        GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
          (outerCoefficient G ha hi order hc) (innerCoefficient G ha hi order hc hlt)
          (orderedGraph G ha hi hlt) := by
  by_cases hadm : (orderedGraph G ha hi hlt).InnerClosed (centerSlot hlt.le) ∧
      (orderedGraph G ha hi hlt).CoarseDistinct (centerSlot hlt.le)
  · exact normalized_integral_eq_signed_graftProfile G ha hi order hc hlt
      (noOutgoing_of_innerClosed G ha hi hlt hadm.1) hadm.2
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible _ _ _ _ hadm, mul_zero]
    have hz : (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u+1),
        orderedRealDensity (graphEdges G order) hlt.le z ∂volume.prod volume) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      exact nativeFaceDensity_zero_of_orderedGraph_not_admissible G ha hi hlt order hadm
        (orderedRealFace hlt.le z) ((orderedRealFace_open_iff ha hi hlt.le z).mpr hz)
    rw [hz, mul_zero]

end General

open MixedRealPhysicalFaces MixedGraphProfileCarrier MixedScalarBoundaryAssembly
variable {N : ℕ} (H : VectorGraph N 2) (K : Key N H.vertex)

def edgeOrder : Fin (shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u) ≃
    KontsevichGraph.General.Edge (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex) :=
  (finCongr K.degree_eq).trans
    (GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex))

theorem physicalEdges_eq_graphEdges : physicalEdges H K = graphEdges H.graph (edgeOrder H K) := rfl

theorem internal_count :
    Fintype.card {j // (graphEdges H.graph (edgeOrder H K) j).1 ∈ K.S} = shapeDegree K.inside K.S K.l K.u := by
  rw [card_graphEdges_source, shapeDegree_eq_source_card K.inside_mem]
  change (∑ v ∈ K.S, oneExceptionalArity 1 H.vertex v) = _
  rw [sum_single_vector_arity, K.property.2.2.2]
  have hS : 0 < K.S.card := Finset.card_pos.mpr K.property.1
  split_ifs <;> omega

theorem normalized_physicalValue_eq_graftProfile :
    MixedPairedEdgeRelabelling.normalization H * physicalValue H K =
      fibreSign H.graph K.inside_mem K.outside_not_mem (edgeOrder H K) (internal_count H K) K.block_lt *
        GraphGeneralWeightedGraft.graftProfile (centerSlot K.block_lt.le)
          (outerCoefficient H.graph K.inside_mem K.outside_not_mem (edgeOrder H K) (internal_count H K))
          (innerCoefficient H.graph K.inside_mem K.outside_not_mem (edgeOrder H K) (internal_count H K) K.block_lt)
          (orderedGraph H.graph K.inside_mem K.outside_not_mem K.block_lt) := by
  have he := normalized_integral_eq_signed_graftProfile_all H.graph K.inside_mem K.outside_not_mem
    K.block_lt (edgeOrder H K) (internal_count H K)
  have hn : (∏ v : Fin (N+1), ((Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex v).factorial : ℝ)⁻¹) *
      ((2*Real.pi)^(shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u))⁻¹ =
      MixedPairedEdgeRelabelling.normalization H := by
    rw [K.degree_eq]
    rfl
  rw [hn, ← physicalEdges_eq_graphEdges] at he
  exact he

theorem nativeOrderedPermutation_key :
    (Equiv.Perm.sign (nativeOrderedPermutation (i := K.outside) (a := K.inside) (S := K.S)
      K.property.2.2.1) : ℝ) = if H.vertex ∈ K.S then -1 else 1 := by
  have h : ∀ l u : Fin 3, ∀ hle : l ≤ u,
      (boundaryClusterBlock l u).card = (if H.vertex ∈ K.S then 1 else 2) →
      (Equiv.Perm.sign (nativeOrderedPermutation (i := K.outside) (a := K.inside) (S := K.S) hle) : ℝ) =
        if H.vertex ∈ K.S then -1 else 1 := by
    intro l u hle hcard
    by_cases hv : H.vertex ∈ K.S
    · rw [if_pos hv] at hcard ⊢
      have hc : (l = 0 ∧ u = 1) ∨ (l = 1 ∧ u = 2) := by
        have he : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 1 →
            (l = 0 ∧ u = 1) ∨ (l = 1 ∧ u = 2) := by decide
        exact he l u hle hcard
      rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [MixedRealForestOrderedSlotSign.nativeOrderedPermutation_slotZero]
      · simp [MixedRealForestOrderedSlotSign.nativeOrderedPermutation_slotOne]
    · rw [if_neg hv] at hcard ⊢
      have hc : l = 0 ∧ u = 2 := by
        have he : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 2 →
            l = 0 ∧ u = 2 := by decide
        exact he l u hle hcard
      rcases hc with ⟨rfl,rfl⟩
      simp [MixedRealForestOrderedSlotSign.nativeOrderedPermutation_fullBlock]
  exact h K.l K.u K.property.2.2.1 K.property.2.2.2

/-- The actual canonical one-vector edge order cancels all extracted-row
and cluster-block signs, for every geometric real cluster. -/
theorem edgeOrderingSign_key :
    RealForestGraftSlotMatching.edgeOrderingSign H.graph K.inside_mem K.outside_not_mem
      (edgeOrder H K) (internal_count H K) = 1 := by
  apply RealForestProfileRowSign.mixed_edgeOrderingSign_eq_one H.vertex H.graph
    K.inside_mem K.outside_not_mem (edgeOrder H K) (internal_count H K)
  rintro ⟨v,j⟩
  change ((vertexMajorEdgeEquiv _).symm ⟨v,j⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val]

/-- Only the computed geometric chamber sign remains in the genuine fibre. -/
theorem fibreSign_key :
    fibreSign H.graph K.inside_mem K.outside_not_mem (edgeOrder H K)
      (internal_count H K) K.block_lt = if H.vertex ∈ K.S then -1 else 1 := by
  rw [RealForestGraftSlotMatching.fibreSign_eq_nativeOrdered_mul_edgeOrderingSign,
    edgeOrderingSign_key, mul_one, nativeOrderedPermutation_key]

end EnvelopingIsomorphism.Deformation.MixedRealUnconditionalWeight
