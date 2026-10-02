import EnvelopingIsomorphism.Deformation.MainRealPhysicalIndex
import EnvelopingIsomorphism.Deformation.Kontsevich.MainRealGraftPhysicalCoefficient
import EnvelopingIsomorphism.Deformation.MainPairedGeometricMatching

/-! Every binary real face has its actual physical graft coefficient.
Invalid graft fibres vanish both geometrically and in the finite pushforward. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.MainRealUnconditionalWeight
open Kontsevich KontsevichGraph.General UniformBinaryGraphs MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
open BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection BoundaryGraphCanonicalFibreMatching
open BoundaryGraphNativeTransport MainRealGraftPhysicalCoefficient
open scoped Classical BigOperators

section General
variable {N M : ℕ} {i a : Fin N} {S : Finset (Fin N)} {l u : Fin (M+1)}

theorem collapsedVertex_eq_slot_iff (ha : a ∈ S) (hi : i ∉ S) (hlt : l < u)
    (v : KontsevichGraph.General.Vertex N M) :
    collapsedVertex ha hi hlt v = Sum.inr (centerSlot hlt.le) ↔
      boundaryClusterCollapses S l u (Sum.inl v) := by
  cases v with
  | inl v =>
    by_cases hv : v ∈ S
    · simp [collapsedVertex_internal_inside ha hi hlt v hv, boundaryClusterCollapses, hv]
    · simp [collapsedVertex_internal_outside ha hi hlt v hv, boundaryClusterCollapses, hv]
  | inr v =>
    by_cases hv : v ∈ boundaryClusterBlock l u
    · simp [collapsedVertex_external_inside ha hi hlt v hv, boundaryClusterCollapses, hv]
    · rw [collapsedVertex_external_outside ha hi hlt v hv]
      simp [boundaryClusterCollapses, hv, Fin.succAbove_ne]

theorem binary_noOutgoing_of_innerClosed (H : BinaryGraph N M)
    (ha : a ∈ S) (hi : i ∉ S) (hlt : l < u)
    (hclosed : (orderedGraph H ha hi hlt).InnerClosed (centerSlot hlt.le)) :
    ∀ e : KontsevichGraph.General.Edge (fun _ : Fin N ↦ 2), e.1 ∈ S →
      boundaryClusterCollapses S l u (Sum.inl (H.target e)) := by
  rintro ⟨v,j⟩ hv
  have he : anchoredPartitionEquiv ha hi
      (Fin.natAdd (coarseN i S + 1) (shapeSourceEquiv ha ⟨v,hv⟩)) = v := by
    rw [anchoredPartition_inner, Equiv.symm_apply_apply]
  have hc := hclosed ⟨shapeSourceEquiv ha ⟨v,hv⟩,j⟩
  have hh := (graftCollapse_eq_slot_iff _ _).mpr hc
  rw [orderedGraph, Graph.reindexForGraft_target_inner] at hh
  change collapsedVertex ha hi hlt (H.target ⟨_,j⟩) = _ at hh
  rw [he] at hh
  exact (collapsedVertex_eq_slot_iff ha hi hlt _).mp hh

theorem binary_internal_count (H : BinaryGraph N M)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin N ↦ 2))
    (ha : a ∈ S) (hsize : shapeM l u = 2) :
    Fintype.card {j // (graphEdges H order j).1 ∈ S} = shapeDegree a S l u := by
  rw [card_graphEdges_source, shapeDegree_eq_source_card ha]
  have hc : (boundaryClusterBlock l u).card = 2 := by simpa [shapeM] using hsize
  rw [hc]
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨a,ha⟩
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  omega

theorem normalized_integral_eq_signed_graftProfile_all (H : BinaryGraph N M)
    (ha : a ∈ S) (hi : i ∉ S) (hlt : l < u)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin N ↦ 2))
    (hc : Fintype.card {j // (graphEdges H order j).1 ∈ S} = shapeDegree a S l u) :
    (∏ _v : Fin N, ((2 : ℕ).factorial : ℝ)⁻¹) *
      ((2*Real.pi)^(shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u+1),
        orderedRealDensity (graphEdges H order) hlt.le z ∂volume.prod volume) =
      fibreSign H ha hi order hc hlt *
        GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
          (outerCoefficient H ha hi order hc) (innerCoefficient H ha hi order hc hlt)
          (orderedGraph H ha hi hlt) := by
  by_cases hadm : (orderedGraph H ha hi hlt).InnerClosed (centerSlot hlt.le) ∧
      (orderedGraph H ha hi hlt).CoarseDistinct (centerSlot hlt.le)
  · exact normalized_integral_eq_signed_graftProfile H ha hi order hc hlt
      (binary_noOutgoing_of_innerClosed H ha hi hlt hadm.1) hadm.2
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible _ _ _ _ hadm, mul_zero]
    have hz : (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
          GeometricWeights.realDomain (coarseN i S) (outsideM l u+1),
        orderedRealDensity (graphEdges H order) hlt.le z ∂volume.prod volume) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      exact nativeFaceDensity_zero_of_orderedGraph_not_admissible H ha hi hlt order hadm
        (orderedRealFace hlt.le z) ((orderedRealFace_open_iff ha hi hlt.le z).mpr hz)
    rw [hz, mul_zero]

end General

open MainRealPhysicalFaces MainRealPhysicalIndex MainScalarBoundaryAssembly
variable {n : ℕ} (H : BinaryGraph (n+2) 3) (K : Key n)

def edgeOrder : Fin (shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u) ≃
    KontsevichGraph.General.Edge (fun _ : Fin (n+2) ↦ 2) :=
  (finCongr K.degree_eq).trans (GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)))

theorem edgeOrder_sourceMajor (e : KontsevichGraph.General.Edge (fun _ : Fin (n+2) ↦ 2)) :
    ((edgeOrder K).symm e).val = 2*e.1.val+e.2.val := by
  rcases e with ⟨v,j⟩
  change ((vertexMajorEdgeEquiv (fun _ : Fin (n+2) ↦ 2)).symm ⟨v,j⟩).val = _
  rw [vertexMajorEdgeEquiv_symm_val, edgePrefix_constant]

theorem physicalEdges_eq_graphEdges : physicalEdges H K = graphEdges H (edgeOrder K) := rfl

theorem shapeM_key : shapeM K.l K.u = 2 := by
  simpa [shapeM] using K.property.2.2.2

theorem physicalSlot_key : physicalSlot K.block_lt (shapeM_key K) = slot K := Fin.ext rfl

theorem nativeOrderedPermutation_key :
    -(Equiv.Perm.sign (nativeOrderedPermutation (i := K.outside) (a := K.inside) (S := K.S)
      K.property.2.2.1) : ℝ) = (-1 : ℝ)^(slot K).val := by
  have h : ∀ l u : Fin 4, ∀ hle : l ≤ u, (boundaryClusterBlock l u).card = 2 →
      -(Equiv.Perm.sign (nativeOrderedPermutation (i := K.outside) (a := K.inside) (S := K.S) hle) : ℝ) =
        (-1 : ℝ)^l.val := by
    intro l u hle hcard
    have hc : (l = 0 ∧ u = 2) ∨ (l = 1 ∧ u = 3) := by
      have he : ∀ l u : Fin 4, l ≤ u → (boundaryClusterBlock l u).card = 2 →
          (l = 0 ∧ u = 2) ∨ (l = 1 ∧ u = 3) := by decide
      exact he l u hle hcard
    rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [RealForestOrderedSlotSign.nativeOrderedPermutation_slotZero]
    · simp [RealForestOrderedSlotSign.nativeOrderedPermutation_slotOne]
  exact h K.l K.u K.property.2.2.1 K.property.2.2.2

/-- Every original graph is included. Both failed incidence and duplicate
coarse targets give zero on both sides by actual graft-fibre support. -/
theorem normalized_physicalValue_eq_rawCluster :
    MainPairedGeometricMatching.normalization n * physicalValue H K =
      (-1 : ℝ)^(slot K).val *
        GraphBinaryClusterSums.rawClusterCoefficient (slot K)
          (GraphAssociatorProfiles.castVertices (anchoredCount K.inside_mem K.outside_not_mem).symm H)
          (physicalCluster K.inside_mem K.outside_not_mem) := by
  let hc := binary_internal_count H (edgeOrder K) K.inside_mem (shapeM_key K)
  have he := normalized_integral_eq_signed_graftProfile_all H K.inside_mem K.outside_not_mem
    K.block_lt (edgeOrder K) hc
  rw [RealForestGraftSlotMatching.fibreSign_eq_nativeOrdered_mul_edgeOrderingSign,
    RealForestBinaryRowSign.edgeOrderingSign_eq_one H K.inside_mem K.outside_not_mem
      (edgeOrder K) hc (edgeOrder_sourceMajor K), mul_one,
    canonical_graft_eq_rawCluster H K.inside_mem K.outside_not_mem (edgeOrder K) hc K.block_lt (shapeM_key K),
    physicalSlot_key] at he
  have hn : (∏ _v : Fin (n+2), ((2 : ℕ).factorial : ℝ)⁻¹) *
      ((2*Real.pi)^(shapeDegree K.inside K.S K.l K.u + coarseDegree K.outside K.S K.l K.u))⁻¹ =
      MainPairedGeometricMatching.normalization n := by
    rw [K.degree_eq]
    rfl
  rw [hn, ← physicalEdges_eq_graphEdges] at he
  have hh := congrArg Neg.neg he
  simpa only [physicalValue, mul_neg, ← neg_mul, nativeOrderedPermutation_key] using hh

end EnvelopingIsomorphism.Deformation.MainRealUnconditionalWeight
