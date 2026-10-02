import EnvelopingIsomorphism.Deformation.MainPureOrbitAssembly
import EnvelopingIsomorphism.Deformation.MainPureInfinityVanishing
import EnvelopingIsomorphism.Deformation.MainPurePhysicalIntegral
import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling

/-! The original mixed pure-boundary contribution is the one physical
output face. Its boundary block is all of the two boundary labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPurePhysicalAssembly
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open PureForestSimpleCluster (lower upper)
open MixedScalarBoundaryAssembly MixedPairedCoreData MainPurePhysicalFace MainPureOrbitAssembly
open MeasureTheory OrientedFormChangeVariables
open scoped Classical

def face : FaceData 2 where
  l := 0
  u := 2
  a := 0
  b := 1
  ordered := by decide
  left_mem := by decide
  right_mem := by decide
  endpoints := by decide
  left_eq := rfl
  right_eq := rfl
  card_eq := by decide

variable {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2} (P : MixedPartition H)

theorem nativeKind_pureBoundary_eq_cluster :
    nativeKindBoundary P .pureBoundary = clusterValue (ofMixed P) face := by
  unfold nativeKindBoundary ForestRadialFaceLocalization.classifiedContribution
  simp only [Finset.mul_sum,clusterValue,orbitSum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : kind 0 j.val o = .pureBoundary
  · rw [if_pos ho]
    rw [← ForestRadialFaceLocalization.contribution_eq_integral_source
      (mixed_dimension N) j.val o (P.partition j) (mixedEdges H) (mixedEdges_noLoops H)
      (P.localizer j) (P.localization j)]
    change PairedData.orbitValue (ofMixed P) j o = _
    by_cases hc : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card = 2
    · have hh : ∀ l u : Fin 3, l ≤ u → (boundaryClusterBlock l u).card = 2 →
          l = 0 ∧ u = 2 := by decide
      obtain ⟨hl,hu⟩ := hh _ _ (block_order 0 j.val (RealForestCoarsePositions.node j.val o)) hc
      rw [if_pos ⟨ho,hl,hu⟩]
    · have hz := MainPureInfinityVanishing.mixed_pure_orbitValue_eq_zero P j o ho hc
      have hn : ¬ (kind 0 j.val o = .pureBoundary ∧ lower j.val o = face.l ∧ upper j.val o = face.u) := by
        rintro ⟨_,hl,hu⟩
        exact hc (by rw [hl,hu]; exact face.card_eq)
      rw [hz,if_neg hn]
  · simp only [ho,false_and,if_false,mul_zero]

/-- No support, coverage, orientation, or integrability matching premise is
assumed: all are inherited from the genuine finite mixed Stokes partition. -/
theorem nativeKind_pureBoundary_eq_integral :
    nativeKindBoundary P .pureBoundary =
      ∫ y in region (mixed_dimension N) face,
        density (form (mixed_dimension N) face (mixedEdges H)) y := by
  rw [nativeKind_pureBoundary_eq_cluster,clusterValue_eq_integral]
  simp [face]

theorem nativeKind_pureBoundary_eq_rawIntegral :
    nativeKindBoundary P .pureBoundary =
      GeometricWeights.rawIntegral (fun j ↦ PureBoundaryGraphQuotient.quotientEdge face.ordered
        (mixedEdges H (finCongr (degree_eq (mixed_dimension N) face) j))) := by
  rw [nativeKind_pureBoundary_eq_integral,MainPurePhysicalIntegral.integral_eq_rawIntegral]

open PureBoundaryGraphMatching BoundaryGraphFaceFactorization

theorem quotient_edgeCount :
    ∑ v, Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex v =
      GraphForms.dimension N (outsideM face.l face.u + 1) :=
  (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex).trans
    (degree_eq (mixed_dimension N) face).symm

/-- The normalized pure endpoint is the genuine quotient-graph weight;
if collapsing the two boundary labels repeats an outgoing target, it is zero. -/
theorem normalization_mul_nativeKind_pureBoundary :
    MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .pureBoundary =
      if hd : QuotientDistinct face.ordered H.graph then
        GeometricWeights.canonicalWeight (quotientGraph face.ordered H.graph hd)
          (quotient_edgeCount (H := H)) else 0 := by
  rw [nativeKind_pureBoundary_eq_rawIntegral]
  have he : (fun j ↦ PureBoundaryGraphQuotient.quotientEdge face.ordered
      (mixedEdges H (finCongr (degree_eq (mixed_dimension N) face) j))) =
      fun j ↦ PureBoundaryGraphQuotient.quotientEdge face.ordered
        (originalEdges H.graph (GeometricWeights.canonicalOrder (quotient_edgeCount (H := H))) j) := by
    funext j
    rfl
  rw [he]
  split_ifs with hd
  · rw [quotientEdges_eq_orderedEdges face.ordered H.graph _ hd]
    unfold GeometricWeights.canonicalWeight GeometricWeights.geometricWeight
    congr 1
  · rw [GeometricWeights.rawIntegral,
      quotientDensity_eq_zero_of_not_distinct face.ordered H.graph _ hd]
    simp

end EnvelopingIsomorphism.Deformation.MixedPurePhysicalAssembly
