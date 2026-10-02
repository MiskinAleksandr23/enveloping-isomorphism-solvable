import EnvelopingIsomorphism.Deformation.MixedPairedFullFaceIntegral
import EnvelopingIsomorphism.Deformation.MixedPairedCoefficientMatching
import EnvelopingIsomorphism.Deformation.SignedMixedPhysicalBoundaryNormalization

/-! Unconditional assembly of the genuine mixed paired boundary, with the
geometric negative correction density and every low-degree endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedGeometricMatching
open Kontsevich MixedGraphProfileCarrier MixedScalarBoundaryAssembly
open MixedPairedCoreCover MixedPairedFullFaceIntegral MixedPairedEdgeRelabelling
open MixedPairedCoefficientMatching MixedPhysicalBoundaryNormalization
open GraphCurvatureLabelCounting MixedGraphOutgoingPairNormalization
open scoped Classical

private theorem normalized_eq_integral {N : ℕ} (H : VectorGraph N 2)
    (T : Finset (Fin (N+1))) (hT : 1 < T.card) :
    normalized (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) H =
      normalization H * (∫ y in Face (m := 2) T, density (H := H) T hT y) := rfl

section LargeDegree
variable {n : ℕ} {H : VectorGraph (n+2) 2} (P : MixedPartition H)

theorem pair_cluster_matching (T : PhysicalPair (n+1)) :
    normalization H * clusterValue P T.val = -sourcePhysicalCoefficient H T +
      (3 / 2 : ℝ) * correctionPhysicalCoefficient H T := by
  have hT : 1 < T.val.card := by rw [T.property]; omega
  rw [clusterValue_eq_neg_integral P T.val hT, mul_neg, ← normalized_eq_integral]
  rw [normalized_eq_physicalCoefficient H T]
  ring

theorem paired_matching_succ_succ :
    normalization H * nativeKindBoundary P .paired = -sourceSum (n+2) H + correctionSum (n+2) H := by
  rw [paired_eq_sum_pairs P, Finset.mul_sum]
  change (∑ T : PhysicalPair (n+1), normalization H * clusterValue P T.val) = _
  simp_rw [pair_cluster_matching P]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    sourceSum, correctionSum]
end LargeDegree

section DegreeOne
variable {H : VectorGraph 1 2} (P : MixedPartition H)

private theorem vector_mem_pair (T : PhysicalPair 0) : H.vertex ∈ T.val := by
  have he : T.val = Finset.univ := Finset.eq_univ_of_card T.val (by simpa using T.property)
  rw [he]
  exact Finset.mem_univ _

theorem pair_cluster_matching_one (T : PhysicalPair 0) :
    normalization H * clusterValue P T.val = -sourcePhysicalCoefficient H T := by
  have hT : 1 < T.val.card := by rw [T.property]; omega
  rw [clusterValue_eq_neg_integral P T.val hT, mul_neg, ← normalized_eq_integral,
    normalized_source H T _ _ _ _ (vector_mem_pair T)]

theorem paired_matching_one :
    normalization H * nativeKindBoundary P .paired = -sourceSum 1 H + correctionSum 1 H := by
  rw [paired_eq_sum_pairs P, Finset.mul_sum]
  change (∑ T : PhysicalPair 0, normalization H * clusterValue P T.val) = _
  simp_rw [pair_cluster_matching_one P]
  simp only [Finset.sum_neg_distrib, sourceSum, correctionSum, add_zero]
end DegreeOne

section DegreeZero
variable {H : VectorGraph 0 2} (P : MixedPartition H)

theorem paired_matching_zero :
    normalization H * nativeKindBoundary P .paired = -sourceSum 0 H + correctionSum 0 H := by
  rw [paired_eq_sum_pairs P]
  have hempty : IsEmpty {T : Finset (Fin (0+1)) // T.card = 2} := ⟨fun T ↦ by
    have hc := Finset.card_le_univ T.val
    simp only [Fintype.card_fin, T.property] at hc
    omega⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sourceSum, correctionSum,
    neg_zero, add_zero]
end DegreeZero

/-- The entire paired part of the original finite mixed Stokes partition is
the negative source plus correction sum. No coefficient or matching premise
remains, including degrees zero and one and every marked vector placement. -/
theorem paired_matching {N : ℕ} {H : VectorGraph N 2} (P : MixedPartition H) :
    normalization H * nativeKindBoundary P .paired = -sourceSum N H + correctionSum N H := by
  rcases N with _ | (_ | n)
  · exact paired_matching_zero P
  · exact paired_matching_one P
  · exact paired_matching_succ_succ P

end EnvelopingIsomorphism.Deformation.MixedPairedGeometricMatching
