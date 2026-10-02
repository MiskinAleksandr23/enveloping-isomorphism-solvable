import EnvelopingIsomorphism.Deformation.MainPurePhysicalAssembly
import EnvelopingIsomorphism.Deformation.MainPurePhysicalIntegral
import EnvelopingIsomorphism.Deformation.MainNullaryGraphCoefficients
import EnvelopingIsomorphism.Deformation.MainPairedGeometricMatching

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPureGeometricMatching
open Kontsevich MainScalarBoundaryAssembly MainPurePhysicalFace MainPurePhysicalAssembly
open MainPurePhysicalIntegral MainPureOrbitAssembly PureBoundaryGraphMatching
open MainPairedGeometricMatching (normalization)
open scoped Classical
variable {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3} (P : MainPartition H)

theorem degree (s : Fin 2) :
    ∑ _ : Fin (n+2), (2 : ℕ) = PureBoundaryGraphIntegral.Degree
      (n := n+1) (l := (face s).l) (u := (face s).u) :=
  (GeometricWeights.binaryEdgeCount (n+1)).trans
    (degree_eq (main_dimension n) (face s)).symm

def quotientValue (H : UniformBinaryGraphs.BinaryGraph (n+2) 3) (s : Fin 2) : ℝ :=
  if hd : QuotientDistinct (face s).ordered H then
    GeometricWeights.canonicalWeight (quotientGraph (face s).ordered H hd) (degree s)
  else 0

theorem normalized_clusterValue (s : Fin 2) :
    normalization n * clusterValue (ofMain P) (face s) =
      (-1 : ℝ)^s.val * quotientValue H s := by
  rw [clusterValue_eq_integral]
  change normalization n * ((-1 : ℝ)^s.val * _) = _
  rw [mul_left_comm]
  congr 1
  by_cases hd : QuotientDistinct (face s).ordered H
  · rw [quotientValue,dif_pos hd]
    exact normalized_integral_eq_quotientWeight (main_dimension n) (face s) H
      (GeometricWeights.binaryEdgeCount (n+1)) hd
  · rw [quotientValue,dif_neg hd]
    have hz := integral_eq_zero_of_not_distinct (main_dimension n) (face s) H
      (GeometricWeights.binaryEdgeCount (n+1)) hd
    change (∫ y in region (main_dimension n) (face s),
      OrientedFormChangeVariables.density (form (main_dimension n) (face s) (mainEdges H)) y) = 0 at hz
    rw [hz,mul_zero]

theorem normalization_mul_nativeKind_pureBoundary_quotient :
    normalization n * nativeKindBoundary P .pureBoundary = quotientValue H 0 - quotientValue H 1 := by
  rw [nativeKind_pureBoundary_eq_clusters,mul_add,normalized_clusterValue,normalized_clusterValue]
  simp [sub_eq_add_neg]


theorem quotientValue_eq_coefficient_empty (s : Fin 2) :
    quotientValue H s = GraphBinaryPhysicalSubsetIndex.coefficient H s ∅ := by
  have hs : BoundaryGraphFaceFactorization.shapeM (face s).l (face s).u = 2 :=
    (Fintype.card_coe _).trans (face s).card_eq
  have hslot : MainNullaryGraphCoefficients.slot (face s).ordered hs = s := Fin.ext rfl
  by_cases hd : QuotientDistinct (face s).ordered H
  · rw [quotientValue,dif_pos hd]
    have h := MainNullaryGraphCoefficients.coefficient_empty_eq_canonicalQuotientWeight
      (face s).ordered hs H hd (degree s)
    rw [hslot] at h
    exact h.symm
  · rw [quotientValue,dif_neg hd]
    have h := MainNullaryGraphCoefficients.coefficient_empty_of_not_distinct
      (face s).ordered hs H hd
    rw [hslot] at h
    exact h.symm

/-- Complete matching of the original pure-boundary Stokes contributions
with the actual empty physical-subset associator coefficient. -/
theorem normalization_mul_nativeKind_pureBoundary :
    normalization n * nativeKindBoundary P .pureBoundary =
      GraphBinaryPhysicalSubsetIndex.coefficient H 0 ∅ -
        GraphBinaryPhysicalSubsetIndex.coefficient H 1 ∅ := by
  rw [normalization_mul_nativeKind_pureBoundary_quotient,
    quotientValue_eq_coefficient_empty,quotientValue_eq_coefficient_empty]

end EnvelopingIsomorphism.Deformation.MainPureGeometricMatching
