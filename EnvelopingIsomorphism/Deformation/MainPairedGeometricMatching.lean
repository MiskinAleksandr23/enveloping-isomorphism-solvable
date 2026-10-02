import EnvelopingIsomorphism.Deformation.MainPairedFullFaceIntegral
import EnvelopingIsomorphism.Deformation.MainPairedPhysicalPairWeight

/-! Unconditional matching of the entire paired part of the original main
Stokes partition to the actual physical-pair curvature coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedGeometricMatching
open Kontsevich UniformBinaryGraphs MainScalarBoundaryAssembly MainClassifiedFaceAssembly
open MainPairedClusterAssembly MainPairedFixedChartCover MainPairedFixedChartIntegral
open MainPairedFullFaceIntegral MainPairedPhysicalPairWeight
open GraphCurvatureLabelCounting GraphCurvaturePhysicalPairs ForestRadialFaceClassification
open scoped Classical
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)

/-- One genuine outgoing-factorial and angle normalization for every original
radial face; its exponent is the main graph's actual edge count. -/
def normalization (n : ℕ) : ℝ :=
  GeometricWeights.outgoingFactor (fun _ : Fin (n+2) => 2) *
    ((2 * Real.pi) ^ (GraphForms.dimension (n+1) 2))⁻¹

theorem normalization_eq_native {a b : Fin (n+2)} {S : Finset (Fin (n+2))}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : (0 : Fin (n+2)) ∈ S → a = 0) :
    normalization n = GeometricWeights.outgoingFactor (fun _ : Fin (n+2) => 2) *
      ((2 * Real.pi) ^ (InteriorGraphFaceCoordinates.shapeDegree a b S +
        InteriorGraphFaceCoordinates.coarseDegree (0 : Fin (n+2)) a S 3))⁻¹ := by
  rw [PairedForestCommonRealDensity.degree_eq (main_dimension n) ha hb hba hi]
  rfl

theorem pair_cluster_matching (T : PhysicalPair n) :
    normalization n * clusterValue P T.val = -(3 / 2 : ℝ) * physicalCoefficient H T := by
  have hT : 1 < T.val.card := by rw [T.property]; omega
  rw [clusterValue_eq_neg_integral P T.val hT, mul_neg]
  have hw := normalized_common_integral_eq_physicalCoefficient H
    (anchorMem T.val hT) (referenceMem T.val hT) (referenceNe T.val hT)
    (anchorGlobal T.val) T.property
  rw [← mul_assoc] at hw
  change normalization n * (∫ y in Face T.val, density (H := H) T.val hT y) =
    (3 / 2 : ℝ) * physicalCoefficient H T at hw
  rw [hw, neg_mul]

theorem cluster_matching (S : Finset (Fin (n+2))) :
    normalization n * clusterValue P S = clusterTarget (H := H) S := by
  apply cluster_matching_of_pairs_and_large P (normalization n) (pair_cluster_matching P)
  intro T hT
  rw [clusterValue_eq_zero_of_large P T hT, mul_zero]

/-- No face coefficient, coverage, orientation or local-to-global matching
hypothesis remains in the paired half of the main Stokes identity. -/
theorem paired_matching
    (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o) :
    interiorPairSum H = -(normalization n * transportedKind P D .paired) :=
  paired_matching_of_cluster_matching P D (normalization n) (cluster_matching P)

theorem paired_native_matching :
    interiorPairSum H = -(normalization n * nativeKindBoundary P .paired) := by
  rw [← transportedKind_eq_nativeKind P (defaultCoordinates P)]
  exact paired_matching P (defaultCoordinates P)

end EnvelopingIsomorphism.Deformation.MainPairedGeometricMatching
