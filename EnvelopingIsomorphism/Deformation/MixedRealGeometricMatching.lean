import EnvelopingIsomorphism.Deformation.MixedRealPhysicalCoefficientMatching

/-! Complete original-partition proper-real matching for every one-vector
graph. The three physical faces of a nonempty binary subset give its actual
output-minus-two-input target coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealGeometricMatching
open MixedGraphProfileCarrier MixedScalarBoundaryAssembly MixedRealPhysicalFaces MixedRealPhysicalIndex
open MixedGraphPhysicalSubsetIndex MixedRealPhysicalSubsetCoefficients MixedRealPhysicalCoefficientMatching
open scoped Classical BigOperators
variable {N : ℕ} (H : VectorGraph N 2)

theorem normalization_mul_three_faces (T : BinarySubset H.vertex) :
    MixedPairedEdgeRelabelling.normalization H *
      (physicalValue H (outputKey T) + physicalValue H (inputKey T 0) + physicalValue H (inputKey T 1)) =
      coefficient H T.val := by
  rw [mul_add,mul_add,normalized_outputKey,normalized_inputKey,normalized_inputKey,
    coefficient_eq_output_sub_inputs]
  ring

variable {H} (P : MixedPartition H)

/-- All surviving original proper-real orbits have been reassembled and
matched to their genuine graph coefficients. No geometric matching premise
or finite fibre hypothesis remains. -/
theorem normalization_mul_nativeKind_properReal :
    MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .properReal =
      ∑ T : BinarySubset H.vertex, coefficient H T.val := by
  rw [nativeKind_properReal_eq_binarySubsets,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T _ ↦ normalization_mul_three_faces H T)

/-- The only target term outside the completely matched proper-real sum is
the empty binary subset, containing the pure output and both infinity inputs. -/
theorem targetSum_eq_empty_add_properReal :
    MixedPhysicalBoundaryNormalization.targetSum H = coefficient H ∅ +
      MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .properReal := by
  rw [targetSum_eq_empty_add_binarySubsets,normalization_mul_nativeKind_properReal]

end EnvelopingIsomorphism.Deformation.MixedRealGeometricMatching
