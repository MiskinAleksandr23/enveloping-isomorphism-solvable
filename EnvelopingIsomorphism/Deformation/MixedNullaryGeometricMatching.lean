import EnvelopingIsomorphism.Deformation.MixedPurePhysicalAssembly
import EnvelopingIsomorphism.Deformation.MixedInfinityGeometricWeight
import EnvelopingIsomorphism.Deformation.MixedNullaryGraphCoefficients
import EnvelopingIsomorphism.Deformation.MixedRealPhysicalSubsetCoefficients

/-! The nullary binary-subset endpoints in the actual mixed Stokes boundary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedNullaryGeometricMatching
open MixedGraphProfileCarrier MixedScalarBoundaryAssembly MixedRealPhysicalSubsetCoefficients
open MixedNullaryGraphCoefficients
open Kontsevich MixedInfinityGeometricWeight
open scoped Classical
variable {N : ℕ} {H : VectorGraph N 2} (P : MixedPartition H)

theorem pure_matching :
    MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .pureBoundary =
      outputCoefficient H ∅ := by
  rw [outputCoefficient_eq_of_count (Nat.add_zero N) H (emptyCluster N) ∅
    (by simp [emptyCluster]),MixedPurePhysicalAssembly.normalization_mul_nativeKind_pureBoundary]
  change _ = MixedRealPhysicalClusterCoefficients.rawOutputClusterCoefficient (a := N) (b := 0) H (emptyCluster N)
  rw [output_empty_eq_quotient]
  rfl

theorem innerClosed_iff_inputClosed (H : VectorGraph N 2) (r : Fin 2) :
    InnerClosed H (MixedInfinityPhysicalAssembly.face r) ↔ InputClosed H r := by
  unfold InnerClosed InputClosed
  apply forall_congr'
  intro e
  cases ht : H.graph.target e with
  | inl v =>
    simp only [boundaryAnchoredInfinityCollapses,true_iff]
    exact ⟨Sum.inl v,rfl⟩
  | inr j =>
    have hm : j ∈ boundaryClusterBlock (MixedInfinityPhysicalAssembly.face r).l
        (MixedInfinityPhysicalAssembly.face r).u ↔ j = r := by
      fin_cases r <;> fin_cases j <;> decide
    change (j ∈ boundaryClusterBlock _ _) ↔ _
    rw [hm]
    constructor
    · intro h
      exact ⟨Sum.inr 0,by rw [h]; rfl⟩
    · rintro ⟨w,hw⟩
      cases w with
      | inl w => cases hw
      | inr w => exact (Sum.inr.inj hw).symm

theorem shapeWeight_eq_inputCoefficient (H : VectorGraph N 2) (r : Fin 2) :
    shapeWeight H (MixedInfinityPhysicalAssembly.face r) = inputCoefficient r H ∅ := by
  rw [inputCoefficient_eq_of_count r (Nat.add_zero N) H (emptyCluster N) ∅ (by simp [emptyCluster])]
  change _ = MixedRealPhysicalClusterCoefficients.rawInputClusterCoefficient (a := N) (b := 0) r H (emptyCluster N)
  rw [input_empty_eq_graph,shapeWeight_eq_canonical]
  by_cases hc : InputClosed H r
  · rw [dif_pos hc,dif_pos ((innerClosed_iff_inputClosed H r).mpr hc)]
    exact canonicalShapeWeight_eq_originalLabels H _ _ (inputGraph H r hc) (inputGraph_target H r hc)
  · rw [dif_neg hc,dif_neg (mt (innerClosed_iff_inputClosed H r).mp hc)]

theorem infinity_matching :
    MixedPairedEdgeRelabelling.normalization H * nativeKindBoundary P .infinity =
      -inputCoefficient 0 H ∅ - inputCoefficient 1 H ∅ := by
  rw [normalization_mul_nativeKind_infinity,shapeWeight_eq_inputCoefficient,shapeWeight_eq_inputCoefficient]

/-- All three nullary mixed faces belong to the same empty binary subset. -/
theorem nullary_matching :
    MixedPairedEdgeRelabelling.normalization H *
      (nativeKindBoundary P .pureBoundary + nativeKindBoundary P .infinity) =
      MixedGraphPhysicalSubsetIndex.coefficient H ∅ := by
  rw [mul_add,pure_matching,infinity_matching,coefficient_eq_output_sub_inputs]
  ring

end EnvelopingIsomorphism.Deformation.MixedNullaryGeometricMatching
