import EnvelopingIsomorphism.Deformation.MainRealGeometricMatching
import EnvelopingIsomorphism.Deformation.MainPureGeometricMatching
import EnvelopingIsomorphism.Deformation.MainInfinityGeometricMatching

/-! The unconditional main scalar boundary relation. Every classified part
of the actual finite forest Stokes partition is matched to its genuine graph
coefficient, including the empty and full physical subsets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainCanonicalScalarBoundary
open Kontsevich UniformBinaryGraphs MainScalarBoundaryAssembly
open ForestRadialFaceClassification MainPairedGeometricMatching
open scoped Classical BigOperators
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)

/-- The three real boundary kinds exhaust the associator's physical subsets. -/
theorem realClusterSum_eq_native :
    realClusterSum H = normalization n *
      (nativeKindBoundary P .properReal + nativeKindBoundary P .pureBoundary +
        nativeKindBoundary P .infinity) := by
  rw [MainRealGeometricMatching.realClusterSum_eq_endpoints_add_properReal P,
    ← MainPureGeometricMatching.normalization_mul_nativeKind_pureBoundary P,
    ← MainInfinityGeometricMatching.infinity_native_matching P]
  ring

/-- Cancellation for precisely the four native geometric face kinds. -/
theorem native_kinds_eq_zero :
    nativeKindBoundary P .properReal + nativeKindBoundary P .pureBoundary +
      nativeKindBoundary P .infinity + nativeKindBoundary P .paired = 0 := by
  have h := nativeBoundary_eq_zero P
  rw [nativeBoundary_eq_sum_kind] at h
  have hu : (Finset.univ : Finset Kind) = {.paired,.pureBoundary,.properReal,.infinity} := by decide
  rw [hu] at h
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,reduceCtorEq,
    or_self,not_false_eq_true,Finset.sum_singleton] at h
  linarith

include P in
/-- Actual Stokes cancellation kills the unnormalized main graph defect. -/
theorem defect_eq_zero : defect H = 0 := by
  unfold defect
  rw [realClusterSum_eq_native P,paired_native_matching P,sub_neg_eq_add,
    ← mul_add,native_kinds_eq_zero,mul_zero]

/-- The main canonical scalar boundary relation has no matching assumptions. -/
theorem canonicalScalarBoundaryRelation :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ) := by
  apply canonicalScalarBoundaryRelation_iff_defect_zero.mpr
  intro n H
  exact defect_eq_zero (mainPartition H)

end EnvelopingIsomorphism.Deformation.MainCanonicalScalarBoundary
