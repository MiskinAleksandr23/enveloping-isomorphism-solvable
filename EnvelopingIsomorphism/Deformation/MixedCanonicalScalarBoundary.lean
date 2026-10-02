import EnvelopingIsomorphism.Deformation.MixedRealGeometricMatching
import EnvelopingIsomorphism.Deformation.MixedNullaryGeometricMatching
import EnvelopingIsomorphism.Deformation.MixedPairedGeometricMatching

/-! The unconditional signed mixed scalar boundary relation, obtained from
all actual native forest boundary kinds and their computed graph weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedCanonicalScalarBoundary
open Kontsevich MixedGraphProfileCarrier MixedScalarBoundaryAssembly
open ForestRadialFaceClassification MixedPairedEdgeRelabelling MixedPhysicalBoundaryNormalization
open SignedMixedPhysicalBoundaryNormalization
open scoped Classical BigOperators
variable {N : ℕ} {H : VectorGraph N 2} (P : MixedPartition H)

/-- Pure output, infinity inputs and proper real faces give the full target. -/
theorem targetSum_eq_native :
    targetSum H = normalization H *
      (nativeKindBoundary P .properReal + nativeKindBoundary P .pureBoundary +
        nativeKindBoundary P .infinity) := by
  rw [MixedRealGeometricMatching.targetSum_eq_empty_add_properReal P,
    ← MixedNullaryGeometricMatching.nullary_matching P]
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
/-- The computed negative correction sign is retained in the scalar defect. -/
theorem signedDefect_eq_zero : signedDefect H = 0 := by
  have hp := MixedPairedGeometricMatching.paired_matching P
  have hz := congrArg (fun x : ℝ ↦ normalization H * x) (native_kinds_eq_zero P)
  rw [mul_zero,mul_add,← targetSum_eq_native P,hp] at hz
  unfold signedDefect
  linarith

/-- The signed mixed relation, in every degree and vector placement, without
any geometric matching or boundary-integral assumptions. -/
theorem signedCanonicalScalarMixedBoundaryRelation :
    SignedCanonicalScalarMixedBoundaryRelation (k := ℝ) := by
  apply signedCanonicalScalarMixedBoundaryRelation_iff_defect_zero.mpr
  intro N H
  exact signedDefect_eq_zero (mixedPartition H)

end EnvelopingIsomorphism.Deformation.MixedCanonicalScalarBoundary
