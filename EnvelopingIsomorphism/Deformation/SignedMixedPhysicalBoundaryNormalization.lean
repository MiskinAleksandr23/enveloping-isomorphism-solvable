import EnvelopingIsomorphism.Deformation.MixedPhysicalBoundaryNormalization

/-! The signed mixed boundary convention delivered by the actual geometric
correction faces. The negative curvature kernel is explicit; the earlier
source-plus-correction relation is a separate proposition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.SignedMixedPhysicalBoundaryNormalization
open scoped Classical BigOperators
open MixedGraphProfileCarrier MixedGraphBoundaryProfiles MixedGraphCorrectionProfiles
open MixedGraphAveraging MixedGraphPhysicalPairSums MixedPhysicalBoundaryNormalization
open MixedGraphSourceProfiles MixedGraphTargetProfiles MixedGraphClusterSums

section Algebra
variable {k : Type*} [Field k] [CharZero k] {N : ℕ}

omit [CharZero k] in
theorem correctionProfile_neg {n : ℕ} (c : CorrectionGraph n → k) :
    correctionProfile (fun Γ ↦ -c Γ) = -correctionProfile c := by
  funext H
  simp [correctionProfile, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    Finset.sum_neg_distrib]

theorem fullCorrectionProfile_neg (c : (j : ℕ) → CorrectionGraph j → k) (N : ℕ) :
    fullCorrectionProfile (fun j Γ ↦ -c j Γ) N = -fullCorrectionProfile c N := by
  rcases N with _ | (_ | n)
  · simp [fullCorrectionProfile]
  · simp [fullCorrectionProfile]
  · exact correctionProfile_neg (c n)

omit [CharZero k] in
theorem boundaryAverage_neg (c : VectorGraph N 2 → k) :
    boundaryAverage (-c) = -boundaryAverage c := by
  funext H
  simp [boundaryAverage_apply, Finset.sum_neg_distrib]

omit [CharZero k] in
theorem boundaryAverage_add (c d : VectorGraph N 2 → k) :
    boundaryAverage (c+d) = boundaryAverage c + boundaryAverage d := by
  funext H
  simp [boundaryAverage_apply, Finset.sum_add_distrib, mul_add]

variable [Algebra ℝ k]

/-- Same actual canonical star and velocity weights, with the geometrically
computed negative correction kernel. No mixed identity is asserted here. -/
def SignedCanonicalScalarMixedBoundaryRelation : Prop :=
  ScalarMixedBoundaryRelation (GraphBoundaryProfiles.canonicalBinaryWeight (k := k))
    (fun _ ↦ canonicalVelocityWeight (k := k)) (fun _ Γ ↦ -canonicalQuotientWeight (k := k) Γ)

end Algebra

variable {N : ℕ}

/-- Literal source-minus-correction-minus-target equation, keeping the
proved source factor one and correction factor three halves. -/
def signedDefect (H : VectorGraph N 2) : ℝ :=
  sourceSum N H - correctionSum N H - targetSum H

/-- The same signed equation before cancelling the outgoing average. -/
def signedPhysicalDefect (H : VectorGraph N 2) : ℝ :=
  sourcePhysicalSum N H - correctionPhysicalSum N H - targetPhysicalSum N H

theorem signedDefect_eq_normalized (H : VectorGraph N 2) :
    signedDefect H = ((2 : ℝ)^N)⁻¹ * signedPhysicalDefect H := by
  rw [signedDefect, sourceSum_eq_normalized, correctionSum_eq_normalized, targetSum_eq_normalized]
  simp only [signedPhysicalDefect, mul_sub]

theorem signedDefect_eq_zero_iff (H : VectorGraph N 2) :
    signedDefect H = 0 ↔ signedPhysicalDefect H = 0 := by
  rw [signedDefect_eq_normalized, mul_eq_zero]
  simp only [inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, false_or]

theorem boundaryAverage_signed_source_eq_normalized (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (fullSourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ)) N +
      fullCorrectionProfile (fun _ Γ ↦ -canonicalQuotientWeight (k := ℝ) Γ) N) H =
      ((N+1).factorial : ℝ)⁻¹ * (sourceSum N H - correctionSum N H) := by
  rw [fullCorrectionProfile_neg, boundaryAverage_add, boundaryAverage_neg]
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [boundaryAverage_full_source_eq_pairs, boundaryAverage_full_correction_eq_pairs,
    sourceSum_eq_normalized, correctionSum_eq_normalized]
  ring

theorem boundaryAverage_target_eq_normalized (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (targetActionProfile N
      (fun _ ↦ canonicalVelocityWeight (k := ℝ))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      ((N+1).factorial : ℝ)⁻¹ * targetSum H := by
  rw [boundaryAverage_canonical_targetAction_eq_clusters, targetSum_eq_normalized]
  unfold targetPhysicalSum
  ring

/-- Exact equivalence of the finite signed scalar table and the normalized
physical source-minus-correction equation in every degree and placement. -/
theorem signedCanonicalScalarMixedBoundaryRelation_iff_endpoints :
    SignedCanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      ∀ N (H : VectorGraph N 2), sourceSum N H - correctionSum N H = targetSum H := by
  unfold SignedCanonicalScalarMixedBoundaryRelation ScalarMixedBoundaryRelation
  constructor
  · intro h N H
    have he := congrFun (h N) H
    rw [boundaryAverage_signed_source_eq_normalized, boundaryAverage_target_eq_normalized] at he
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (N+1))) he
  · intro h N
    funext H
    rw [boundaryAverage_signed_source_eq_normalized, boundaryAverage_target_eq_normalized, h N H]

theorem signedCanonicalScalarMixedBoundaryRelation_iff_defect_zero :
    SignedCanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      ∀ N (H : VectorGraph N 2), signedDefect H = 0 := by
  rw [signedCanonicalScalarMixedBoundaryRelation_iff_endpoints]
  simp only [signedDefect, sub_eq_zero]

theorem signedCanonicalScalarMixedBoundaryRelation_iff_physical_defect_zero :
    SignedCanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      ∀ N (H : VectorGraph N 2), signedPhysicalDefect H = 0 := by
  rw [signedCanonicalScalarMixedBoundaryRelation_iff_defect_zero]
  exact forall_congr' fun N ↦ forall_congr' fun H ↦ signedDefect_eq_zero_iff H

theorem signedCanonicalScalarMixedBoundaryRelation_of_defect_zero
    (h : ∀ N (H : VectorGraph N 2), signedDefect H = 0) :
    SignedCanonicalScalarMixedBoundaryRelation (k := ℝ) :=
  signedCanonicalScalarMixedBoundaryRelation_iff_defect_zero.mpr h

end EnvelopingIsomorphism.Deformation.SignedMixedPhysicalBoundaryNormalization
