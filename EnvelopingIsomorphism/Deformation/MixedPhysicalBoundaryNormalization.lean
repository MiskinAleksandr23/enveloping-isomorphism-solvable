import EnvelopingIsomorphism.Deformation.MixedScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingClusterSums

/-! The exact mixed physical boundary equation after removing the global
outgoing average. Its source and correction retain their genuine physical
pair coefficients, with factors one and three halves respectively. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPhysicalBoundaryNormalization
open scoped Classical BigOperators
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphPhysicalPairSums
open MixedGraphOutgoingPairNormalization MixedGraphClusterSums MixedGraphOutgoingClusterSums
open GraphLabelledClusterCounting MixedGraphLabelledClusterCounting MixedGraphTargetProfiles
open GraphCurvatureLabelCounting
variable {N : ℕ}

/-- The physical vector-bivector two-point faces, including the empty degree. -/
def sourceSum : (N : ℕ) → VectorGraph N 2 → ℝ
  | 0, _ => 0
  | n+1, H => ∑ T : PhysicalPair n, sourcePhysicalCoefficient H T

/-- Binary two-point faces with the exterior vector retained. The factor
three halves is the proved outgoing normalization of the split, not a sign
convention; each coefficient still carries its actual two-odd sign. -/
def correctionSum : (N : ℕ) → VectorGraph N 2 → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n+2, H => (3 / 2 : ℝ) * ∑ T : PhysicalPair (n+1), correctionPhysicalCoefficient H T

/-- Every real cluster, including both zero-degree factor endpoints, occurs
once with its genuine output-minus-inputs coefficient. -/
def targetSum (H : VectorGraph N 2) : ℝ :=
  ∑ a : Fin (N+1), ∑ T : Clusters (binaryBlock a (N-a)),
    rawActionClusterCoefficient (castVertices (splitDegree N a).symm H) T

def defect (H : VectorGraph N 2) : ℝ := sourceSum N H + correctionSum N H - targetSum H

theorem sourceSum_eq_normalized (H : VectorGraph N 2) :
    sourceSum N H = ((2 : ℝ)^N)⁻¹ * sourcePhysicalSum N H := by
  cases N with
  | zero => simp [sourceSum, sourcePhysicalSum]
  | succ n =>
    simp only [sourceSum, sourcePhysicalSum, sourcePhysicalCoefficient, Finset.mul_sum]
    rw [Finset.sum_comm]

theorem correctionSum_eq_normalized (H : VectorGraph N 2) :
    correctionSum N H = ((2 : ℝ)^N)⁻¹ * correctionPhysicalSum N H := by
  cases N with
  | zero => simp [correctionSum, correctionPhysicalSum]
  | succ n =>
    cases n with
    | zero => simp [correctionSum, correctionPhysicalSum]
    | succ n =>
      simp only [correctionSum, correctionPhysicalSum, correctionPhysicalCoefficient,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro T _
      ring

theorem targetPhysicalSum_eq_pow_mul (H : VectorGraph N 2) :
    targetPhysicalSum N H = (2 : ℝ)^N * targetSum H := by
  unfold targetPhysicalSum
  simp_rw [rawActionClusterCoefficient_cast_outgoing_symm]
  simp only [← Finset.mul_sum, ← mul_assoc, outgoingSign_sq, one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Nat.factorial_two,
    Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem targetSum_eq_normalized (H : VectorGraph N 2) :
    targetSum H = ((2 : ℝ)^N)⁻¹ * targetPhysicalSum N H := by
  rw [targetPhysicalSum_eq_pow_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

/-- The previous independently defined physical defect and this normalized
equation differ only by the nonzero global outgoing factor. -/
theorem defect_eq_normalized (H : VectorGraph N 2) :
    defect H = ((2 : ℝ)^N)⁻¹ * MixedScalarBoundaryAssembly.defect H := by
  rw [defect, sourceSum_eq_normalized, correctionSum_eq_normalized, targetSum_eq_normalized]
  simp only [MixedScalarBoundaryAssembly.defect, mul_add, mul_sub]

theorem defect_eq_zero_iff (H : VectorGraph N 2) :
    defect H = 0 ↔ MixedScalarBoundaryAssembly.defect H = 0 := by
  rw [defect_eq_normalized, mul_eq_zero]
  simp only [inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, false_or]

/-- Exact finite geometric obligation, with no graph covariance premise.
All degrees and vector placements are quantified, including zero and one. -/
theorem canonicalScalarMixedBoundaryRelation_iff_defect_zero :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      ∀ N (H : VectorGraph N 2), defect H = 0 := by
  rw [MixedScalarBoundaryAssembly.canonicalScalarMixedBoundaryRelation_iff_defect_zero]
  exact forall_congr' fun N ↦ forall_congr' fun H ↦ (defect_eq_zero_iff H).symm

theorem canonicalScalarMixedBoundaryRelation_of_defect_zero
    (h : ∀ N (H : VectorGraph N 2), defect H = 0) :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ) :=
  canonicalScalarMixedBoundaryRelation_iff_defect_zero.mpr h

end EnvelopingIsomorphism.Deformation.MixedPhysicalBoundaryNormalization
