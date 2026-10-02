import EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphAveraging

/-! The actual symmetrized one-vector carrier evaluates the native target-action
profile to the existing homogeneous weighted unary action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles

open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles UniformBinaryGraphs
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

omit [CharZero k] in
theorem rawBinaryValue_diagonal (Γ : VectorGraph n 2)
    (π : Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawBinaryValue Γ (fun _ => π) X = binaryValue Γ (fun _ => π) X := by
  have h := operator_eq_rawValue Γ (fun _ => π) X
  exact congrArg (cochainTwoEquiv k (MvPolynomial (Fin d) k)) h.symm

/-- Background averaging leaves actual diagonal graph values unchanged. -/
theorem evaluation_symmetrized_diagonal (c : VectorGraph n 2 → k)
    (π : Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) c (fun _ => π) X =
      evaluation (fun Γ => rawBinaryValue Γ (fun _ => π) X) c := by
  simp only [evaluation_apply, sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    symmetrizedBinaryValue_diagonal, rawBinaryValue_diagonal]

/-- Exact homogeneous weighted unary action from the actual scalar target table,
with the established symmetrized one-vector carrier and all total-degree splits. -/
theorem evaluation_targetActionProfile_symmetrized_diagonal (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (targetActionProfile N w v) (fun _ => π) X =
      ∑ a : Fin (N + 1), unaryAction (weightedVelocity (w a) (fun _ => π) X)
        (GraphWeightedInsertion.weightedBinary (v (N - a)) π) := by
  rw [evaluation_symmetrized_diagonal, evaluation_targetActionProfile_diagonal]

end EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
