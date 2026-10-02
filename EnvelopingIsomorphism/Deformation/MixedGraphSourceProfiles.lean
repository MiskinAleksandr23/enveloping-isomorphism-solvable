import EnvelopingIsomorphism.Deformation.MixedGraphActionSplits
import EnvelopingIsomorphism.Deformation.GraphFixedArityMaps

/-! Genuine mixed scalar source profiles evaluate to differentiation of the
actual weighted binary coefficient in the vector-field action direction. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphSourceProfiles
open scoped BigOperators Classical
open MixedGraphProfileCarrier MixedGraphActionSplits GraphCoefficientProfiles
open UniformBinaryGraphs SymmetrizedGraphInsertion

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

omit [CharZero k] in
theorem evaluation_binaryValue_apply (c : VectorGraph n 2 → k)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) c R X =
      cochainTwoEquiv k _ (evaluation (fun Γ ↦ MixedGraphProfileCarrier.operator Γ R X) c) := by
  simp only [evaluation_apply, sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    binaryValue, LinearMap.compMultilinearMap_apply, LinearMap.llcomp_apply, map_sum, map_smul]
  rfl

/-- Weighted source split profiles yield precisely the sum of actual
independently varying slot derivatives. The vector argument remains linear. -/
theorem evaluation_sourceActionProfile
    (w : BinaryGraph (n + 1) 2 → k)
    (R : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (sourceActionProfile w) R X =
      ∑ i : Fin (n + 1), binaryMap w
        (Function.update R i (schoutenVectorAction 1 X (R i))) := by
  rw [evaluation_binaryValue_apply, sourceActionProfile, map_sum]
  simp only [map_sum, map_smul, evaluation_actionSplitProfile_ordered]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [binaryMap_apply]

/-- All total bivector degrees, including the zero derivative of nullary multiplication. -/
def fullSourceActionProfile (w : (j : ℕ) → BinaryGraph j 2 → k) :
    (N : ℕ) → VectorGraph N 2 → k
  | 0 => 0
  | n + 1 => sourceActionProfile (w (n + 1))

theorem evaluation_fullSourceActionProfile
    (w : (j : ℕ) → BinaryGraph j 2 → k) (N : ℕ)
    (R : Fin N → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (fullSourceActionProfile w N) R X =
      ∑ i : Fin N, binaryMap (w N) (Function.update R i (schoutenVectorAction 1 X (R i))) := by
  cases N with
  | zero => simp [fullSourceActionProfile]
  | succ n => exact evaluation_sourceActionProfile (w (n + 1)) R X

variable [Algebra ℝ k]

/-- The canonical scalar source profile is the actual canonical homogeneous
Taylor derivative, not an assumed source cochain relation. -/
theorem evaluation_canonicalSourceActionProfile (N : ℕ)
    (R : Fin N → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d))
      (fullSourceActionProfile (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)) N) R X =
      ∑ i : Fin N, Gauge.CanonicalTangentCoefficients.mcFamily k d N
        (Function.update R i (schoutenVectorAction 1 X (R i))) := by
  rw [evaluation_fullSourceActionProfile]
  simp only [GraphFixedArityMaps.binaryMap_canonical]

end EnvelopingIsomorphism.Deformation.MixedGraphSourceProfiles
