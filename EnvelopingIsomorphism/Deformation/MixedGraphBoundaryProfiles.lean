import EnvelopingIsomorphism.Deformation.MixedGraphSourceProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphAveraging

/-! The mixed graph boundary relation is a literal equality of finite scalar
tables. The source vector action, target unary gauge action and signed
two-exceptional curvature correction remain separate actual graph profiles. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles
open scoped BigOperators Classical
open MixedGraphProfileCarrier MixedGraphSourceProfiles MixedGraphTargetProfiles
open MixedGraphCorrectionProfiles MixedGraphAveraging GraphCoefficientProfiles
open UniformBinaryGraphs

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

/-- The curvature correction starts with two bivectors to be contracted;
degrees zero and one carry no artificial correction term. -/
def fullCorrectionProfile (u : (j : ℕ) → CorrectionGraph j → k) :
    (N : ℕ) → VectorGraph N 2 → k
  | 0 => 0
  | 1 => 0
  | n + 2 => correctionProfile (u n)

/-- Fixed argument convention is (X,Q,bivectors). The correction already
contains the two-odd placement sign and 1/2; this equation fixes its global
boundary orientation as source plus correction equals target. -/
def ScalarMixedBoundaryRelation
    (w : (j : ℕ) → BinaryGraph j 2 → k)
    (v : (j : ℕ) → VectorGraph j 1 → k)
    (u : (j : ℕ) → CorrectionGraph j → k) : Prop :=
  ∀ N, boundaryAverage (fullSourceActionProfile w N + fullCorrectionProfile u N) =
    boundaryAverage (targetActionProfile N v w)

/-- A scalar boundary relation gives equality of the independently varying
mixed multilinear maps; it assumes no operator, tangent or path equation. -/
theorem evaluation_scalarMixedBoundaryRelation
    {w : (j : ℕ) → BinaryGraph j 2 → k}
    {v : (j : ℕ) → VectorGraph j 1 → k}
    {u : (j : ℕ) → CorrectionGraph j → k}
    (h : ScalarMixedBoundaryRelation w v u) (N : ℕ) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (fullSourceActionProfile w N) +
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) (fullCorrectionProfile u N) =
      evaluation (symmetrizedBinaryValue (k := k) (d := d)) (targetActionProfile N v w) := by
  rw [← map_add]
  exact evaluation_eq_of_boundaryAverage_eq (h N)

section Canonical
variable [Algebra ℝ k]

/-- Actual canonical velocity weights with their retained distinguished vertex. -/
def canonicalVelocityWeight (Γ : VectorGraph n 1) : k :=
  algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ.graph
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 Γ.vertex))

theorem canonicalVelocityWeight_factorial (Γ : VectorGraph n 1) :
    canonicalVelocityWeight (k := k) Γ = ((n + 1).factorial : ℚ)⁻¹ •
      algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalWeight Γ.graph
        (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 Γ.vertex)) :=
  Kontsevich.map_effectiveMCWeight (algebraMap ℝ k).toAddMonoidHom (n + 1) _

omit [CharZero k] in
/-- The carrier's canonical velocity is exactly the existing canonical family. -/
theorem weightedVelocity_canonical :
    weightedVelocity (k := k) (d := d) canonicalVelocityWeight =
      Gauge.CanonicalTangentCoefficients.velocityFamily k d n :=
  weightedVelocity_eq_placed (fun _ i Γ ↦ algebraMap ℝ k
    (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ
      (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 i)))

/-- The still-analytic mixed condition consists only of canonical scalar
graph boundary coefficients, including the signed two-odd correction. -/
def CanonicalScalarMixedBoundaryRelation : Prop :=
  ScalarMixedBoundaryRelation (GraphBoundaryProfiles.canonicalBinaryWeight (k := k))
    (fun _ ↦ canonicalVelocityWeight) (fun _ ↦ canonicalQuotientWeight)

end Canonical
end EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles
