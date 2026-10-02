import EnvelopingIsomorphism.Deformation.GraphAssociatorProfiles
import EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
import EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentCoefficients

/-! Scalar boundary relations and their exact diagonal operator consequence.
The relation is solely between finite scalar tables. This module does not infer
an identity on independently varying Laurent inputs from diagonal polynomial
evaluation; the multilinear/polarization and completion transfer remains separate.
-/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles

open scoped BigOperators Classical
open UniformBinaryGraphs GraphWeightedInsertion GraphCoefficientProfiles
open GraphAssociatorProfiles GraphCurvatureProfiles BinaryGraphAveraging
open EnvelopingIsomorphism.FormalSeries

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

/-- The remaining boundary condition has only finite graph labels and scalars.
Both sides retain the true internal and outgoing relabellings, multiplicities,
weight products, quotient positions and the curvature factor 1/2. -/
def ScalarBoundaryRelation
    (w : (n : ℕ) → BinaryGraph n 2 → k)
    (v : (n : ℕ) → (i : Fin (n + 1)) → CurvatureGraph i → k) : Prop :=
  ∀ n, boundaryAverage (associatorProfile (n + 2) w) =
    boundaryAverage (curvatureProfile (v n))

/-- A scalar boundary relation evaluates to the literal coefficient of the
actual weighted binary associator and the literal all-position source curvature. -/
theorem associator_coefficient_eq_curvature
    {w : (n : ℕ) → BinaryGraph n 2 → k}
    {v : (n : ℕ) → (i : Fin (n + 1)) → CurvatureGraph i → k}
    (h : ScalarBoundaryRelation w v) (n : ℕ) (π : Bivector (k := k) (d := d)) :
    PowerSeriesModule.coeffV (n + 2) (PowerSeriesModule.applyBilinear
      PowerSeriesModule.insertBinaryLinear (binarySeries w π) (binarySeries w π)) =
    weightedCurvature (v n) π ((1/2 : k) •
      (show Multiderivation k (MvPolynomial (Fin d) k) 3 from schoutenBracket k d 1 1 π π)) := by
  rw [← evaluation_associatorProfile, ← evaluation_curvatureProfile]
  exact evaluation_eq_of_boundaryAverage_eq π (h n)

/-- All coefficients of the actual diagonal associator vanish at a Poisson
bivector. Degrees zero and one are proved algebraically, without boundary premises. -/
theorem insertion_zero_of_scalarBoundaryRelation
    {w : (n : ℕ) → BinaryGraph n 2 → k}
    {v : (n : ℕ) → (i : Fin (n + 1)) → CurvatureGraph i → k}
    (h : ScalarBoundaryRelation w v) (π : Bivector (k := k) (d := d))
    (hπ : (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
      schoutenBracket k d 1 1 π π) = 0) :
    PowerSeriesModule.applyBilinear PowerSeriesModule.insertBinaryLinear
      (binarySeries w π) (binarySeries w π) = 0 := by
  apply PowerSeriesModule.ext
  intro n
  rw [PowerSeriesModule.coeffV_zero, ← evaluation_associatorProfile]
  rcases n with _ | (_ | n)
  · exact evaluation_associatorProfile_zero_eq_zero w π
  · exact evaluation_associatorProfile_one_eq_zero w π
  · rw [evaluation_eq_of_boundaryAverage_eq π (h n)]
    exact evaluation_curvatureProfile_eq_zero (v n) π hπ

/-- Associativity on polynomial-valued power series follows from the pure
scalar boundary equations. This is a diagonal polynomial theorem, not MCIdentity. -/
theorem associative_of_scalarBoundaryRelation
    {w : (n : ℕ) → BinaryGraph n 2 → k}
    {v : (n : ℕ) → (i : Fin (n + 1)) → CurvatureGraph i → k}
    (h : ScalarBoundaryRelation w v) (π : Bivector (k := k) (d := d))
    (hπ : (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
      schoutenBracket k d 1 1 π π) = 0) :
    ∀ p q r, PowerSeriesModule.extendBinary (binarySeries w π)
      (PowerSeriesModule.extendBinary (binarySeries w π) p q) r =
      PowerSeriesModule.extendBinary (binarySeries w π) p
        (PowerSeriesModule.extendBinary (binarySeries w π) q r) :=
  (PowerSeriesModule.associative_iff_insertion_zero _).mpr
    (insertion_zero_of_scalarBoundaryRelation h π hπ)

section Canonical
variable [Algebra ℝ k]

/-- Actual canonical binary weights, including the true nullary multiplication. -/
def canonicalBinaryWeight : (n : ℕ) → BinaryGraph n 2 → k
  | 0, _ => 1
  | n + 1, Γ => Kontsevich.GeometricWeights.binaryWeightOver k n (toLegacy Γ)

omit [CharZero k] in
theorem weightedBinary_canonical (n : ℕ) (π : Bivector (k := k) (d := d)) :
    weightedBinary (canonicalBinaryWeight n) π =
      Gauge.CanonicalTangentCoefficients.mcFamily k d n (fun _ ↦ π) := by
  cases n with
  | zero =>
    rw [weightedBinary_zero]
    exact one_smul k _
  | succ n =>
    change weightedBinary _ π = Gauge.GraphTaylorCoefficients.weightedCoefficient
      Finset.univ (Kontsevich.GeometricWeights.binaryWeightOver k n) (fun _ ↦ π)
    rw [Gauge.GraphTaylorCoefficients.weightedCoefficient_apply]
    unfold weightedBinary
    apply Fintype.sum_equiv (legacyEquiv (n + 1))
    intro Γ
    exact congrArg (fun B ↦ canonicalBinaryWeight (n + 1) Γ • B)
      (operator_legacy Γ (fun _ ↦ π))

omit [CharZero k] in
/-- The series in the coefficient computation is exactly the existing canonical base series. -/
theorem binarySeries_canonical (π : Bivector (k := k) (d := d)) :
    binarySeries canonicalBinaryWeight π = Gauge.CanonicalTangentCoefficients.starSeries k d π := by
  apply PowerSeriesModule.ext
  intro n
  exact weightedBinary_canonical n π

/-- Only normalized geometric scalar weights occur in this proposition. -/
def CanonicalScalarBoundaryRelation : Prop :=
  ScalarBoundaryRelation (canonicalBinaryWeight (k := k))
    (fun _ ↦ GraphCurvatureProfiles.canonicalWeight)

theorem canonical_insertion_zero (h : CanonicalScalarBoundaryRelation (k := k))
    (π : Bivector (k := k) (d := d))
    (hπ : (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
      schoutenBracket k d 1 1 π π) = 0) :
    PowerSeriesModule.applyBilinear PowerSeriesModule.insertBinaryLinear
      (Gauge.CanonicalTangentCoefficients.starSeries k d π)
      (Gauge.CanonicalTangentCoefficients.starSeries k d π) = 0 := by
  rw [← binarySeries_canonical]
  exact insertion_zero_of_scalarBoundaryRelation h π hπ

end Canonical
end EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles
