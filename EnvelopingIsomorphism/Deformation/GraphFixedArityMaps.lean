import EnvelopingIsomorphism.Deformation.GraphMultilinearCurvature
import EnvelopingIsomorphism.Deformation.SymmetrizedGraphInsertion

/-! Canonical independent-input binary maps and the exact low-arity profile identities. -/
noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphFixedArityMaps
open scoped BigOperators Classical
open UniformBinaryGraphs GraphWeightedInsertion GraphCoefficientProfiles GraphAssociatorProfiles
open SymmetrizedGraphProfiles SymmetrizedGraphInsertion
variable {k : Type*} [Field k] [CharZero k] {d n N : ℕ}

omit [CharZero k] in
/-- Equality of the actual independent-input canonical binary maps, including nullary multiplication. -/
theorem binaryMap_canonical [Algebra ℝ k] (n : ℕ) :
    binaryMap (d := d) (GraphBoundaryProfiles.canonicalBinaryWeight (k := k) n) =
      Gauge.CanonicalTangentCoefficients.mcFamily k d n := by
  apply MultilinearMap.ext
  intro R
  cases n with
  | zero =>
    rw [binaryMap_apply, Fintype.sum_unique]
    change (1 : k) • cochainTwoEquiv k _ (operator (emptyGraph 2) R) = _
    rw [operator_emptyGraph_two, one_smul]
    rfl
  | succ n =>
    rw [binaryMap_apply]
    change _ = Gauge.GraphTaylorCoefficients.weightedCoefficient
      Finset.univ (Kontsevich.GeometricWeights.binaryWeightOver k n) R
    rw [Gauge.GraphTaylorCoefficients.weightedCoefficient_apply]
    apply Fintype.sum_equiv (legacyEquiv (n + 1))
    intro Γ
    exact congrArg (fun B ↦ GraphBoundaryProfiles.canonicalBinaryWeight (n + 1) Γ • B)
      (operator_legacy Γ R)

/-- The arity-zero profile is the zero multilinear map, since its unique input tuple is empty. -/
theorem symmetrized_associator_zero (w : (n : ℕ) → BinaryGraph n 2 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (associatorProfile 0 w) = 0 := by
  apply MultilinearMap.ext
  intro R
  have hR : R = fun _ ↦ (0 : Bivector (k := k) (d := d)) := funext (fun i ↦ Fin.elim0 i)
  rw [hR, SymmetrizedGraphProfiles.evaluation_diagonal, evaluation_associatorProfile_zero_eq_zero]
  rfl

/-- Every arity-one tuple is its single entry; the actual one-vertex Leibniz identity gives zero. -/
theorem symmetrized_associator_one (w : (n : ℕ) → BinaryGraph n 2 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (associatorProfile 1 w) = 0 := by
  apply MultilinearMap.ext
  intro R
  have hR : R = fun _ ↦ R 0 := funext (fun i ↦ congrArg R (Fin.eq_zero i))
  rw [hR, SymmetrizedGraphProfiles.evaluation_diagonal, evaluation_associatorProfile_one_eq_zero]
  rfl

/-- Transport only the number of multilinear arguments along a proved equality. -/
def castArity (h : n = N) (F : ProfileMap k d n) : ProfileMap k d N := h ▸ F

omit [CharZero k] in
theorem evaluation_castProfile (h : n = N) (c : BinaryGraph n 3 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (castProfile h c) =
      castArity h (evaluation (symmetrizedValue (k := k) (d := d)) c) := by
  cases h
  rfl

open EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

omit [CharZero k] in
theorem evaluation_associatorProfile_grouped (N : ℕ)
    (w : (n : ℕ) → BinaryGraph n 2 → k) :
    evaluation (symmetrizedValue (k := k) (d := d)) (associatorProfile N w) =
      ∑ a : Fin (N + 1),
        (castArity (n := (a : ℕ) + (N - a)) (N := N) (d := d) (splitDegree N a)
          (symmetrize (n := (a : ℕ) + (N - a)) (groupedInsertion (a := (a : ℕ)) (b := N - a) (d := d) insertLeftLinear (binaryMap (w a)) (binaryMap (w (N-a))))) -
        castArity (n := (a : ℕ) + (N - a)) (N := N) (d := d) (splitDegree N a)
          (symmetrize (n := (a : ℕ) + (N - a)) (groupedInsertion (a := (a : ℕ)) (b := N - a) (d := d) insertRightLinear (binaryMap (w a)) (binaryMap (w (N-a)))))) := by
  simp only [associatorProfile, map_sum, map_sub, evaluation_castProfile,
    evaluation_symmetrized_graftProfile_left, evaluation_symmetrized_graftProfile_right]

end EnvelopingIsomorphism.Deformation.GraphFixedArityMaps
