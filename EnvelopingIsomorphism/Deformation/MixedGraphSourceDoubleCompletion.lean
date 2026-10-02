import EnvelopingIsomorphism.Deformation.MixedGraphDoubleEvaluation
import EnvelopingIsomorphism.FormalSeries.SlotActionCompletion
import EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalPlacements
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenEmbedding

/-! Actual double completion of the independent mixed scalar source identity. -/
noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphSourceDoubleCompletion
open scoped BigOperators Classical
open EnvelopingIsomorphism.FormalSeries
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphSourceProfiles MixedGraphDoubleEvaluation
open GraphCoefficientProfiles SymmetrizedGraphInsertion UniformBinaryGraphs SlotActionCompletion
variable {k : Type*} [Field k] [CharZero k] {d N : ℕ}

omit [CharZero k] in
theorem evaluation_symmetrized (c : VectorGraph N 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) c =
      symmetrize (evaluation (binaryValue (k := k) (d := d)) c) := by
  simp only [evaluation_apply, map_sum, map_smul, symmetrizedBinaryValue]

theorem sourceProfile_map (w : (j : ℕ) → BinaryGraph j 2 → k) (N : ℕ) :
    evaluation (binaryValue (k := k) (d := d)) (fullSourceActionProfile w N) =
      ∑ i : Fin N, actionSlot (binaryMap (d := d) (w N))
        (Gauge.LaurentSchouten.coefficientAction (K := k) (d := d)) i := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  rw [evaluation_fullSourceActionProfile]
  simp only [sum_apply, LinearMap.sum_apply, actionSlot_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (binaryMap (w N))
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    rfl
  · simp [Function.update, hj]

theorem action_eq_extendCoefficientAction :
    Gauge.LaurentSchouten.action (K := k) (d := d) =
      LaurentModule.extendBilinear (Gauge.LaurentSchouten.coefficientAction (K := k) (d := d)) := by
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro R
  rfl

theorem mixedDoubleApply_actionSlot
    (F : MultilinearMap k (fun _ : Fin N ↦ Bivector (k := k) (d := d))
      (Binary k (MvPolynomial (Fin d) k))) (i : Fin N)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    mixedDoubleApply α Y (actionSlot F (Gauge.LaurentSchouten.coefficientAction (K := k) (d := d)) i) =
      PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F)
        (Function.update (fun _ ↦ α) i (PowerSeriesModule.applyBilinear Gauge.LaurentSchouten.action Y α)) := by
  have h := double_actionSlot F (Gauge.LaurentSchouten.coefficientAction (K := k) (d := d)) i (fun _ ↦ α) Y
  refine h.trans ?_
  apply congrArg (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F))
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, action_eq_extendCoefficientAction]
  · simp [Function.update, hj]

/-- Every actual scalar source split contributes exactly its completed action-slot derivative. -/
theorem sourceProfile_double (w : (j : ℕ) → BinaryGraph j 2 → k) (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    mixedDoubleApply α Y
      (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (fullSourceActionProfile w N)) =
      ∑ i : Fin N, PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars (binaryMap (d := d) (w N)))
        (Function.update (fun _ ↦ α) i (PowerSeriesModule.applyBilinear Gauge.LaurentSchouten.action Y α)) := by
  rw [evaluation_symmetrized, mixedDoubleApply_symmetrize, sourceProfile_map, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mixedDoubleApply_actionSlot _ i α Y

/-- The actual canonical source profile is the existing completed ordered directional term.
The empty slot sum covers N=0 without a separate assumed identity. -/
theorem canonical_sourceProfile_double [Algebra ℝ k] (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    mixedDoubleApply α Y
      (evaluation (symmetrizedBinaryValue (k := k) (d := d))
        (fullSourceActionProfile (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)) N)) =
      Gauge.LaurentDirectionalPlacements.directionalTerm
        (LaurentModule.extendScalars (Gauge.CanonicalTangentCoefficients.mcFamily k d N)) α
        (PowerSeriesModule.applyBilinear Gauge.LaurentSchouten.action Y α) := by
  rw [sourceProfile_double]
  simp only [GraphFixedArityMaps.binaryMap_canonical, Gauge.LaurentDirectionalPlacements.directionalTerm]

end EnvelopingIsomorphism.Deformation.MixedGraphSourceDoubleCompletion
