import EnvelopingIsomorphism.Deformation.MixedGraphBoundaryProfiles
import EnvelopingIsomorphism.Deformation.GraphFixedArityPowerSeries

/-! Actual h-Laurent and outer-t evaluation of independent mixed graph maps.
The vector argument is evaluated separately by the genuine linear cochain
convolution; semilinearity records the constant embedding k → k((h)). -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MixedGraphDoubleEvaluation
open EnvelopingIsomorphism.FormalSeries
open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

def mixedDoubleApply
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedMap k d n →ₛₗ[(HahnSeries.C : k →+* LaurentSeries k)]
      PowerSeriesModule (LaurentSeries k) (LaurentModule k (Binary k (MvPolynomial (Fin d) k))) where
  toFun F := PowerSeriesModule.applyBilinear LaurentModule.linearApply
    (GraphFixedArityPowerSeries.doubleApplyLinear (fun _ ↦ α) F) Y
  map_add' F G := by
    rw [map_add]
    apply PowerSeriesModule.ext
    intro D
    simp only [PowerSeriesModule.coeffV_applyBilinear, PowerSeriesModule.coeffV_add,
      map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' r F := by
    rw [map_smulₛₗ]
    apply PowerSeriesModule.ext
    intro D
    simp only [PowerSeriesModule.coeffV_applyBilinear, PowerSeriesModule.coeffV_smul,
      map_smul, LinearMap.smul_apply, Finset.smul_sum]

omit [CharZero k] in
@[simp] theorem mixedDoubleApply_apply
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d))))
    (F : MixedMap k d n) :
    mixedDoubleApply α Y F = PowerSeriesModule.applyBilinear LaurentModule.linearApply
      (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F) (fun _ ↦ α)) Y := rfl

omit [CharZero k] in
theorem mixedDoubleApply_domDomCongr
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d))))
    (F : MixedMap k d n) (σ : Equiv.Perm (Fin n)) :
    mixedDoubleApply α Y (F.domDomCongr σ) = mixedDoubleApply α Y F := by
  change PowerSeriesModule.applyBilinear LaurentModule.linearApply
    (GraphFixedArityPowerSeries.doubleApplyLinear (fun _ ↦ α) (F.domDomCongr σ)) Y = _
  rw [GraphFixedArityPowerSeries.doubleApply_domDomCongr]
  rfl

omit [CharZero k] in
theorem symmetrize_eq_sum (F : MixedMap k d n) :
    symmetrize F = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), F.domDomCongr σ := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- Symmetrization is removed by genuine double coefficient reindexing,
not by a diagonal polynomial specialization. -/
theorem mixedDoubleApply_symmetrize
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d))))
    (F : MixedMap k d n) : mixedDoubleApply α Y (symmetrize F) = mixedDoubleApply α Y F := by
  rw [symmetrize_eq_sum, map_smulₛₗ, map_sum]
  simp only [mixedDoubleApply_domDomCongr, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul (LaurentSeries k),
    smul_smul, map_inv₀, map_natCast]
  have hn : (n.factorial : LaurentSeries k) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C : k →+* LaurentSeries k)]
    exact HahnSeries.C_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [inv_mul_cancel₀ hn, one_smul]

/-- The pure mixed scalar relation is consumed after both genuine completions. -/
theorem scalarMixedBoundaryRelation_double
    {w : (j : ℕ) → UniformBinaryGraphs.BinaryGraph j 2 → k}
    {v : (j : ℕ) → VectorGraph j 1 → k}
    {u : (j : ℕ) → MixedGraphCorrectionProfiles.CorrectionGraph j → k}
    (h : MixedGraphBoundaryProfiles.ScalarMixedBoundaryRelation w v u) (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (MixedGraphSourceProfiles.fullSourceActionProfile w N)) +
      mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (MixedGraphBoundaryProfiles.fullCorrectionProfile u N)) =
      mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (MixedGraphTargetProfiles.targetActionProfile N v w)) := by
  rw [← map_add, MixedGraphBoundaryProfiles.evaluation_scalarMixedBoundaryRelation h]

end EnvelopingIsomorphism.Deformation.MixedGraphDoubleEvaluation
