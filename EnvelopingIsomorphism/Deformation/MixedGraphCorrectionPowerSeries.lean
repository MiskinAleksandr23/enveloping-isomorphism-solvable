import EnvelopingIsomorphism.Deformation.MixedGraphDoubleEvaluation
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionBinary

/-! Fixed outer-power-series evaluation of the actual signed mixed correction.
The independent-input grouped composition is extended through both genuine
Laurent and outer-t convolutions. Full outer-t curvature zero kills the result
for every independent vector series, without an arity-summability assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.MixedGraphCorrectionPowerSeries

open EnvelopingIsomorphism.FormalSeries
open MixedGraphProfileCarrier MixedGraphCorrectionProfiles MixedGraphCorrectionMultilinear
open MixedGraphCorrectionBinary MixedGraphDoubleEvaluation GraphCoefficientProfiles
open GraphFixedArityPowerSeries
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

abbrev BivectorSeries := PowerSeriesModule (LaurentSeries k)
  (LaurentModule k (Bivector (k := k) (d := d)))
abbrev VectorSeries := PowerSeriesModule (LaurentSeries k)
  (LaurentModule k (Vector (k := k) (d := d)))

/-- Reordering the curried output slots keeps the already established X,Q
placement signs inside the actual correction source family. -/
def sourceFlip (w : CorrectionGraph n → k) :
    MultilinearMap k (fun _ : Fin n => Bivector (k := k) (d := d))
      (Trivector (k := k) (d := d) →ₗ[k] Vector (k := k) (d := d) →ₗ[k]
        Binary k (MvPolynomial (Fin d) k)) :=
  let flip : (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k)) →ₗ[k]
      (Trivector (k := k) (d := d) →ₗ[k] Vector (k := k) (d := d) →ₗ[k]
        Binary k (MvPolynomial (Fin d) k)) :=
    { toFun F := F.flip
      map_add' F G := by ext Q X; rfl
      map_smul' r F := by ext Q X; rfl }
  flip.compMultilinearMap (correctionSource w)

/-- Independent-input source composition, before either completion is taken. -/
theorem mapped_groupedCorrection_eq_groupedBilinear (w : CorrectionGraph n → k) :
    mapBinary (groupedCorrectionMap (k := k) (d := d) w) =
      LaurentModule.groupedBilinear LinearMap.id (sourceFlip w)
        ((1 / 2 : k) • GraphMultilinearCurvature.bracketMap) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  rw [groupedCorrectionMap_source, LaurentModule.groupedBilinear_apply]
  rfl

/-- Exact outer-t convolution of the actual Laurent source correction. The
constant-field embedding of one-half is retained at the completed curvature slot. -/
theorem doubleApply_groupedCorrection (w : CorrectionGraph n → k)
    (α : BivectorSeries (k := k) (d := d)) :
    doubleApplyLinear (fun _ => α) (mapBinary (groupedCorrectionMap w)) =
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
        (doubleApplyLinear (fun _ => α) (sourceFlip w))
        ((HahnSeries.C (1 / 2 : k) : LaurentSeries k) •
          PowerSeriesModule.applyBilinear
            (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α) := by
  rw [mapped_groupedCorrection_eq_groupedBilinear]
  change PowerSeriesModule.applyMultilinear
    (LaurentModule.extendScalars (LaurentModule.groupedBilinear LinearMap.id _ _)) (fun _ => α) = _
  rw [PowerSeriesModule.applyMultilinear_groupedBilinear_laurent_diagonal]
  change PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
    (doubleApplyLinear (fun _ => α) _)
    (doubleApplyLinear (fun _ => α) ((1 / 2 : k) • GraphMultilinearCurvature.bracketMap)) = _
  rw [map_smulₛₗ, doubleApply_bracketMap]

/-- Full outer-t curvature zero kills the completed correction as an operator
on the vector argument, before that independent argument is evaluated. -/
theorem doubleApply_groupedCorrection_eq_zero (w : CorrectionGraph n → k)
    (α : BivectorSeries (k := k) (d := d))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) :
    doubleApplyLinear (fun _ => α) (mapBinary (groupedCorrectionMap w)) = 0 := by
  rw [doubleApply_groupedCorrection, hα, smul_zero]
  change PowerSeriesModule.extendBilinear _ _ 0 = 0
  exact map_zero _

/-- Exact evaluation of the symmetrized scalar correction on arbitrary actual
outer-t Laurent bivector and vector series, with no scalar-curvature assumption. -/
theorem mixedDoubleApply_correction (w : CorrectionGraph n → k)
    (α : BivectorSeries (k := k) (d := d)) (Y : VectorSeries (k := k) (d := d)) :
    mixedDoubleApply α Y
      (evaluation (MixedGraphAveraging.symmetrizedBinaryValue (k := k) (d := d)) (correctionProfile w)) =
      PowerSeriesModule.applyBilinear LaurentModule.linearApply
        (PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
          (doubleApplyLinear (fun _ => α) (sourceFlip w))
          ((HahnSeries.C (1 / 2 : k) : LaurentSeries k) •
            PowerSeriesModule.applyBilinear
              (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α)) Y := by
  rw [evaluation_symmetrized_correctionProfile_binary, mixedDoubleApply_symmetrize]
  change PowerSeriesModule.applyBilinear LaurentModule.linearApply
    (doubleApplyLinear (fun _ => α) (mapBinary (groupedCorrectionMap w))) Y = _
  rw [doubleApply_groupedCorrection]

/-- The requested fixed-arity source cancellation. The assumption is the full
outer power-series Laurent bracket square, not individual polynomial diagonal identities. -/
theorem mixedDoubleApply_correction_eq_zero (w : CorrectionGraph n → k)
    (α : BivectorSeries (k := k) (d := d)) (Y : VectorSeries (k := k) (d := d))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) :
    mixedDoubleApply α Y
      (evaluation (MixedGraphAveraging.symmetrizedBinaryValue (k := k) (d := d)) (correctionProfile w)) = 0 := by
  rw [evaluation_symmetrized_correctionProfile_binary, mixedDoubleApply_symmetrize]
  change PowerSeriesModule.applyBilinear LaurentModule.linearApply
    (doubleApplyLinear (fun _ => α) (mapBinary (groupedCorrectionMap w))) Y = 0
  rw [doubleApply_groupedCorrection_eq_zero w α hα]
  change PowerSeriesModule.extendBilinear _ 0 Y = 0
  rw [map_zero, LinearMap.zero_apply]

/-- Every total arity, including the two genuinely zero low-arity correction profiles. -/
theorem mixedDoubleApply_fullCorrectionProfile_eq_zero
    (w : (j : ℕ) → CorrectionGraph j → k) (N : ℕ)
    (α : BivectorSeries (k := k) (d := d)) (Y : VectorSeries (k := k) (d := d))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) :
    mixedDoubleApply α Y
      (evaluation (MixedGraphAveraging.symmetrizedBinaryValue (k := k) (d := d))
        (MixedGraphBoundaryProfiles.fullCorrectionProfile w N)) = 0 := by
  rcases N with _ | (_ | n)
  · simp only [MixedGraphBoundaryProfiles.fullCorrectionProfile, map_zero]
  · simp only [MixedGraphBoundaryProfiles.fullCorrectionProfile, map_zero]
  · exact mixedDoubleApply_correction_eq_zero (w n) α Y hα

end EnvelopingIsomorphism.Deformation.MixedGraphCorrectionPowerSeries
