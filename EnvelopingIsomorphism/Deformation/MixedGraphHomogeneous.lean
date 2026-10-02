import EnvelopingIsomorphism.Deformation.MixedGraphTargetPowerSeries
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionPowerSeries

/-! The genuine mixed scalar boundary relation gives the completed
homogeneous source/target identity on every actual Laurent Poisson t-family. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MixedGraphHomogeneous
open EnvelopingIsomorphism.FormalSeries
open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles
open MixedGraphDoubleEvaluation MixedGraphBoundaryProfiles
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}

/-- The two-odd correction disappears only after its actual completed source
curvature is zero. The remaining target is the genuine homogeneous gauge action. -/
theorem canonical_source_eq_target
    (h : CanonicalScalarMixedBoundaryRelation (k := k)) (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d))))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) :
    mixedDoubleApply α Y (evaluation (symmetrizedBinaryValue (k := k) (d := d))
      (MixedGraphSourceProfiles.fullSourceActionProfile
        (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)) N)) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
          (Gauge.MixedLaurentArityBounds.mixedTerm (Gauge.CanonicalTangentCoefficients.velocityFamily k d) α Y ab.1)
          (Gauge.LaurentTaylorArityBounds.arityTerm (Gauge.CanonicalTangentCoefficients.mcFamily k d) α ab.2) := by
  have he := scalarMixedBoundaryRelation_double h N α Y
  rw [MixedGraphCorrectionPowerSeries.mixedDoubleApply_fullCorrectionProfile_eq_zero
    (fun _ ↦ MixedGraphCorrectionProfiles.canonicalQuotientWeight (k := k)) N α Y hα, add_zero] at he
  exact he.trans (MixedGraphTargetPowerSeries.canonical_targetActionProfile_double N α Y)

end EnvelopingIsomorphism.Deformation.MixedGraphHomogeneous
