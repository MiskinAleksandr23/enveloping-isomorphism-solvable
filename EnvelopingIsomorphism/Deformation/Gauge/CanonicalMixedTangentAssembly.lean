import EnvelopingIsomorphism.Deformation.MixedGraphHomogeneous
import EnvelopingIsomorphism.Deformation.Gauge.LaurentHomogeneousComparison
import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorDerivativeRecombination
import EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentFullEvaluation

/-! Genuine all-arity assembly of the mixed tangent/gauge equation. Every
coefficient sum is controlled by the actual finite t-jet Laurent bounds. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalMixedTangentAssembly
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open LaurentTaylorArityBounds LaurentFullGraphEvaluation LaurentFullGraphSummation
open MixedLaurentArityBounds
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

abbrev BivectorSeries := PowerSeriesModule (LaurentSeries k) (LaurentSchouten.Bivector k d)
abbrev VectorSeries := PowerSeriesModule (LaurentSeries k) (LaurentSchouten.Vector k d)

def actionDirection (π₀ : CanonicalGraph.BaseBivector k d)
    (β : BivectorSeries (k := k) (d := d)) (Y : VectorSeries (k := k) (d := d)) :=
  applyBilinear LaurentSchouten.action Y (fullInput π₀ β)

omit [Algebra ℝ k] in
theorem actionDirection_positive (π₀ : CanonicalGraph.BaseBivector k d)
    (β : BivectorSeries (k := k) (d := d)) (Y : VectorSeries (k := k) (d := d))
    (hY : coeffV 0 Y = 0) : coeffV 0 (actionDirection π₀ β Y) = 0 := by
  simp [actionDirection, coeffV_applyBilinear, hY]

omit [CharZero k] [Algebra ℝ k] in
theorem unaryCoefficientAction_eq_extension :
    LaurentConjugation.unaryCoefficientAction (k := k) (A := MvPolynomial (Fin d) k) =
      LaurentModule.extendBilinear (unaryActionLinear (k := k) (V := MvPolynomial (Fin d) k)) := by
  apply LinearMap.ext
  intro U
  apply LinearMap.ext
  intro B
  exact (MixedGraphTargetPowerSeries.extend_unaryActionLinear U B).symm

/-- Proved homogeneous graph equations sum to the actual canonical tangent
equation. The finite equations will be supplied by the pure scalar profiles. -/
theorem tangentEquation_of_homogeneous
    (π₀ : CanonicalGraph.BaseBivector k d) (β : BivectorSeries (k := k) (d := d))
    (hβ : coeffV 0 β = 0) (Y : VectorSeries (k := k) (d := d)) (hY : coeffV 0 Y = 0)
    (hhom : ∀ N,
      LaurentDirectionalPlacements.directionalTerm
        (LaurentModule.extendScalars (CanonicalTangentCoefficients.mcFamily k d N))
        (fullInput π₀ β) (actionDirection π₀ β Y) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        applyBilinear LaurentConjugation.unaryCoefficientAction
          (mixedTerm (CanonicalTangentCoefficients.velocityFamily k d) (fullInput π₀ β) Y ab.1)
          (arityTerm (CanonicalTangentCoefficients.mcFamily k d) (fullInput π₀ β) ab.2)) :
    taylorDerivativeApply (CanonicalGraph.taylor k d π₀) β (actionDirection π₀ β Y) =
      applyBilinear LaurentConjugation.unaryCoefficientAction
        (tangentApply (CanonicalGraph.velocityTangent k d π₀) β Y)
        (single 0 (CanonicalGraph.targetBase k d π₀) + taylorApply (CanonicalGraph.taylor k d π₀) β) := by
  let A := mixedTerm (CanonicalTangentCoefficients.velocityFamily k d) (fullInput π₀ β) Y
  let B := arityTerm (CanonicalTangentCoefficients.mcFamily k d) (fullInput π₀ β)
  have hA := mixedTerm_summable (CanonicalTangentCoefficients.velocityFamily k d) π₀ β hβ Y hY
  have hB := arityTerm_summable (CanonicalTangentCoefficients.mcFamily k d) π₀ β hβ
  have hlocal : ∀ D : ℕ, ∃ K : ℤ,
      (∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K) (coeffV e (A m))) ∧
      (∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K) (coeffV e (B m))) := by
    intro D
    obtain ⟨K, hK, hα, hYb⟩ := exists_common_jet_slope π₀ β hβ Y hY D
    refine ⟨K, ?_, ?_⟩
    · intro e he m
      exact mixedTerm_bound _ _ _ e m K
        (fun j hj ↦ hα j (hj.trans he)) (fun j hj ↦ hYb j (hj.trans he))
    · intro e he m
      have hb := arityTerm_bound (CanonicalTangentCoefficients.mcFamily k d)
        (fullInput π₀ β) e m (K + 1) (by
          intro j hj
          simpa only [add_sub_cancel_right] using hα j (hj.trans he))
      simpa only [add_sub_cancel_right] using hb
  have hs := LaurentHomogeneousComparison.eq_bilinear_of_coeff_homogeneous
    (unaryActionLinear (k := k) (V := MvPolynomial (Fin d) k)) A B hA hB hlocal
    (taylorDerivativeApply (CanonicalGraph.taylor k d π₀) β (actionDirection π₀ β Y))
    (by
      intro D H
      rw [show CanonicalGraph.taylor k d π₀ =
        laurentPlacementTaylorFamily (CanonicalTangentCoefficients.mcFamily k d) π₀ from rfl]
      rw [LaurentTaylorDerivativeRecombination.coeff_taylorDerivative_eq_allArity
        (CanonicalTangentCoefficients.mcFamily k d) π₀ β (actionDirection π₀ β Y)
        hβ (actionDirection_positive π₀ β Y hY) D H]
      apply finsum_congr
      intro N
      have hh := congrArg (fun P ↦ LaurentModule.coeff (coeffV D P) H) (hhom N)
      rw [unaryCoefficientAction_eq_extension] at hh
      exact hh)
  have hsumA : LaurentAritySummation.sumSeries A hA =
      tangentApply (CanonicalGraph.velocityTangent k d π₀) β Y :=
    MixedLaurentFullEvaluation.fullMixedEvaluation_eq_tangentApply
      (CanonicalTangentCoefficients.velocityFamily k d) π₀ β hβ Y hY
  have hsumB : LaurentAritySummation.sumSeries B hB =
      single 0 (CanonicalGraph.targetBase k d π₀) + taylorApply (CanonicalGraph.taylor k d π₀) β := by
    exact (sumSeries_eq_fullEvaluation (CanonicalTangentCoefficients.mcFamily k d) π₀ β hβ).trans
      (LaurentTaylorFullIdentity.fullEvaluation_eq_base_add_taylor
        (CanonicalTangentCoefficients.mcFamily k d) π₀ β hβ)
  rw [hsumA, hsumB] at hs
  rw [unaryCoefficientAction_eq_extension]
  exact hs

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalMixedTangentAssembly
