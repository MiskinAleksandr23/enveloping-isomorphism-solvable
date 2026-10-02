import EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentArityBounds
import EnvelopingIsomorphism.Deformation.Gauge.LaurentTangentFullIdentity

/-! The actual mixed arity sum equals full-family application and the existing tangent map. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentFullEvaluation
open EnvelopingIsomorphism.FormalSeries
open scoped BigOperators Classical

section Generic
universe u v
variable {k : Type u} [CommRing k] {U Y W : Type v}
  [AddCommGroup U] [Module k U] [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]
open LaurentAritySummation

/-- A fixed direction commutes with the genuine arity sum, using finite-jet tail estimates. -/
theorem sum_bilinear_eq_bilinear_sum (f : U →ₗ[k] Y →ₗ[k] W)
    (A : ℕ → Series k U) (hA : Summable A) (X : Series k Y)
    (hAX : Summable (fun m ↦ bilinear f (A m) X))
    (hlocal : ∀ D : ℕ, ∃ K : ℤ,
      (∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K) (PowerSeriesModule.coeffV e (A m))) ∧
      (∀ e ≤ D, LaurentModule.BoundedBelow ((e : ℤ) * K) (PowerSeriesModule.coeffV e X))) :
    sumSeries (fun m ↦ bilinear f (A m) X) hAX = bilinear f (sumSeries A hA) X := by
  apply PowerSeriesModule.ext
  intro D
  apply LaurentModule.ext
  intro H
  obtain ⟨K, hAb, hXb⟩ := hlocal D
  let N := (H - (D : ℤ) * K).toNat + 1
  have hN : H < (N : ℤ) + (D : ℤ) * K := by dsimp [N]; omega
  have hT (m : ℕ) : LaurentModule.BoundedBelow ((m : ℤ) + (D : ℤ) * K)
      (PowerSeriesModule.coeffV D (bilinear f (A m) X)) := by
    simpa only [add_zero] using bilinear_bound f (A m) X D (m : ℤ) 0 K
      (fun e he ↦ hAb e he m) (fun e he ↦ by simpa only [zero_add] using hXb e he)
  have htail := bilinear_bound f (sumSeries A hA - truncate A N) X D (N : ℤ) 0 K
    (fun e he ↦ tail_bound A hA e _ (hAb e he) N)
    (fun e he ↦ by simpa only [zero_add] using hXb e he)
  have hz := htail H (by simpa only [add_zero] using hN)
  rw [map_sub, LinearMap.sub_apply, PowerSeriesModule.coeffV_sub, LaurentModule.coeff_sub] at hz
  have heq := sub_eq_zero.mp hz
  rw [coeff_sumSeries, jointSum_eq_truncate _ D ((D : ℤ) * K) hT N H hN, heq]
  simp only [truncate, map_sum, LinearMap.sum_apply, PowerSeriesModule.coeffV_sum, coeff_finset_sum]

end Generic

section Mixed
universe u v
variable {k : Type u} [Field k] {V Y W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]
open LaurentTaylorArityBounds MixedLaurentArityBounds

/-- The constructed mixed sum is the actual full family applied to its Laurent direction. -/
theorem fullMixedEvaluation_eq_fullEvaluation
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) :
    fullMixedEvaluation C π₀ β hβ X hX =
      PowerSeriesModule.applyBilinear LaurentModule.linearApply
        (LaurentFullGraphEvaluation.fullEvaluation C π₀ β hβ) X := by
  have hsum := sum_bilinear_eq_bilinear_sum
    (LinearMap.id : (Y →ₗ[k] W) →ₗ[k] Y →ₗ[k] W)
    (arityTerm C (fullInput π₀ β)) (LaurentFullGraphSummation.arityTerm_summable C π₀ β hβ) X
    (show LaurentAritySummation.Summable (fun m ↦ LaurentAritySummation.bilinear
      (LinearMap.id : (Y →ₗ[k] W) →ₗ[k] Y →ₗ[k] W) (arityTerm C (fullInput π₀ β) m) X) from
      mixedTerm_summable C π₀ β hβ X hX) (by
        intro D
        obtain ⟨K, _, hα, hY⟩ := exists_common_jet_slope π₀ β hβ X hX D
        refine ⟨K, ?_, hY⟩
        intro e he m
        simpa only [add_sub_cancel_right] using arityTerm_bound C _ e m (K + 1)
          (fun j hj ↦ by simpa only [add_sub_cancel_right] using hα j (hj.trans he)))
  rw [LaurentFullGraphSummation.sumSeries_eq_fullEvaluation] at hsum
  exact hsum

end Mixed

section Tangent
universe u
variable {k V Y W : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]
open MixedLaurentArityBounds

/-- Reuse the proved all-placement tangent identity on the actual mixed sum. -/
theorem fullMixedEvaluation_eq_tangentApply
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) :
    fullMixedEvaluation C π₀ β hβ X hX =
      tangentApply (MixedGraphTaylorCoefficients.tangentFamily C π₀) β X := by
  rw [fullMixedEvaluation_eq_fullEvaluation, LaurentTangentFullIdentity.tangentApply_eq_fullEvaluation]

end Tangent
end EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentFullEvaluation
