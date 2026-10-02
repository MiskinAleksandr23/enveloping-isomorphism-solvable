import EnvelopingIsomorphism.Deformation.MixedGraphDoubleEvaluation
import EnvelopingIsomorphism.Deformation.MixedGraphTargetGrouped
import EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentArityBounds
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenEmbedding
import EnvelopingIsomorphism.FormalSeries.PowerSeriesGroupedMultilinear

/-! Actual Laurent and outer-t evaluation of the complete mixed target graft profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.MixedGraphTargetPowerSeries

open EnvelopingIsomorphism.FormalSeries
open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles MixedGraphTargetProfiles
open UniformBinaryGraphs
open scoped BigOperators Classical

variable {k : Type*} [Field k] {d : ℕ}

abbrev PolynomialSpace := MvPolynomial (Fin d) k

/-- The generic coefficient unary action has exactly the existing closed Laurent-cochain extension. -/
theorem extend_unaryActionLinear
    (H : LaurentModule k (Unary k (PolynomialSpace (k := k) (d := d))))
    (C : LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d)))) :
    LaurentModule.extendBilinear (Gauge.unaryActionLinear (k := k) (V := PolynomialSpace)) H C =
      Gauge.LaurentConjugation.unaryCoefficientAction H C := by
  have he : Gauge.unaryActionLinear (k := k) (V := PolynomialSpace (k := k) (d := d)) =
      Gauge.LaurentSchouten.unaryActionLinear := by ext F B f g; rfl
  rw [he]
  exact Gauge.LaurentSchouten.extend_unaryAction H C

/-- Moving the independent vector through a target action is an identity of the
actual Laurent convolutions, checked on monomials with their full lower bounds. -/
theorem linearApply_targetAction
    (H : LaurentModule k (Vector (k := k) (d := d) →ₗ[k] Unary k (PolynomialSpace (k := k) (d := d))))
    (C : LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d))))
    (Y : LaurentModule k (Vector (k := k) (d := d))) :
    LaurentModule.linearApply (LaurentModule.extendBilinear actionBilinear H C) Y =
      Gauge.LaurentConjugation.unaryCoefficientAction (LaurentModule.linearApply H Y) C := by
  let U := Gauge.unaryActionLinear (k := k) (V := PolynomialSpace (k := k) (d := d))
  let L : LaurentModule k (Vector (k := k) (d := d) →ₗ[k] Unary k (PolynomialSpace (k := k) (d := d))) →ₗ[k]
      LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d))) →ₗ[k]
        LaurentModule k (Vector (k := k) (d := d)) →ₗ[k]
          LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d))) :=
    (LaurentModule.restrictBilinear (LaurentModule.extendBilinear actionBilinear)).compr₂
      (LaurentModule.restrictBilinear LaurentModule.linearApply)
  let R₀ : LaurentModule k (Vector (k := k) (d := d) →ₗ[k] Unary k (PolynomialSpace (k := k) (d := d))) →ₗ[k]
      LaurentModule k (Vector (k := k) (d := d)) →ₗ[k]
        LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d))) →ₗ[k]
          LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d))) :=
    (LaurentModule.restrictBilinear LaurentModule.linearApply).compr₂
      (LaurentModule.restrictBilinear (LaurentModule.extendBilinear U))
  let R := (LinearMap.lflip (R₀ := k)).toLinearMap.comp R₀
  have he : L = R := by
    apply LaurentModule.trilinear_ext_of_bounded _ _ 0
    · intro H C Y h c y hH hC hY
      change LaurentModule.BoundedBelow (((h + c) + y) + 0)
        (LaurentModule.linearApply (LaurentModule.extendBilinear actionBilinear H C) Y)
      simpa only [add_zero] using LaurentModule.boundedBelow_linearApply _ Y
        (LaurentModule.boundedBelow_extendBilinear actionBilinear H C hH hC) hY
    · intro H C Y h c y hH hC hY
      change LaurentModule.BoundedBelow (((h + c) + y) + 0)
        (LaurentModule.extendBilinear U (LaurentModule.linearApply H Y) C)
      have hb := LaurentModule.boundedBelow_extendBilinear U _ C
        (LaurentModule.boundedBelow_linearApply H Y hH hY) hC
      convert hb using 1
      omega
    · intro h c y H C Y
      change LaurentModule.linearApply
          (LaurentModule.extendBilinear actionBilinear (LaurentModule.single h H) (LaurentModule.single c C))
          (LaurentModule.single y Y) =
        LaurentModule.extendBilinear U
          (LaurentModule.linearApply (LaurentModule.single h H) (LaurentModule.single y Y))
          (LaurentModule.single c C)
      rw [LaurentModule.extendBilinear_single, LaurentModule.linearApply_single,
        LaurentModule.linearApply_single, LaurentModule.extendBilinear_single]
      congr 1
      omega
  have hv := congrArg (fun F => F H C Y) he
  change LaurentModule.linearApply (LaurentModule.extendBilinear actionBilinear H C) Y =
    LaurentModule.extendBilinear U (LaurentModule.linearApply H Y) C at hv
  exact hv.trans (extend_unaryActionLinear _ C)

/-- Finite outer-t antidiagonal reindexing moves the vector evaluation past the
actual Laurent target action, retaining all three independent series. -/
theorem powerSeries_targetAction
    (H : PowerSeriesModule (LaurentSeries k)
      (LaurentModule k (Vector (k := k) (d := d) →ₗ[k] Unary k (PolynomialSpace (k := k) (d := d)))))
    (C : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d)))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    PowerSeriesModule.applyBilinear LaurentModule.linearApply
        (PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear actionBilinear) H C) Y =
      PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
        (PowerSeriesModule.applyBilinear LaurentModule.linearApply H Y) C := by
  apply PowerSeriesModule.ext
  intro D
  simp only [PowerSeriesModule.coeffV_applyBilinear, map_sum, LinearMap.sum_apply]
  simp_rw [linearApply_targetAction]
  rw [PowerSeriesModule.sum_antidiagonal_assoc
    (fun h c y => Gauge.LaurentConjugation.unaryCoefficientAction
      (LaurentModule.linearApply (PowerSeriesModule.coeffV h H) (PowerSeriesModule.coeffV y Y))
      (PowerSeriesModule.coeffV c C)) D]
  rw [PowerSeriesModule.sum_antidiagonal_assoc
    (fun h y c => Gauge.LaurentConjugation.unaryCoefficientAction
      (LaurentModule.linearApply (PowerSeriesModule.coeffV h H) (PowerSeriesModule.coeffV y Y))
      (PowerSeriesModule.coeffV c C)) D]
  apply Finset.sum_congr rfl
  intro p hp
  exact (Finset.Nat.sum_antidiagonal_swap (f := fun q =>
    Gauge.LaurentConjugation.unaryCoefficientAction
      (LaurentModule.linearApply (PowerSeriesModule.coeffV p.1 H) (PowerSeriesModule.coeffV q.2 Y))
      (PowerSeriesModule.coeffV q.1 C))).symm

/-- Actual two-level grouped multilinear evaluation followed by the independent vector action. -/
theorem mixedDoubleApply_grouped {a b : ℕ}
    (F : MultilinearMap k (fun _ : Fin a => Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Unary k (PolynomialSpace (k := k) (d := d))))
    (G : MultilinearMap k (fun _ : Fin b => Bivector (k := k) (d := d))
      (Binary k (PolynomialSpace (k := k) (d := d))))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y (LaurentModule.groupedBilinear actionBilinear F G) =
      PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
        (PowerSeriesModule.applyBilinear LaurentModule.linearApply
          (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F) (fun _ => α)) Y)
        (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars G) (fun _ => α)) := by
  rw [MixedGraphDoubleEvaluation.mixedDoubleApply_apply,
    PowerSeriesModule.applyMultilinear_groupedBilinear_laurent_diagonal, powerSeries_targetAction]

/-- The same fixed-degree equality in the existing actual mixedTerm/arityTerm API. -/
theorem mixedDoubleApply_grouped_family
    (V : Gauge.MixedLaurentArityBounds.CurriedFamily (k := k)
      (V := Bivector (k := k) (d := d)) (Y := Vector (k := k) (d := d))
      (W := Unary k (PolynomialSpace (k := k) (d := d))))
    (C : Gauge.GraphTaylorFamily (k := k) (V := Bivector (k := k) (d := d))
      (W := Binary k (PolynomialSpace (k := k) (d := d)))) (a b : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y (LaurentModule.groupedBilinear actionBilinear (V a) (C b)) =
      PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
        (Gauge.MixedLaurentArityBounds.mixedTerm V α Y a)
        (Gauge.LaurentTaylorArityBounds.arityTerm C α b) :=
  mixedDoubleApply_grouped (V a) (C b) α Y

/-- The arity-count casts keep the actual double-evaluated map unchanged. -/
theorem mixedDoubleApply_castMixedMap {n N : ℕ} (h : n = N) (F : MixedMap k d n)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y (castMixedMap h F) =
      MixedGraphDoubleEvaluation.mixedDoubleApply α Y F := by subst N; rfl

variable [CharZero k]

set_option maxHeartbeats 800000 in
/-- Every genuine fixed-degree target profile evaluates to the finite sum of
closed coefficient actions on actual independently completed series. -/
theorem targetActionProfile_double (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (targetActionProfile N w v)) =
      ∑ a : Fin (N + 1), PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
        (Gauge.MixedLaurentArityBounds.mixedTerm (fun a => weightedVelocity (w a)) α Y a)
        (Gauge.LaurentTaylorArityBounds.arityTerm (fun b => SymmetrizedGraphInsertion.binaryMap (v b)) α (N - a)) := by
  rw [evaluation_targetActionProfile_symmetrized (k := k) (d := d) N w v, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mixedDoubleApply_castMixedMap, MixedGraphDoubleEvaluation.mixedDoubleApply_symmetrize]
  exact mixedDoubleApply_grouped_family (fun n => weightedVelocity (w n))
    (fun n => SymmetrizedGraphInsertion.binaryMap (v n)) a (N - a) α Y

set_option maxHeartbeats 800000 in
/-- The same genuine completed target action, indexed by the actual total-arity antidiagonal. -/
theorem targetActionProfile_double_antidiagonal (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d)) (targetActionProfile N w v)) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
          (Gauge.MixedLaurentArityBounds.mixedTerm (fun a => weightedVelocity (w a)) α Y ab.1)
          (Gauge.LaurentTaylorArityBounds.arityTerm (fun b => SymmetrizedGraphInsertion.binaryMap (v b)) α ab.2) := by
  rw [targetActionProfile_double N w v α Y]
  let f : ℕ → ℕ → PowerSeriesModule (LaurentSeries k)
      (LaurentModule k (Binary k (PolynomialSpace (k := k) (d := d)))) := fun a b =>
    PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
      (Gauge.MixedLaurentArityBounds.mixedTerm (fun a => weightedVelocity (w a)) α Y a)
      (Gauge.LaurentTaylorArityBounds.arityTerm (fun b => SymmetrizedGraphInsertion.binaryMap (v b)) α b)
  change (∑ a : Fin (N + 1), f a (N - a)) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N, f ab.1 ab.2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ f N, ← Fin.sum_univ_eq_sum_range]

variable [Algebra ℝ k]

set_option maxHeartbeats 800000 in
/-- Canonical weights identify the completed target with the actual velocity and MC
families, including every zero-degree contribution and without an assumed graph law. -/
theorem canonical_targetActionProfile_double (N : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (Y : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Vector (k := k) (d := d)))) :
    MixedGraphDoubleEvaluation.mixedDoubleApply α Y
        (evaluation (symmetrizedBinaryValue (k := k) (d := d))
          (targetActionProfile N (fun _ => MixedGraphBoundaryProfiles.canonicalVelocityWeight)
            (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)))) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeriesModule.applyBilinear Gauge.LaurentConjugation.unaryCoefficientAction
          (Gauge.MixedLaurentArityBounds.mixedTerm (Gauge.CanonicalTangentCoefficients.velocityFamily k d) α Y ab.1)
          (Gauge.LaurentTaylorArityBounds.arityTerm (Gauge.CanonicalTangentCoefficients.mcFamily k d) α ab.2) := by
  have h := targetActionProfile_double_antidiagonal N
    (fun _ => MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := k))
    (GraphBoundaryProfiles.canonicalBinaryWeight (k := k)) α Y
  simpa only [MixedGraphBoundaryProfiles.weightedVelocity_canonical,
    GraphFixedArityMaps.binaryMap_canonical] using h

end EnvelopingIsomorphism.Deformation.MixedGraphTargetPowerSeries
