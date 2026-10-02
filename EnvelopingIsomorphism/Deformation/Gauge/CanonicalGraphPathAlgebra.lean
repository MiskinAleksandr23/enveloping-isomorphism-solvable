import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphComparison
import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenPathDerivative
import EnvelopingIsomorphism.Deformation.Gauge.TaylorDirectionalPath
import EnvelopingIsomorphism.FormalSeries.PolynomialModuleEvaluationExt

/-! The actual polynomial path equation follows from its coefficient tangent
equation. This adapter uses the genuine source ODE, actual velocity and faithful
polynomial evaluation; the mixed scalar producer is assembled separately. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphPathAlgebra
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

section Evaluation
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem seriesEval_pathMap (f : V →ₗ[R] W) (p : ModulePath R V) (s : R) :
    PolynomialModuleCalculus.seriesEval s (pathMap f p) =
      map f (PolynomialModuleCalculus.seriesEval s p) := by
  apply PowerSeriesModule.ext
  intro D
  simp only [PolynomialModuleCalculus.coeff_seriesEval, pathMap, coeffV_map]
  exact PolynomialModule.eval_map R f (coeffV D p) s

end Evaluation

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero
local instance : Infinite (LaurentSeries k) :=
  Infinite.of_injective (fun n : ℕ ↦ (n : LaurentSeries k)) Nat.cast_injective

omit [CharZero k] [Algebra ℝ k] in
theorem seriesEval_shiftedDirectionPath (N : ℕ) (y : LaurentSchouten.Vector k d)
    (s : LaurentSeries k) :
    PolynomialModuleCalculus.seriesEval s (LaurentConjugation.shiftedDirectionPath N y) =
      single N y := by
  apply PowerSeriesModule.ext
  intro D
  simp only [PolynomialModuleCalculus.coeff_seriesEval, LaurentConjugation.shiftedDirectionPath,
    coeffV_single]
  split_ifs <;> simp

omit [CharZero k] [Algebra ℝ k] in
theorem map_unaryCoefficientAction
    (U : PowerSeriesModule (LaurentSeries k) (LaurentConjugation.OperatorCoefficients
      (k := k) (A := MvPolynomial (Fin d) k)))
    (B : LaurentConjugation.Families (k := k) (A := MvPolynomial (Fin d) k)) :
    map LaurentConjugation.evaluateCoefficient
      (applyBilinear LaurentConjugation.unaryCoefficientAction U B) =
      applyBilinear ((unaryActionLinear (k := LaurentSeries k)
        (V := LaurentModule k (MvPolynomial (Fin d) k))).comp LaurentConjugation.evaluateOperator)
        U (map LaurentConjugation.evaluateCoefficient B) := by
  apply PowerSeriesModule.ext
  intro D
  simp only [coeffV_map, coeffV_applyBilinear, map_sum,
    LaurentConjugation.evaluate_unaryCoefficientAction, LinearMap.comp_apply,
    unaryActionLinear_apply]
  rfl

/-- Every evaluation of the actual source path is in the original native
source MC carrier, using the proved source path preservation theorem. -/
def sourcePathAt (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (N : ℕ) (hN : 0 < N) (y : LaurentSchouten.Vector k d)
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ) (s : LaurentSeries k) :
    LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ :=
  ⟨PolynomialModuleCalculus.seriesEval s (CanonicalGraph.sourcePath k d π₀ hπ N y b), by
    rw [PolynomialModuleCalculus.coeff_seriesEval]
    change PolynomialModule.eval s (coeffV 0 (LaurentSchouten.elementaryPath _ N y b.val)) = 0
    rw [LaurentSchouten.elementaryPath_positive _ N hN y b.val b.property.1, map_zero], by
    rw [LaurentSchouten.sourceCurvature_eq]
    exact LaurentSchouten.elementaryPath_eval_MC (CanonicalGraph.sourceBase k d π₀) hπ N hN y
      (LaurentSchouten.sourceMCEquiv _ hπ b) s⟩

omit [Algebra ℝ k] in
/-- This is the genuine source polynomial ODE after evaluating the parameter. -/
theorem sourcePath_derivative_eval (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (N : ℕ) (hN : 0 < N) (y : LaurentSchouten.Vector k d)
    (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ) (s : LaurentSeries k) :
    PolynomialModuleCalculus.seriesEval s (PolynomialModuleCalculus.seriesDerivative
      (CanonicalGraph.sourcePath k d π₀ hπ N y b)) =
      applyBilinear LaurentSchouten.action (single N y)
        (single 0 (CanonicalGraph.sourceBase k d π₀) + (sourcePathAt π₀ hπ N hN y b s).val) := by
  rw [CanonicalGraph.sourcePath, LaurentSchouten.elementaryPath_derivative _ N hN,
    pathBilinear_eval, constantPath_eval, map_add, constantPath_eval]
  rfl

/-- Algebraic path transfer with the coefficient tangent equation left explicit
for the separately proved mixed scalar producer. No integrated lift is assumed. -/
theorem pathIdentity_of_tangentEquation
    (π₀ : CanonicalGraph.BaseBivector k d)
    (hπ : (polynomialSchoutenDGLA k d).laurent.IsMaurerCartan (CanonicalGraph.sourceBase k d π₀))
    (hT : ∀ (b : LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ)
      (Y : PowerSeriesModule (LaurentSeries k) (LaurentSchouten.Vector k d)), coeffV 0 Y = 0 →
      taylorDerivativeApply (CanonicalGraph.taylor k d π₀) b.val
        (applyBilinear LaurentSchouten.action Y (single 0 (CanonicalGraph.sourceBase k d π₀) + b.val)) =
      applyBilinear LaurentConjugation.unaryCoefficientAction
        (tangentApply (CanonicalGraph.velocityTangent k d π₀) b.val Y)
        (single 0 (CanonicalGraph.targetBase k d π₀) + taylorApply (CanonicalGraph.taylor k d π₀) b.val)) :
    CanonicalGraph.PathIdentity k d π₀ hπ := by
  intro N hN y b
  change LaurentSchouten.Vector k d at y
  change LaurentSchouten.SourceMC (CanonicalGraph.sourceBase k d π₀) hπ at b
  apply PolynomialModuleCalculus.series_ext_of_eval_eq
  intro s
  rw [seriesEval_pathMap, polynomialTaylorDerivative_eval,
    sourcePath_derivative_eval π₀ hπ N hN y b s]
  refine (congrArg (map LaurentConjugation.evaluateCoefficient)
    (hT (sourcePathAt π₀ hπ N hN y b s) (single N y)
      (by simp only [coeffV_single, if_neg (Nat.ne_of_lt hN)]))).trans ?_
  rw [map_unaryCoefficientAction]
  change _ = PolynomialModuleCalculus.seriesEval s (pathOperator
    (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom
      (LaurentConjugation.rawPathEquiv (polynomialTangentApply (CanonicalGraph.velocityTangent k d π₀)
        (CanonicalGraph.sourcePath k d π₀ hπ N y b) (LaurentConjugation.shiftedDirectionPath N y)))))
    (pathMap LaurentConjugation.evaluateCoefficient
      (quantizedPath (CanonicalGraph.taylor k d π₀) (single 0 (CanonicalGraph.targetBase k d π₀))
        (CanonicalGraph.sourcePath k d π₀ hπ N y b))))
  rw [LaurentConjugation.orderedVelocity_rawPathEquiv_comp, pathOperator_pathMap,
    pathBilinear_eval, polynomialTangentApply_eval, seriesEval_shiftedDirectionPath,
    seriesEval_pathMap, quantizedPath_eval]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphPathAlgebra
