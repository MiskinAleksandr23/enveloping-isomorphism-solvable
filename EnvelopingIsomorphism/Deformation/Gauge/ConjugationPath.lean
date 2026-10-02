import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPathOperations
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationAction
import EnvelopingIsomorphism.Deformation.NilpotentConjugation
import EnvelopingIsomorphism.FormalSeries.PolynomialModuleRingBridge

/-! Actual polynomial-module-valued conjugation paths obtained from the
path-ordered exponential, including their transport differential equation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

def outputActionLinear : Module.End k V →ₗ[k] Module.End k (Binary k V) where
  toFun := NilpotentConjugation.output
  map_add' X Y := by ext μ a b; simp
  map_smul' c X := by ext μ a b; simp

def leftActionLinear : Module.End k V →ₗ[k] Module.End k (Binary k V) where
  toFun := NilpotentConjugation.inputLeft
  map_add' X Y := by ext μ a b; simp
  map_smul' c X := by ext μ a b; simp

def rightActionLinear : Module.End k V →ₗ[k] Module.End k (Binary k V) where
  toFun := NilpotentConjugation.inputRight
  map_add' X Y := by ext μ a b; simp
  map_smul' c X := by ext μ a b; simp

def unaryActionLinear : Module.End k V →ₗ[k] Module.End k (Binary k V) where
  toFun := NilpotentConjugation.unaryActionEnd
  map_add' X Y := by
    ext B a b
    simp only [NilpotentConjugation.unaryActionEnd_apply, unaryAction_apply,
      LinearMap.add_apply, map_add]
    abel
  map_smul' c X := by
    ext B a b
    simp only [NilpotentConjugation.unaryActionEnd_apply, unaryAction_apply,
      LinearMap.smul_apply, map_smul, smul_sub, RingHom.id_apply]

@[simp] theorem outputActionLinear_apply (X : Module.End k V) (B : Binary k V) (a b : V) :
    outputActionLinear X B a b = X (B a b) := rfl

@[simp] theorem leftActionLinear_apply (X : Module.End k V) (B : Binary k V) (a b : V) :
    leftActionLinear X B a b = B (X a) b := rfl

@[simp] theorem rightActionLinear_apply (X : Module.End k V) (B : Binary k V) (a b : V) :
    rightActionLinear X B a b = B a (X b) := rfl

@[simp] theorem unaryActionLinear_apply (X : Module.End k V) (B : Binary k V) :
    unaryActionLinear X B = unaryAction X B := rfl

abbrev pathMultiply := pathBilinear (LinearMap.mul k (Module.End k V))
abbrev pathPost := pathBilinear (outputActionLinear (k := k) (V := V))
abbrev pathLeft := pathBilinear (leftActionLinear (k := k) (V := V))
abbrev pathRight := pathBilinear (rightActionLinear (k := k) (V := V))

theorem pathPost_mul (G H : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathPost (pathMultiply G H) B = pathPost G (pathPost H B) := by
  apply pathBilinear_assoc
  intro X Y μ
  ext a b
  rfl

theorem pathLeft_mul (H X : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathLeft (pathMultiply H X) B = pathLeft X (pathLeft H B) := by
  rw [pathBilinear_flip (LinearMap.mul k (Module.End k V)) H X]
  apply pathBilinear_assoc
  intro X H μ
  ext a b
  rfl

theorem pathRight_mul (H X : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathRight (pathMultiply H X) B = pathRight X (pathRight H B) := by
  rw [pathBilinear_flip (LinearMap.mul k (Module.End k V)) H X]
  apply pathBilinear_assoc
  intro X H μ
  ext a b
  rfl

theorem pathPost_left_commute (G X : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathPost G (pathLeft X B) = pathLeft X (pathPost G B) := by
  apply pathBilinear_commute
  intro G X μ
  ext a b
  rfl

theorem pathPost_right_commute (G X : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathPost G (pathRight X B) = pathRight X (pathPost G B) := by
  apply pathBilinear_commute
  intro G X μ
  ext a b
  rfl

theorem pathRight_left_commute (H X : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    pathRight H (pathLeft X B) = pathLeft X (pathRight H B) := by
  apply pathBilinear_commute
  intro H X μ
  ext a b
  rfl

/-- A path of unary endomorphisms induces its actual Hochschild action path. -/
def unaryVelocityPath (X : ModulePath k (Module.End k V)) : ModulePath k (Module.End k (Binary k V)) :=
  pathMap unaryActionLinear X

theorem unaryVelocityPath_decompose (X : ModulePath k (Module.End k V)) :
    unaryVelocityPath X = pathMap outputActionLinear X - pathMap leftActionLinear X -
      pathMap rightActionLinear X := by
  apply PowerSeriesModule.ext
  intro n
  apply PolynomialModule.ext
  ext i B a b
  simp [unaryVelocityPath, pathMap, PolynomialModule.map, unaryActionLinear,
    NilpotentConjugation.unaryActionEnd_apply, unaryAction_apply]
  rfl

theorem pathOperator_unaryVelocity (X : ModulePath k (Module.End k V))
    (B : ModulePath k (Binary k V)) :
    pathOperator (unaryVelocityPath X) B = pathPost X B - pathLeft X B - pathRight X B := by
  rw [unaryVelocityPath_decompose]
  rw [pathOperator_sub, pathOperator_sub, pathOperator_pathMap, pathOperator_pathMap,
    pathOperator_pathMap]

def transportWithPaths (G H : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V)) :
    ModulePath k (Binary k V) := pathPost G (pathRight H (pathLeft H B))

set_option maxHeartbeats 1000000 in
/-- Pure transport calculus for paths satisfying the forward and inverse
operator equations. The resulting Hochschild ODE is proved, not assumed. -/
theorem transportWithPaths_derivative
    (X G H : ModulePath k (Module.End k V)) (B : ModulePath k (Binary k V))
    (hG : PolynomialModuleCalculus.seriesDerivative G = pathMultiply X G)
    (hH : PolynomialModuleCalculus.seriesDerivative H = -pathMultiply H X)
    (hB : PolynomialModuleCalculus.seriesDerivative B = 0) :
    PolynomialModuleCalculus.seriesDerivative (transportWithPaths G H B) =
      pathOperator (unaryVelocityPath X) (transportWithPaths G H B) := by
  rw [pathOperator_unaryVelocity]
  unfold transportWithPaths
  rw [pathBilinear_derivative, pathBilinear_derivative, pathBilinear_derivative, hG, hH, hB]
  simp only [map_zero, add_zero, map_neg, LinearMap.neg_apply,
    map_add, pathPost_mul, pathLeft_mul, pathRight_mul]
  rw [pathRight_left_commute H X (pathLeft H B),
    pathPost_right_commute G X (pathRight H (pathLeft H B)),
    pathPost_left_commute G X (pathRight H (pathLeft H B))]
  abel

theorem extendBilinear_outputAction (G : PowerSeriesModule k (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) :
    PowerSeriesModule.extendBilinear outputActionLinear G B = postcomposeBinary G B := by
  apply PowerSeriesModule.ext
  intro n
  ext a b
  simp [postcomposeBinary, linearCompose, PowerSeriesModule.extendBilinear_apply,
    LinearMap.llcomp_apply]

theorem extendBilinear_leftAction (H : PowerSeriesModule k (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) :
    PowerSeriesModule.extendBilinear leftActionLinear H B = linearCompose B H := by
  apply PowerSeriesModule.ext
  intro n
  ext a b
  simp only [PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear, linearCompose,
    LinearMap.sum_apply, leftActionLinear_apply, LinearMap.llcomp_apply]
  exact Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij ↦ coeffV ij.1 B ((coeffV ij.2 H) a) b)

theorem extendBilinear_rightAction (H : PowerSeriesModule k (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) :
    PowerSeriesModule.extendBilinear rightActionLinear H B = precomposeBinaryRight B H := by
  apply PowerSeriesModule.ext
  intro n
  ext a b
  simp only [PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear, precomposeBinaryRight,
    coeffV_flipBinarySeries, linearCompose, LinearMap.flip_apply, LinearMap.sum_apply,
    rightActionLinear_apply, LinearMap.llcomp_apply]
  exact Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij ↦ coeffV ij.1 B a ((coeffV ij.2 H) b))

theorem transportWithPaths_eval (G H : ModulePath k (Module.End k V))
    (B : ModulePath k (Binary k V)) (s : k) :
    PolynomialModuleCalculus.seriesEval s (transportWithPaths G H B) =
      postcomposeBinary (PolynomialModuleCalculus.seriesEval s G)
        (precomposeBinaryRight
          (linearCompose (PolynomialModuleCalculus.seriesEval s B) (PolynomialModuleCalculus.seriesEval s H))
          (PolynomialModuleCalculus.seriesEval s H)) := by
  rw [transportWithPaths, pathBilinear_eval, pathBilinear_eval, pathBilinear_eval,
    extendBilinear_outputAction, extendBilinear_rightAction, extendBilinear_leftAction]

section OrderedSolution

variable [Algebra ℚ k] [Module ℚ V]

def orderedUnitPath (X : PathOrderedExp.PathSeries (Module.End k V)) : ModulePath k (Module.End k V) :=
  PolynomialModuleRingBridge.pathEquiv (PathOrderedExp.solution X)

def orderedInversePath (X : PathOrderedExp.PathSeries (Module.End k V)) : ModulePath k (Module.End k V) :=
  PolynomialModuleRingBridge.pathEquiv (inverseOne (PathOrderedExp.solution X))

def orderedVelocity (X : PathOrderedExp.PathSeries (Module.End k V)) :
    ModulePath k (Module.End k (Binary k V)) :=
  unaryVelocityPath (PolynomialModuleRingBridge.pathEquiv X)

def transportedBinaryPath (X : PathOrderedExp.PathSeries (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) : ModulePath k (Binary k V) :=
  transportWithPaths (orderedUnitPath X) (orderedInversePath X) (constantPath B)

theorem orderedUnitPath_derivative (X : PathOrderedExp.PathSeries (Module.End k V))
    (hX : PowerSeries.constantCoeff X = 0) :
    PolynomialModuleCalculus.seriesDerivative (orderedUnitPath X) =
      pathMultiply (PolynomialModuleRingBridge.pathEquiv X) (orderedUnitPath X) := by
  rw [orderedUnitPath, ← PolynomialModuleRingBridge.pathEquiv_derivative,
    PathOrderedExp.solution_differential X hX, PolynomialModuleRingBridge.pathEquiv_mul]
  rfl

theorem orderedInversePath_derivative (X : PathOrderedExp.PathSeries (Module.End k V))
    (hX : PowerSeries.constantCoeff X = 0) :
    PolynomialModuleCalculus.seriesDerivative (orderedInversePath X) =
      -pathMultiply (orderedInversePath X) (PolynomialModuleRingBridge.pathEquiv X) := by
  rw [orderedInversePath, ← PolynomialModuleRingBridge.pathEquiv_derivative,
    PathOrderedExp.inverse_differential X hX, neg_mul, map_neg,
    PolynomialModuleRingBridge.pathEquiv_mul]
  rfl

theorem transportedBinaryPath_derivative (X : PathOrderedExp.PathSeries (Module.End k V))
    (hX : PowerSeries.constantCoeff X = 0) (B : PowerSeriesModule k (Binary k V)) :
    PolynomialModuleCalculus.seriesDerivative (transportedBinaryPath X B) =
      pathOperator (orderedVelocity X) (transportedBinaryPath X B) :=
  transportWithPaths_derivative _ _ _ _ (orderedUnitPath_derivative X hX)
    (orderedInversePath_derivative X hX) (constantPath_derivative B)

omit [Algebra ℚ k] [Module ℚ V] in
theorem orderedVelocity_positive (X : PathOrderedExp.PathSeries (Module.End k V))
    (hX : PowerSeries.constantCoeff X = 0) : coeffV 0 (orderedVelocity X) = 0 := by
  simp only [orderedVelocity, unaryVelocityPath, pathMap, coeffV_map,
    PolynomialModuleRingBridge.coeff_pathEquiv, PowerSeries.coeff_zero_eq_constantCoeff,
    hX, map_zero]

theorem orderedUnitPath_eval_zero (X : PathOrderedExp.PathSeries (Module.End k V)) :
    PolynomialModuleCalculus.seriesEval 0 (orderedUnitPath X) =
      operatorSeries (1 : PowerSeries (Module.End k V)) := by
  rw [orderedUnitPath, PolynomialModuleRingBridge.pathEquiv_eval_zero, PathOrderedExp.atZero_solution]
  rfl

theorem orderedInversePath_eval_zero (X : PathOrderedExp.PathSeries (Module.End k V)) :
    PolynomialModuleCalculus.seriesEval 0 (orderedInversePath X) =
      operatorSeries (1 : PowerSeries (Module.End k V)) := by
  have h := congrArg (PathOrderedExp.atZero (R := Module.End k V))
    (inverseOne_mul (PathOrderedExp.constantCoeff_solution X))
  have hzero : PathOrderedExp.atZero (inverseOne (PathOrderedExp.solution X)) = 1 := by
    simpa only [map_mul, PathOrderedExp.atZero_solution, map_one, mul_one] using h
  rw [orderedInversePath, PolynomialModuleRingBridge.pathEquiv_eval_zero, hzero]
  rfl

@[simp] theorem transportedBinaryPath_eval_zero (X : PathOrderedExp.PathSeries (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) :
    PolynomialModuleCalculus.seriesEval 0 (transportedBinaryPath X B) = B := by
  rw [transportedBinaryPath, transportWithPaths_eval, orderedUnitPath_eval_zero,
    orderedInversePath_eval_zero, constantPath_eval]
  change conjugateBinarySeries (1 : (PowerSeries (Module.End k V))ˣ) B = B
  exact conjugateBinarySeries_one B

/-- Evaluation at the endpoint is conjugation by the actual path-ordered
endpoint unit, with its genuine inverse on both inputs. -/
@[simp] theorem transportedBinaryPath_eval_one (X : PathOrderedExp.PathSeries (Module.End k V))
    (B : PowerSeriesModule k (Binary k V)) :
    PolynomialModuleCalculus.seriesEval 1 (transportedBinaryPath X B) =
      conjugateBinarySeries (PathOrderedExp.endpointUnit X) B := by
  rw [transportedBinaryPath, transportWithPaths_eval, orderedUnitPath, orderedInversePath,
    PolynomialModuleRingBridge.pathEquiv_eval_one, PolynomialModuleRingBridge.pathEquiv_eval_one,
    constantPath_eval]
  rfl

end OrderedSolution

end EnvelopingIsomorphism.Deformation.Gauge
