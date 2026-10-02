import EnvelopingIsomorphism.Deformation.Gauge.BoundaryStabilizer
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPath
import EnvelopingIsomorphism.Deformation.Gauge.PathOrderedLeading

/-! Actual boundary stabilizers on arbitrary coefficient modules, obtained by
uniqueness of the polynomial-path transport equation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

theorem pathBilinear_constantPath {A C D : Type*}
    [AddCommGroup A] [Module k A] [AddCommGroup C] [Module k C]
    [AddCommGroup D] [Module k D] (f : A →ₗ[k] C →ₗ[k] D)
    (a : PowerSeriesModule k A) (c : PowerSeriesModule k C) :
    pathBilinear f (constantPath a) (constantPath c) =
      constantPath (extendBilinear f a c) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathBilinear, extendBilinear_apply, coeffV_applyBilinear,
    constantPath, coeffV_map, map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  exact PolynomialModuleCalculus.extendBilinear_single_single f 0 0 _ _

/-- A constant-in-s path of formal endomorphisms. -/
def constantOperatorPath (F : PowerSeries (Module.End k V)) :
    PathOrderedExp.PathSeries (Module.End k V) := PowerSeries.map Polynomial.C F

@[simp] theorem coeff_constantOperatorPath (F : PowerSeries (Module.End k V)) (n : ℕ) :
    PowerSeries.coeff n (constantOperatorPath F) = Polynomial.C (PowerSeries.coeff n F) := rfl

theorem pathEquiv_constantOperatorPath (F : PowerSeries (Module.End k V)) :
    PolynomialModuleRingBridge.pathEquiv (k := k) (constantOperatorPath F) =
      constantPath (operatorSeries F) := by
  apply PowerSeriesModule.ext
  intro n
  rfl

theorem derivation_series_identity (F : PowerSeries (Module.End k V))
    (B : PowerSeriesModule k (Binary k V))
    (hF : ∀ x y, actV F (extendBinary B x y) =
      extendBinary B (actV F x) y + extendBinary B x (actV F y)) :
    postcomposeBinary (operatorSeries F) B - linearCompose B (operatorSeries F) -
      precomposeBinaryRight B (operatorSeries F) = 0 := by
  apply extendBinary_injective
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [extendBinary_apply, map_sub, LinearMap.sub_apply, map_zero, LinearMap.zero_apply]
  change extendBinary (postcomposeBinary (operatorSeries F) B) x y -
    extendBinary (linearCompose B (operatorSeries F)) x y -
    extendBinary (precomposeBinaryRight B (operatorSeries F)) x y = 0
  rw [extendBinary_postcomp, extendBinary_precomp_left, extendBinary_precomp_right]
  have h := hF x y
  simp only [actV_eq_linearApply] at h
  change linearApply (operatorSeries F) (extendBinary B x y) =
    extendBinary B (linearApply (operatorSeries F) x) y +
      extendBinary B x (linearApply (operatorSeries F) y) at h
  rw [h]
  abel

theorem constantPath_solves_inner_ode (F : PowerSeries (Module.End k V))
    (B : PowerSeriesModule k (Binary k V))
    (hF : ∀ x y, actV F (extendBinary B x y) =
      extendBinary B (actV F x) y + extendBinary B x (actV F y)) :
    PolynomialModuleCalculus.seriesDerivative (constantPath B) =
      pathOperator (orderedVelocity (constantOperatorPath F)) (constantPath B) := by
  rw [constantPath_derivative, orderedVelocity, pathEquiv_constantOperatorPath,
    pathOperator_unaryVelocity]
  simp only [pathPost, pathLeft, pathRight, pathBilinear_constantPath,
    extendBilinear_outputAction, extendBilinear_leftAction, extendBilinear_rightAction]
  unfold constantPath
  rw [← map_sub, ← map_sub]
  rw [derivation_series_identity F B hF, map_zero]

/-- The boundary velocity is constant in the path parameter and contains all
coefficients of the deformed multiplication. -/
def boundaryPath (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PathOrderedExp.PathSeries (Module.End k V) := constantOperatorPath (boundaryVelocity N B u)

theorem boundaryPath_coeff_below (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V)
    (i : ℕ) (hi : i < N) : PowerSeries.coeff i (boundaryPath N B u) = 0 := by
  simp [boundaryPath, boundaryVelocity_coeff_below N B u i hi]

@[simp] theorem boundaryPath_leading (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeries.coeff N (boundaryPath N B u) = Polynomial.C (differentialZero (coeffV 0 B) u) := by
  simp [boundaryPath]

theorem boundaryPath_positive {N : ℕ} (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeries.constantCoeff (boundaryPath N B u) = 0 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using boundaryPath_coeff_below N B u 0 hN

variable [Algebra ℚ k] [Module ℚ V]

def boundaryPathGauge (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    GaugeUnit (Module.End k V) := orderedGauge (boundaryPath N B u)

theorem boundaryPathGauge_near (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    NearIdentity N (boundaryPathGauge N B u).series :=
  orderedGauge_near _ N (boundaryPath_coeff_below N B u)

@[simp] theorem boundaryPathGauge_leading (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeries.coeff N (boundaryPathGauge N B u).series = differentialZero (coeffV 0 B) u :=
  orderedGauge_leading _ N hN (boundaryPath_coeff_below N B u) _ (boundaryPath_leading N B u)

/-- Exact stabilization follows from the actual ODE, for arbitrary modules V. -/
theorem boundaryPathGauge_fixes (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k V)) (u : V)
    (hB : ∀ x y z, extendBinary B (extendBinary B x y) z = extendBinary B x (extendBinary B y z)) :
    conjugateBinarySeries (boundaryPathGauge N B u).val B = B := by
  have hX := boundaryPath_positive hN B u
  have heq := path_unique (orderedVelocity_positive _ hX)
    (transportedBinaryPath_derivative (boundaryPath N B u) hX B)
    (constantPath_solves_inner_ode (boundaryVelocity N B u) B (boundaryVelocity_derivation N B u hB))
    (by simp : PolynomialModuleCalculus.seriesEval 0 (transportedBinaryPath (boundaryPath N B u) B) =
      PolynomialModuleCalculus.seriesEval 0 (constantPath B))
  have h := congrArg (PolynomialModuleCalculus.seriesEval (1 : k)) heq
  simpa only [transportedBinaryPath_eval_one, constantPath_eval,
    boundaryPathGauge, orderedGauge] using h

end EnvelopingIsomorphism.Deformation.Gauge
