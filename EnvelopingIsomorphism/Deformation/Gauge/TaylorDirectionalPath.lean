import EnvelopingIsomorphism.Deformation.Gauge.TaylorPath

/-! The actual slot derivative of Taylor evaluation and its exact polynomial
path evaluation. This is a chain-rule adapter, with no graph identity assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open scoped BigOperators Classical

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The ordered Taylor directional derivative keeps every varying slot,
without assuming symmetry or replacing its sum by an arity factor. -/
def taylorDerivativeApply (T : TaylorFamily (k := k) (V := V) (W := W))
    (β δ : PowerSeriesModule k V) : PowerSeriesModule k W :=
  mk fun D ↦ ∑ n ∈ Finset.range D, ∑ i : Fin (n + 1),
    coeffV D (applyMultilinear (T n) (Function.update (fun _ ↦ β) i δ))

@[simp] theorem coeff_taylorDerivativeApply
    (T : TaylorFamily (k := k) (V := V) (W := W))
    (β δ : PowerSeriesModule k V) (D : ℕ) :
    coeffV D (taylorDerivativeApply T β δ) =
      ∑ n ∈ Finset.range D, ∑ i : Fin (n + 1),
        coeffV D (applyMultilinear (T n) (Function.update (fun _ ↦ β) i δ)) := rfl

/-- Polynomial parameter evaluation preserves the genuine complete slot
derivative, with the evaluated actual path derivative as its direction. -/
theorem polynomialTaylorDerivative_eval
    (T : TaylorFamily (k := k) (V := V) (W := W)) (p : ModulePath k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (polynomialTaylorDerivative T p) =
      taylorDerivativeApply T (PolynomialModuleCalculus.seriesEval s p)
        (PolynomialModuleCalculus.seriesEval s (PolynomialModuleCalculus.seriesDerivative p)) := by
  apply PowerSeriesModule.ext
  intro D
  rw [PolynomialModuleCalculus.coeff_seriesEval, coeff_taylorDerivativeApply]
  change PolynomialModule.eval s
    (∑ n ∈ Finset.range D, ∑ i : Fin (n + 1),
      coeffV D (applyMultilinear (PolynomialModuleCalculus.extendMultilinear (T n))
        (pathVelocityInputs p i))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (coeffV D)
    (PolynomialModuleCalculus.seriesEval_extendMultilinear (T n) (pathVelocityInputs p i) s)
  simp only [PolynomialModuleCalculus.coeff_seriesEval, extendMultilinear_apply] at h
  rw [h]
  congr 2
  funext j
  by_cases hj : j = i
  · subst j
    simp [pathVelocityInputs]
  · simp [pathVelocityInputs, hj]

end EnvelopingIsomorphism.Deformation.Gauge
