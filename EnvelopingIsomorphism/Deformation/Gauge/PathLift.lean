import EnvelopingIsomorphism.Deformation.Gauge.LinearPathODE

/-!
Integrate a restricted Taylor/tangent path identity into an actual endpoint
comparison.  The input identity is differential and coefficientwise; no
endpoint gauge-lifting assertion is assumed.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def constantPath (b : PowerSeriesModule k V) : ModulePath k V :=
  map (PolynomialModule.lsingle k 0) b

@[simp] theorem constantPath_eval (b : PowerSeriesModule k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (constantPath b) = b := by
  apply PowerSeriesModule.ext
  intro n
  rw [PolynomialModuleCalculus.coeff_seriesEval]
  simp only [constantPath, coeffV_map, PolynomialModule.eval_lsingle, pow_zero, one_smul]

@[simp] theorem constantPath_derivative (b : PowerSeriesModule k V) :
    PolynomialModuleCalculus.seriesDerivative (constantPath b) = 0 := by
  apply PowerSeriesModule.ext
  intro n
  rw [PolynomialModuleCalculus.coeff_seriesDerivative, coeffV_zero]
  change PolynomialModuleCalculus.derivative (PolynomialModule.single k 0 (coeffV n b)) = 0
  exact PolynomialModuleCalculus.derivative_single_zero _

def quantizedPath (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V) : ModulePath k W :=
  constantPath base + polynomialTaylorApply T b

theorem quantizedPath_eval (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (quantizedPath T base b) =
      base + taylorApply T (PolynomialModuleCalculus.seriesEval s b) := by
  rw [quantizedPath, map_add, constantPath_eval, polynomialTaylor_eval]

theorem quantizedPath_derivative (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V) :
    PolynomialModuleCalculus.seriesDerivative (quantizedPath T base b) =
      polynomialTaylorDerivative T b := by
  rw [quantizedPath, map_add, constantPath_derivative, zero_add, polynomialTaylor_derivative]

variable [Algebra ℚ k]

/-- An actual Taylor path identity plus the actual transport ODE imply endpoint gauge lifting. -/
theorem endpoint_lift_of_path_identity
    (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V)
    (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (L : ModulePath k (Module.End k W)) (hL : coeffV 0 L = 0)
    (transported : ModulePath k W)
    (hTransport : PolynomialModuleCalculus.seriesDerivative transported = pathOperator L transported)
    (hInitial : PolynomialModuleCalculus.seriesEval 0 transported = base + taylorApply T start)
    (hProducer : polynomialTaylorDerivative T b = pathOperator L (quantizedPath T base b)) :
    PolynomialModuleCalculus.seriesEval 1 transported = base + taylorApply T finish := by
  have hQ : PolynomialModuleCalculus.seriesDerivative (quantizedPath T base b) =
      pathOperator L (quantizedPath T base b) := by
    rw [quantizedPath_derivative]
    exact hProducer
  have h0 : PolynomialModuleCalculus.seriesEval 0 transported =
      PolynomialModuleCalculus.seriesEval 0 (quantizedPath T base b) := by
    rw [quantizedPath_eval, hb0]
    exact hInitial
  have heq := path_unique hL hTransport hQ h0
  rw [heq, quantizedPath_eval, hb1]

end EnvelopingIsomorphism.Deformation.Gauge
