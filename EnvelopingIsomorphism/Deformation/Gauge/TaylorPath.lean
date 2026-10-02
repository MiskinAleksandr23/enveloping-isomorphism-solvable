import EnvelopingIsomorphism.Deformation.Gauge.Taylor
import EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus

/-! Actual Taylor evaluation and differentiation on complete polynomial-coefficient paths. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

abbrev ModulePath (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V] :=
  PowerSeriesModule k (PolynomialModule k V)

def polynomialTaylorFamily (T : TaylorFamily (k := k) (V := V) (W := W)) :
    TaylorFamily (k := k) (V := PolynomialModule k V) (W := PolynomialModule k W) :=
  fun n => PolynomialModuleCalculus.extendMultilinear (T n)

def polynomialTaylorApply (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : ModulePath k V) : ModulePath k W := taylorApply (polynomialTaylorFamily T) b

/-- The full formal map commutes with genuine evaluation of the path parameter. -/
theorem polynomialTaylor_eval (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : ModulePath k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (polynomialTaylorApply T b) =
      taylorApply T (PolynomialModuleCalculus.seriesEval s b) := by
  apply PowerSeriesModule.ext
  intro d
  rw [PolynomialModuleCalculus.coeff_seriesEval]
  change PolynomialModule.eval s (coeffV d (taylorApply (polynomialTaylorFamily T) b)) = _
  rw [coeffV_taylorApply, coeffV_taylorApply, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he := congrArg (coeffV d)
    (PolynomialModuleCalculus.seriesEval_extendMultilinear (T n) (fun _ => b) s)
  simpa only [PolynomialModuleCalculus.coeff_seriesEval, extendMultilinear_apply,
    polynomialTaylorFamily] using he

/-- Replace one argument with the actual derivative of the polynomial path. -/
def pathVelocityInputs {n : ℕ} (b : ModulePath k V) (i : Fin (n + 1)) :
    Fin (n + 1) → ModulePath k V :=
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  Function.update (fun _ => b) i (PolynomialModuleCalculus.seriesDerivative b)

def polynomialTaylorDerivative (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : ModulePath k V) : ModulePath k W :=
  mk fun d => ∑ n ∈ Finset.range d, ∑ i : Fin (n + 1),
    coeffV d (extendMultilinear (PolynomialModuleCalculus.extendMultilinear (T n))
      (pathVelocityInputs b i))

/-- The complete Taylor chain rule, with finite sums at each formal degree. -/
theorem polynomialTaylor_derivative (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : ModulePath k V) :
    PolynomialModuleCalculus.seriesDerivative (polynomialTaylorApply T b) =
      polynomialTaylorDerivative T b := by
  apply PowerSeriesModule.ext
  intro d
  rw [PolynomialModuleCalculus.coeff_seriesDerivative]
  change PolynomialModuleCalculus.derivative (coeffV d (taylorApply (polynomialTaylorFamily T) b)) = _
  rw [coeffV_taylorApply, map_sum]
  change (∑ n ∈ Finset.range d,
    PolynomialModuleCalculus.derivative (coeffV d (applyMultilinear (polynomialTaylorFamily T n) (fun _ => b)))) = _
  rw [polynomialTaylorDerivative, coeffV_mk]
  apply Finset.sum_congr rfl
  intro n _
  have hd := congrArg (coeffV d)
    (PolynomialModuleCalculus.seriesDerivative_extendMultilinear (T n) (fun _ => b))
  simpa only [PolynomialModuleCalculus.coeff_seriesDerivative, coeffV_sum,
    extendMultilinear_apply, polynomialTaylorFamily, pathVelocityInputs] using hd

end EnvelopingIsomorphism.Deformation.Gauge
