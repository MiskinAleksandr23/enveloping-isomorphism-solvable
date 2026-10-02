import EnvelopingIsomorphism.Deformation.Gauge.PathLift
import EnvelopingIsomorphism.Deformation.Gauge.PathOrderedLeading
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPath
import EnvelopingIsomorphism.Deformation.Gauge.AssociativeMC

/-! The forward gauge lift is the actual path-ordered operator unit. The only
remaining formality input is a differential Taylor identity along the source
path; the target ODE, initial value, endpoint, and leading jet are all proved. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V A : Type*} [CommRing k] [Algebra ℚ k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup A] [Module k A] [Module ℚ A]

/-- Integrating the differential producer identity gives genuine binary conjugation. -/
theorem orderedGauge_lifts_taylor_path
    (T : TaylorFamily (k := k) (V := V) (W := Binary k A))
    (base : PowerSeriesModule k (Binary k A)) (b : ModulePath k V)
    (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (X : PathOrderedExp.PathSeries (Module.End k A)) (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : polynomialTaylorDerivative T b =
      pathOperator (orderedVelocity X) (quantizedPath T base b)) :
    conjugateBinarySeries (orderedGauge X).val (base + taylorApply T start) =
      base + taylorApply T finish := by
  have h := endpoint_lift_of_path_identity T base b start finish hb0 hb1
    (orderedVelocity X) (orderedVelocity_positive X hX)
    (transportedBinaryPath X (base + taylorApply T start))
    (transportedBinaryPath_derivative X hX _)
    (transportedBinaryPath_eval_zero X _) hProducer
  rw [transportedBinaryPath_eval_one] at h
  exact h

/-- The same constructed lift has the precise filtration order and tangent coefficient. -/
theorem orderedGauge_lift_spec
    (T : TaylorFamily (k := k) (V := V) (W := Binary k A))
    (base : PowerSeriesModule k (Binary k A)) (b : ModulePath k V)
    (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (X : PathOrderedExp.PathSeries (Module.End k A)) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i < N, PowerSeries.coeff i X = 0) (x : Module.End k A)
    (hx : PowerSeries.coeff N X = Polynomial.C x)
    (hProducer : polynomialTaylorDerivative T b =
      pathOperator (orderedVelocity X) (quantizedPath T base b)) :
    NearIdentity N (orderedGauge X).series ∧ PowerSeries.coeff N (orderedGauge X).series = x ∧
      conjugateBinarySeries (orderedGauge X).val (base + taylorApply T start) =
        base + taylorApply T finish := by
  refine ⟨orderedGauge_near X N hX, orderedGauge_leading X N hN hX x hx, ?_⟩
  exact orderedGauge_lifts_taylor_path T base b start finish hb0 hb1 X
    (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hX 0 hN) hProducer

/-- The actual unit lifts the forward path in coefficient MC coordinates. -/
theorem orderedGauge_lifts_MC_path
    (μ : Binary k A) (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (T : TaylorFamily (k := k) (V := V) (W := Binary k A))
    (b : ModulePath k V) (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (initial final : AssociativeMC μ)
    (hi : initial.val = taylorApply T start) (hf : final.val = taylorApply T finish)
    (X : PathOrderedExp.PathSeries (Module.End k A)) (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : polynomialTaylorDerivative T b =
      pathOperator (orderedVelocity X) (quantizedPath T (single 0 μ) b)) :
    associativeMCTransport μ hμ (orderedGauge X) initial = final := by
  apply Subtype.ext
  rw [associativeMCTransport_val, hi,
    orderedGauge_lifts_taylor_path T (single 0 μ) b start finish hb0 hb1 X hX hProducer, hf]
  abel

end EnvelopingIsomorphism.Deformation.Gauge
