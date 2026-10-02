import EnvelopingIsomorphism.Deformation.Gauge.LaurentBoundary
import EnvelopingIsomorphism.Deformation.Gauge.ForwardPathEmbedding

/-! A real differential Taylor identity integrates to a gauge lift inside the
Laurent full-cochain completion. The constructed unit has coefficients in the
original Laurent endomorphism ring; only its action is mapped to ambient operators. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u v w
variable {k : Type u} [CommRing k] [Algebra ℚ k]
variable {A : Type v} [AddCommGroup A] [Module k A] [Module ℚ A]
variable {V : Type w} [AddCommGroup V] [Module (Scalars (k := k)) V]

theorem ambientGauge_orderedGauge (X : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A))) :
    ambientGauge (orderedGauge X) = orderedGauge (PathOrderedExp.mapPath LaurentOperator.actionHom X) := by
  apply Subtype.ext
  exact (PathOrderedExp.endpointUnit_mapPath LaurentOperator.actionHom X).symm

/-- Closure and faithful evaluation turn the actual ambient path ODE into a
coefficient identity without enlarging the Laurent full-cochain carrier. -/
theorem rawOrderedGauge_lifts_path
    (T : TaylorFamily (k := Scalars (k := k)) (V := V) (W := BinaryCoefficients (k := k) (A := A)))
    (base : Families (k := k) (A := A)) (b : ModulePath (Scalars (k := k)) V)
    (start finish : PowerSeriesModule (Scalars (k := k)) V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (X : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A)))
    (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : pathMap evaluateCoefficient (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom X))
        (pathMap evaluateCoefficient (quantizedPath T base b))) :
    conjugateFamily (orderedGauge X).val (base + taylorApply T start) = base + taylorApply T finish := by
  apply embed_injective
  rw [embed_conjugateFamily]
  change conjugateBinarySeries (ambientGauge (orderedGauge X)).val (embed (base + taylorApply T start)) =
    embed (base + taylorApply T finish)
  rw [ambientGauge_orderedGauge]
  have hX' : PowerSeries.constantCoeff (PathOrderedExp.mapPath
      (LaurentOperator.actionHom (k := k) (X := A)) X) = 0 := by
    simp only [PathOrderedExp.constantCoeff_mapPath, hX, Polynomial.map_zero]
  exact orderedGauge_lifts_embedded_path (k := Scalars (k := k)) (V := V)
    (W := BinaryCoefficients (k := k) (A := A)) (A := Functions (k := k) (A := A))
    evaluateCoefficient T base b start finish hb0 hb1
    (PathOrderedExp.mapPath (LaurentOperator.actionHom (k := k) (X := A)) X) hX' hProducer

/-- The same actual constructed gauge transports coefficient MC elements. -/
theorem rawOrderedGauge_lifts_mcPath (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (T : TaylorFamily (k := Scalars (k := k)) (V := V) (W := BinaryCoefficients (k := k) (A := A)))
    (b : ModulePath (Scalars (k := k)) V)
    (start finish : PowerSeriesModule (Scalars (k := k)) V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (initial final : MC μ) (hi : initial.val = taylorApply T start) (hf : final.val = taylorApply T finish)
    (X : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A)))
    (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : pathMap evaluateCoefficient (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom X))
        (pathMap evaluateCoefficient (quantizedPath T (single 0 μ) b))) :
    transport μ hμ (orderedGauge X) initial = final := by
  apply Subtype.ext
  rw [transport_val, transportFamily, hi,
    rawOrderedGauge_lifts_path T (single 0 μ) b start finish hb0 hb1 X hX hProducer, hf]
  abel

/-- Forward lifting carries the exact raw Laurent leading coefficient used in reflection. -/
theorem rawOrderedGauge_lift_spec (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (T : TaylorFamily (k := Scalars (k := k)) (V := V) (W := BinaryCoefficients (k := k) (A := A)))
    (b : ModulePath (Scalars (k := k)) V)
    (start finish : PowerSeriesModule (Scalars (k := k)) V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (initial final : MC μ) (hi : initial.val = taylorApply T start) (hf : final.val = taylorApply T finish)
    (X : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A))) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i < N, PowerSeries.coeff i X = 0) (x : OperatorCoefficients (k := k) (A := A))
    (hx : PowerSeries.coeff N X = Polynomial.C (operatorCoordinates.symm x))
    (hProducer : pathMap evaluateCoefficient (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom X))
        (pathMap evaluateCoefficient (quantizedPath T (single 0 μ) b))) :
    NearIdentity N (orderedGauge X).series ∧
      operatorCoordinates (PowerSeries.coeff N (orderedGauge X).series) = x ∧
        transport μ hμ (orderedGauge X) initial = final := by
  refine ⟨orderedGauge_near X N hX, ?_, ?_⟩
  · rw [orderedGauge_leading X N hN hX _ hx, AddEquiv.apply_symm_apply]
  · exact rawOrderedGauge_lifts_mcPath μ hμ T b start finish hb0 hb1 initial final hi hf X
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hX 0 hN) hProducer

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
