import EnvelopingIsomorphism.Deformation.Gauge.ForwardPathLift
import EnvelopingIsomorphism.Deformation.Gauge.TaylorNaturality
import EnvelopingIsomorphism.Deformation.Gauge.AssociativeEmbedding

/-! The forward path lift can be checked on actual operators and reflected
through a faithful completed-cochain embedding. No ambient cochain is silently
identified with a bounded Laurent cochain. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V W A : Type*} [CommRing k] [Algebra ℚ k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup A] [Module k A] [Module ℚ A]

theorem orderedGauge_lifts_embedded_path
    (ι : W →ₗ[k] Binary k A) (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V)
    (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (X : PathOrderedExp.PathSeries (Module.End k A)) (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : pathMap ι (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity X) (pathMap ι (quantizedPath T base b))) :
    conjugateBinarySeries (orderedGauge X).val (map ι (base + taylorApply T start)) =
      map ι (base + taylorApply T finish) := by
  rw [pathMap_polynomialTaylorDerivative, pathMap_quantizedPath] at hProducer
  simpa only [map_add, map_taylorApply] using
    orderedGauge_lifts_taylor_path (mapTaylorFamily ι T) (map ι base) b start finish hb0 hb1 X hX hProducer

/-- Actual closure under conjugation plus faithful evaluation gives the bounded
coefficient identity required by the reflection producer. -/
theorem orderedGauge_lifts_bounded_path
    (ι : W →ₗ[k] Binary k A) (hι : Function.Injective ι)
    (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V)
    (start finish : PowerSeriesModule k V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (X : PathOrderedExp.PathSeries (Module.End k A)) (hX : PowerSeries.constantCoeff X = 0)
    (hProducer : pathMap ι (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity X) (pathMap ι (quantizedPath T base b)))
    (transported : PowerSeriesModule k W)
    (hTransport : map ι transported =
      conjugateBinarySeries (orderedGauge X).val (map ι (base + taylorApply T start))) :
    transported = base + taylorApply T finish := by
  apply seriesMap_injective ι hι
  rw [hTransport]
  exact orderedGauge_lifts_embedded_path ι T base b start finish hb0 hb1 X hX hProducer

end EnvelopingIsomorphism.Deformation.Gauge
