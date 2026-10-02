import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPathOperations

/-! Faithful coefficient embeddings commute with genuine Taylor evaluation and
path differentiation. These formulas connect bounded Laurent cochains to their
actual operators without enlarging their coefficient space. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V W Z : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup Z] [Module k Z]

def mapTaylorFamily (f : W →ₗ[k] Z) (T : TaylorFamily (k := k) (V := V) (W := W)) :
    TaylorFamily (k := k) (V := V) (W := Z) := fun n ↦ f.compMultilinearMap (T n)

theorem map_taylorApply (f : W →ₗ[k] Z) (T : TaylorFamily (k := k) (V := V) (W := W))
    (b : PowerSeriesModule k V) : map f (taylorApply T b) = taylorApply (mapTaylorFamily f T) b := by
  apply PowerSeriesModule.ext
  intro n
  rw [coeffV_map, coeffV_taylorApply, coeffV_taylorApply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (coeffV n) (applyMultilinear_postcomp (T j) f (fun _ ↦ b))

theorem pathMap_derivative (f : W →ₗ[k] Z) (b : ModulePath k W) :
    pathMap f (PolynomialModuleCalculus.seriesDerivative b) =
      PolynomialModuleCalculus.seriesDerivative (pathMap f b) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathMap, coeffV_map, PolynomialModuleCalculus.coeff_seriesDerivative,
    PolynomialModuleCalculus.derivative_map]

theorem pathMap_polynomialTaylorApply (f : W →ₗ[k] Z)
    (T : TaylorFamily (k := k) (V := V) (W := W)) (b : ModulePath k V) :
    pathMap f (polynomialTaylorApply T b) = polynomialTaylorApply (mapTaylorFamily f T) b := by
  change map (PolynomialModule.map k f) (taylorApply (polynomialTaylorFamily T) b) = _
  rw [map_taylorApply]
  congr 1
  funext n
  apply MultilinearMap.ext
  intro p
  exact PolynomialModuleCalculus.map_extendMultilinear (T n) f p

theorem pathMap_polynomialTaylorDerivative (f : W →ₗ[k] Z)
    (T : TaylorFamily (k := k) (V := V) (W := W)) (b : ModulePath k V) :
    pathMap f (polynomialTaylorDerivative T b) = polynomialTaylorDerivative (mapTaylorFamily f T) b := by
  rw [← polynomialTaylor_derivative, pathMap_derivative,
    pathMap_polynomialTaylorApply, polynomialTaylor_derivative]

theorem pathMap_constantPath (f : W →ₗ[k] Z) (b : PowerSeriesModule k W) :
    pathMap f (constantPath b) = constantPath (map f b) := by
  apply PowerSeriesModule.ext
  intro n
  simp [pathMap, constantPath]

theorem pathMap_quantizedPath (f : W →ₗ[k] Z)
    (T : TaylorFamily (k := k) (V := V) (W := W))
    (base : PowerSeriesModule k W) (b : ModulePath k V) :
    pathMap f (quantizedPath T base b) = quantizedPath (mapTaylorFamily f T) (map f base) b := by
  rw [quantizedPath, map_add, pathMap_constantPath, pathMap_polynomialTaylorApply]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge
