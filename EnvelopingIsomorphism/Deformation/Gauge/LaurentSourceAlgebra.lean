import EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceComplex
import EnvelopingIsomorphism.Deformation.Gauge.ReflectionAlgebra
import EnvelopingIsomorphism.FormalSeries.PolynomialCochainCoordinates

/-! All generated source coordinate changes preserve ordinary multiplication.
Their actual Laurent coefficient representation is transported to the native
Laurent algebra for the terminal reflected algebra equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceAlgebra
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open PolynomialCochainCoordinates.Transport
open scoped LaurentAlgebra

section SeriesTransport
universe u v
variable {k : Type u} [CommRing k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem seriesEquiv_operator (e : V ≃ₗ[k] W) (F : PowerSeries (Module.End k V))
    (p : PowerSeriesModule k V) :
    seriesEquiv e (operator F p) =
      operator (PowerSeries.map e.conjRingEquiv.toRingHom F) (seriesEquiv e p) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeff_seriesEquiv, operator_apply, coeffV_actV, map_sum, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro ij hij
  change e ((PowerSeries.coeff ij.1 F) (coeffV ij.2 p)) =
    e ((PowerSeries.coeff ij.1 F) (e.symm (e (coeffV ij.2 p))))
  rw [LinearEquiv.symm_apply_apply]

theorem seriesEquiv_extendBinary (e : V ≃ₗ[k] W) (B : PowerSeriesModule k (Binary k V))
    (p q : PowerSeriesModule k V) :
    seriesEquiv e (extendBinary B p q) =
      extendBinary (PowerSeriesModule.map (binaryEquiv e).toLinearMap B)
        (seriesEquiv e p) (seriesEquiv e q) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeff_seriesEquiv, coeffV_extendBinary, map_sum, coeffV_map,
    LinearEquiv.coe_coe, binaryEquiv_apply, LinearEquiv.symm_apply_apply]

end SeriesTransport

open LaurentSchouten
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
local instance : CharZero (Scalars K) := scalarCharZero

abbrev NativeFunctions (K : Type*) [Field K] (d : ℕ) := LaurentSeries (PolynomialFunctions K d)

abbrev nativeEquiv : Functions K d ≃ₗ[Scalars K] NativeFunctions K d :=
  LaurentAlgebra.moduleEquiv

abbrev nativeSeriesEquiv : PowerSeriesModule (Scalars K) (Functions K d) ≃ₗ[PowerSeries (Scalars K)]
    PowerSeriesModule (Scalars K) (NativeFunctions K d) := seriesEquiv nativeEquiv

/-- The original coefficient operator ring acts on the actual Laurent algebra. -/
def nativeRepresentation : LaurentSeries (Module.End K (PolynomialFunctions K d)) →+*
    Module.End (Scalars K) (NativeFunctions K d) :=
  nativeEquiv.conjRingEquiv.toRingHom.comp LaurentOperator.actionHom

/-- The actual evaluated bivector, conjugated through the native Laurent algebra bridge. -/
def nativeBivector : Bivector K d →ₗ[Scalars K] Binary (Scalars K) (NativeFunctions K d) :=
  (binaryEquiv nativeEquiv).toLinearMap.comp evaluateBivector

omit [CharZero K] in
@[simp] theorem nativeBivector_apply (π : Bivector K d) (p q : NativeFunctions K d) :
    nativeBivector π p q = nativeEquiv (evaluateBivector π (nativeEquiv.symm p) (nativeEquiv.symm q)) := rfl

/-- Ordinary multiplication before the native algebra bridge. -/
def ordinaryProduct : Binary (PowerSeries (Scalars K)) (PowerSeriesModule (Scalars K) (Functions K d)) :=
  extendBinary (single 0 (LaurentDerivationSeries.moduleMul (k := K) (A := PolynomialFunctions K d)))

omit [CharZero K] in
private theorem binaryEquiv_moduleMul :
    binaryEquiv (nativeEquiv (K := K) (d := d)) LaurentDerivationSeries.moduleMul =
      LinearMap.mul (Scalars K) (NativeFunctions K d) := by
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro q
  change nativeEquiv (LaurentDerivationSeries.moduleMul (nativeEquiv.symm p) (nativeEquiv.symm q)) = p*q
  rw [LaurentDerivationSeries.moduleEquiv_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

omit [CharZero K] in
theorem nativeSeriesEquiv_ordinaryProduct (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    nativeSeriesEquiv (ordinaryProduct p q) =
      extendBinary (single 0 (LinearMap.mul (Scalars K) (NativeFunctions K d)))
        (nativeSeriesEquiv p) (nativeSeriesEquiv q) := by
  rw [ordinaryProduct, seriesEquiv_extendBinary, PowerSeriesModule.map_single]
  simp only [LinearEquiv.coe_coe, binaryEquiv_moduleMul]

omit [CharZero K] in
theorem functionSeriesBridge_ordinaryProduct (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    functionSeriesBridge (ordinaryProduct p q) = functionSeriesBridge p * functionSeriesBridge q := by
  change PowerSeriesModuleBridge.moduleEquiv (nativeSeriesEquiv (ordinaryProduct p q)) = _
  rw [nativeSeriesEquiv_ordinaryProduct, moduleEquiv_ordinary_mul]
  rfl

/-- Each actual coordinate generator preserves the ordinary product, because
its represented operator is the proved derivation-exponential automorphism. -/
theorem coordinateGauge_preserves_mul (N : ℕ) (hN : 0 < N) (X : LaurentSchouten.Vector K d)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    operator (PowerSeries.map LaurentOperator.actionHom (coordinateGauge N hN X).series)
        (ordinaryProduct p q) =
      ordinaryProduct
        (operator (PowerSeries.map LaurentOperator.actionHom (coordinateGauge N hN X).series) p)
        (operator (PowerSeries.map LaurentOperator.actionHom (coordinateGauge N hN X).series) q) := by
  apply functionSeriesBridge_injective
  rw [coordinateGauge_matches_automorphism, functionSeriesBridge_ordinaryProduct, map_mul,
    functionSeriesBridge_ordinaryProduct, coordinateGauge_matches_automorphism,
    coordinateGauge_matches_automorphism]

/-- Ordinary multiplication is preserved for all positive and negative letters
and hence for every genuine source group word. -/
theorem source_preserves_mul (s : SourceGroup K d)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    operator (PowerSeries.map LaurentOperator.actionHom (sourceOperators s).series)
        (ordinaryProduct p q) =
      ordinaryProduct
        (operator (PowerSeries.map LaurentOperator.actionHom (sourceOperators s).series) p)
        (operator (PowerSeries.map LaurentOperator.actionHom (sourceOperators s).series) q) :=
  generatedGauge_intertwines (k := Scalars K) (V := Functions K d)
    LaurentOperator.actionHom (mcCoordinateUnit (K := K) (d := d))
    (fun _ ↦ Equiv.refl Unit) (fun _ ↦ ordinaryProduct)
    (fun γ _ a b ↦ coordinateGauge_preserves_mul γ.order γ.positive γ.direction a b)
    s Unit.unit p q

omit [CharZero K] in
/-- Conjugating the coefficient representation commutes with its full formal action. -/
theorem nativeSeriesEquiv_operator
    (F : PowerSeries (LaurentSeries (Module.End K (PolynomialFunctions K d))))
    (p : PowerSeriesModule (Scalars K) (Functions K d)) :
    nativeSeriesEquiv (operator (PowerSeries.map LaurentOperator.actionHom F) p) =
      operator (PowerSeries.map nativeRepresentation F) (nativeSeriesEquiv p) := by
  rw [seriesEquiv_operator]
  rfl

/-- Exact product-preservation hypothesis required by `reflectedAlgEquiv`,
proved for the actual native coefficient representation and every source word. -/
theorem native_source_preserves_mul (s : SourceGroup K d)
    (p q : PowerSeriesModule (Scalars K) (NativeFunctions K d)) :
    operator (PowerSeries.map nativeRepresentation (sourceOperators s).series)
        (extendBinary (single 0 (LinearMap.mul (Scalars K) (NativeFunctions K d))) p q) =
      extendBinary (single 0 (LinearMap.mul (Scalars K) (NativeFunctions K d)))
        (operator (PowerSeries.map nativeRepresentation (sourceOperators s).series) p)
        (operator (PowerSeries.map nativeRepresentation (sourceOperators s).series) q) := by
  obtain ⟨p,rfl⟩ := (nativeSeriesEquiv (K := K) (d := d)).surjective p
  obtain ⟨q,rfl⟩ := (nativeSeriesEquiv (K := K) (d := d)).surjective q
  rw [← nativeSeriesEquiv_ordinaryProduct, ← nativeSeriesEquiv_operator, source_preserves_mul,
    nativeSeriesEquiv_ordinaryProduct, nativeSeriesEquiv_operator, nativeSeriesEquiv_operator]

omit [CharZero K] in
theorem nativeBivector_moduleEquiv (π : Bivector K d) (p q : Functions K d) :
    nativeEquiv (evaluateBivector π p q) = nativeBivector π (nativeEquiv p) (nativeEquiv q) := by
  rw [nativeBivector_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

omit [CharZero K] in
theorem functionSeriesBridge_eq_nativeSeriesEquiv (p : PowerSeriesModule (Scalars K) (Functions K d)) :
    functionSeriesBridge p = PowerSeriesModuleBridge.moduleEquiv (nativeSeriesEquiv p) := rfl

section Poisson
variable (π : Bivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
local instance : MulAction (SourceGroup K d) (SourceMC π hπ) := sourceMulAction π hπ

/-- The source bracket on the actual native Laurent coefficient algebra. -/
def nativeSourceBinary (b : SourceMC π hπ) :
    Binary (PowerSeries (Scalars K)) (PowerSeriesModule (Scalars K) (NativeFunctions K d)) :=
  extendBinary (single 0 (nativeBivector π) + PowerSeriesModule.map nativeBivector b.val)

theorem nativeSeriesEquiv_sourceBinary (b : SourceMC π hπ)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    nativeSeriesEquiv (sourceBinary π hπ b p q) =
      nativeSourceBinary π hπ b (nativeSeriesEquiv p) (nativeSeriesEquiv q) := by
  have hB : PowerSeriesModule.map (binaryEquiv (nativeEquiv (K := K) (d := d))).toLinearMap
      (single 0 (evaluateBivector π) + PowerSeriesModule.map evaluateBivector b.val) =
      single 0 (nativeBivector π) + PowerSeriesModule.map nativeBivector b.val := by
    apply PowerSeriesModule.ext
    intro n
    simp only [coeffV_map, coeffV_add, map_add, coeffV_single]
    by_cases hn : n = 0
    · simp only [hn, ite_true]
      rfl
    · simp only [hn, ite_false, map_zero, zero_add]
      rfl
  rw [sourceBinary, seriesEquiv_extendBinary, hB]
  rfl

theorem functionSeriesBridge_sourceBinary (b : SourceMC π hπ)
    (p q : PowerSeriesModule (Scalars K) (Functions K d)) :
    functionSeriesBridge (sourceBinary π hπ b p q) =
      PowerSeriesModuleBridge.binaryBridge
        (single 0 (nativeBivector π) + PowerSeriesModule.map nativeBivector b.val)
        (functionSeriesBridge p) (functionSeriesBridge q) := by
  rw [functionSeriesBridge_eq_nativeSeriesEquiv, nativeSeriesEquiv_sourceBinary]
  change PowerSeriesModuleBridge.moduleEquiv (k := Scalars K) (A := NativeFunctions K d)
    (extendBinary (single 0 (nativeBivector π) + PowerSeriesModule.map nativeBivector b.val)
      (nativeSeriesEquiv p) (nativeSeriesEquiv q)) = _
  rw [PowerSeriesModuleBridge.moduleEquiv_extendBinary]
  rfl

/-- Exact all-word Poisson intertwining needed by the reflected algebra
construction, with the actual native bivector inclusion. -/
theorem native_source_intertwines (s : SourceGroup K d) (b : SourceMC π hπ)
    (p q : PowerSeriesModule (Scalars K) (NativeFunctions K d)) :
    operator (PowerSeries.map nativeRepresentation (sourceOperators s).series)
        (nativeSourceBinary π hπ b p q) =
      nativeSourceBinary π hπ (s • b)
        (operator (PowerSeries.map nativeRepresentation (sourceOperators s).series) p)
        (operator (PowerSeries.map nativeRepresentation (sourceOperators s).series) q) := by
  obtain ⟨p,rfl⟩ := (nativeSeriesEquiv (K := K) (d := d)).surjective p
  obtain ⟨q,rfl⟩ := (nativeSeriesEquiv (K := K) (d := d)).surjective q
  rw [← nativeSeriesEquiv_sourceBinary, ← nativeSeriesEquiv_operator, source_intertwines,
    nativeSeriesEquiv_sourceBinary, nativeSeriesEquiv_operator, nativeSeriesEquiv_operator]

end Poisson
end EnvelopingIsomorphism.Deformation.Gauge.LaurentSourceAlgebra
