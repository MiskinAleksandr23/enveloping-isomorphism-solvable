import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenElementary
import EnvelopingIsomorphism.FormalSeries.DerivationMonomial

/-! The actual Laurent source coordinate gauge is an algebra automorphism of iterated series. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule PowerSeries
open scoped LaurentAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

local instance : CharZero (Scalars K) := scalarCharZero
local instance : Module ℚ (Functions K d) := functionRationalModule
local instance : IsScalarTower ℚ (Scalars K) (Functions K d) := functionRationalTower
local instance : SMulCommClass (Scalars K) ℚ (Functions K d) := functionRationalComm
local instance actualFunctionRing : Ring (LaurentSeries (PolynomialFunctions K d)) :=
  HahnSeries.instRing
local instance actualFunctionRationalModule : Module ℚ (LaurentSeries (PolynomialFunctions K d)) :=
  (inferInstance : Algebra ℚ (LaurentSeries (PolynomialFunctions K d))).toModule
local instance : Ring (Module.End (Scalars K) (Functions K d)) :=
  @Module.End.instRing (Scalars K) (Functions K d) inferInstance inferInstance inferInstance
local instance actualEndRing : Ring (Module.End (Scalars K) (LaurentSeries (PolynomialFunctions K d))) :=
  @Module.End.instRing (Scalars K) (LaurentSeries (PolynomialFunctions K d)) inferInstance inferInstance inferInstance
local instance actualEndAlgebra : Algebra ℚ (Module.End (Scalars K) (LaurentSeries (PolynomialFunctions K d))) :=
  Module.End.instAlgebra ℚ (Scalars K) (LaurentSeries (PolynomialFunctions K d))

/-- The actual derivation on the entire Laurent function algebra. -/
def coordinateDerivation (X : Vector K d) :
    Derivation (Scalars K) (LaurentSeries (PolynomialFunctions K d)) (LaurentSeries (PolynomialFunctions K d)) :=
  LaurentDerivationSeries.toDerivation (vectorDerivations X)

omit [CharZero K] in
theorem coordinateDerivation_intertwines (X : Vector K d) (p : Functions K d) :
    LaurentAlgebra.moduleEquiv (coordinateEnd X p) =
      coordinateDerivation X (LaurentAlgebra.moduleEquiv p) := by
  change LaurentAlgebra.moduleEquiv (coordinateEnd X p) =
    (LaurentDerivationSeries.toDerivation (vectorDerivations X)).toLinearMap (LaurentAlgebra.moduleEquiv p)
  rw [LaurentDerivationSeries.toDerivation_toLinearMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    coordinateEnd_eq_actionHom, vectorOperator]

def coordinateDerivationCoefficients (N : ℕ) (X : Vector K d) (j : ℕ) :
    Derivation (Scalars K) (LaurentSeries (PolynomialFunctions K d)) (LaurentSeries (PolynomialFunctions K d)) :=
  if j = N then coordinateDerivation X else 0

omit [CharZero K] in
theorem coordinateDerivation_operators (N : ℕ) (X : Vector K d) :
    DerivationSeries.operators (coordinateDerivationCoefficients N X) = monomial N (coordinateDerivation X).toLinearMap := by
  apply PowerSeries.ext
  intro j
  rw [DerivationSeries.coeff_operators, PowerSeries.coeff_monomial]
  by_cases h : j = N <;> simp [coordinateDerivationCoefficients, h]

/-- Actual scalar-series algebra automorphism on `A((h))[[t]]`. -/
def coordinateAutomorphism (N : ℕ) (hN : 0 < N) (X : Vector K d) :
    PowerSeries (LaurentSeries (PolynomialFunctions K d)) ≃ₐ[PowerSeries (Scalars K)]
      PowerSeries (LaurentSeries (PolynomialFunctions K d)) :=
  DerivationSeries.monomialAutomorphism (k := Scalars K) (A := LaurentSeries (PolynomialFunctions K d))
    N hN (coordinateDerivation X)

theorem coordinateAutomorphism_apply (N : ℕ) (hN : 0 < N) (X : Vector K d)
    (p : PowerSeries (LaurentSeries (PolynomialFunctions K d))) :
    coordinateAutomorphism N hN X p =
      EndomorphismSeries.act (k := Scalars K) (A := LaurentSeries (PolynomialFunctions K d))
        (exp (monomial N (coordinateDerivation X).toLinearMap)) p :=
  DerivationSeries.monomialAutomorphism_apply (k := Scalars K) (A := LaurentSeries (PolynomialFunctions K d))
    N hN (coordinateDerivation X) p

/-- The established coefficient-model bridges, applied in the two series variables. -/
def functionSeriesBridge : PowerSeriesModule (Scalars K) (Functions K d) →ₗ[PowerSeries (Scalars K)]
    PowerSeries (LaurentSeries (PolynomialFunctions K d)) :=
  PowerSeriesModuleBridge.moduleEquiv.toLinearMap.comp
    (PowerSeriesModule.map (LaurentAlgebra.moduleEquiv (k := K) (A := PolynomialFunctions K d)).toLinearMap)

omit [CharZero K] in
theorem functionSeriesBridge_injective : Function.Injective (functionSeriesBridge (K := K) (d := d)) :=
  (PowerSeriesModuleBridge.moduleEquiv (k := Scalars K) (A := LaurentSeries (PolynomialFunctions K d))).injective.comp
    (seriesMap_injective (k := Scalars K) (V := Functions K d) (W := LaurentSeries (PolynomialFunctions K d))
      (LaurentAlgebra.moduleEquiv (k := K) (A := PolynomialFunctions K d)).toLinearMap
      (LaurentAlgebra.moduleEquiv (k := K) (A := PolynomialFunctions K d)).injective)

/-- The coordinate action represented by the original Laurent operator ring is exactly the
actual derivation exponential algebra automorphism. -/
theorem coordinateGauge_matches_automorphism (N : ℕ) (hN : 0 < N) (X : Vector K d)
    (p : PowerSeriesModule (Scalars K) (Functions K d)) :
    functionSeriesBridge
      (operator (PowerSeries.map LaurentOperator.actionHom (coordinateGauge N hN X).series) p) =
      coordinateAutomorphism N hN X (functionSeriesBridge p) := by
  have hu : PowerSeries.map LaurentOperator.actionHom (coordinateGauge N hN X).series =
      (ambientCoordinateGauge N hN X).series :=
    congrArg GaugeUnit.series (ambient_coordinateGauge N hN X)
  rw [hu, operator_apply]
  change PowerSeriesModuleBridge.moduleEquiv
      (PowerSeriesModule.map LaurentAlgebra.moduleEquiv.toLinearMap
        (actV (exp (monomial N (coordinateEnd X))) p)) = _
  rw [map_actV_exp_monomial LaurentAlgebra.moduleEquiv.toLinearMap (coordinateEnd X)
    (coordinateDerivation X).toLinearMap (coordinateDerivation_intertwines X),
    PowerSeriesModuleBridge.moduleEquiv_actV, coordinateAutomorphism_apply]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
