import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenElementary
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPathOperations
import EnvelopingIsomorphism.FormalSeries.PolynomialModuleRingBridge

/-! The actual polynomial-in-parameter elementary path in the Laurent Schouten source. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.MonomialOperatorPath

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule PowerSeries
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

variable {k V : Type*} [CommRing k] [Algebra ℚ k] [AddCommGroup V] [Module k V]
  [Module ℚ V] [IsScalarTower ℚ k V] [SMulCommClass k ℚ V]

local instance : Ring (Module.End k V) := @Module.End.instRing k V inferInstance inferInstance inferInstance

/-- The genuine formal exponential with polynomial coefficient parameter `s`. -/
def ringPath (N : ℕ) (D : Module.End k V) : PathOrderedExp.PathSeries (Module.End k V) :=
  exp (monomial N (Polynomial.monomial 1 D))

/-- Each formal coefficient is an actual polynomial of endomorphisms. -/
def operatorPath (N : ℕ) (D : Module.End k V) : ModulePath k (Module.End k V) :=
  PolynomialModuleRingBridge.pathEquiv (ringPath N D)

/-- The actual finite polynomial coefficient formula, retaining the exponential factorial. -/
theorem coeff_operatorPath (N : ℕ) (D : Module.End k V) (n : ℕ) :
    coeffV n (operatorPath N D) = PolynomialModuleRingBridge.toModule (k := k)
      (∑ m ∈ Finset.range (n + 1), (m.factorial : ℚ)⁻¹ •
        (if m * N = n then Polynomial.monomial m (D ^ m) else 0)) := by
  rw [operatorPath, PolynomialModuleRingBridge.coeff_pathEquiv]
  simp only [ringPath, FormalSeries.exp, coeff_sumPowers, noncomm_monomial_pow,
    PowerSeries.coeff_monomial, Polynomial.monomial_pow, one_mul, one_div, eq_comm]

theorem operatorPath_eval (N : ℕ) (D : Module.End k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (operatorPath N D) =
      operatorSeries (exp (monomial N (s • D))) := by
  let ρ : Polynomial (Module.End k V) →+* Module.End k V :=
    Polynomial.eval₂RingHom' (RingHom.id _) (algebraMap k (Module.End k V) s)
      (fun a => (Algebra.commutes s a).symm)
  have he : PolynomialModuleCalculus.seriesEval s (operatorPath N D) =
      operatorSeries (PowerSeries.map ρ (ringPath N D)) := by
    apply PowerSeriesModule.ext
    intro n
    simp only [operatorPath, PolynomialModuleCalculus.coeff_seriesEval,
      PolynomialModuleRingBridge.coeff_pathEquiv, PolynomialModuleRingBridge.eval_toModule,
      coeffV_operatorSeries, PowerSeries.coeff_map]
    rfl
  have hm : PowerSeries.map ρ (monomial N (Polynomial.monomial 1 D)) = monomial N (s • D) := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_monomial]
    split_ifs
    · change (Polynomial.monomial 1 D).eval₂ (RingHom.id _) (algebraMap k (Module.End k V) s) = s • D
      rw [Polynomial.eval₂_monomial, RingHom.id_apply, pow_one, Algebra.smul_def]
      exact (Algebra.commutes s D).symm
    · exact map_zero ρ
  rw [he, ringPath, FormalSeries.map_exp, hm]

theorem operatorPath_below (N : ℕ) (hN : 0 < N) (D : Module.End k V)
    (n : ℕ) (hn : n < N) :
    coeffV n (operatorPath N D) = if n = 0 then PolynomialModule.single k 0 (1 : Module.End k V) else 0 := by
  have hc := (elementaryGauge_near N hN (Polynomial.monomial 1 D)).coeff n hn
  change coeff n (ringPath N D) = coeff n (1 : PowerSeries (Polynomial (Module.End k V))) at hc
  rw [operatorPath, PolynomialModuleRingBridge.coeff_pathEquiv, hc, PowerSeries.coeff_one]
  split_ifs
  · change PolynomialModuleRingBridge.toModule (k := k) (Polynomial.monomial 0 (1 : Module.End k V)) = _
    rw [PolynomialModuleRingBridge.toModule_monomial]
  · exact map_zero _

/-- Apply the actual parameterized exponential to a constant vector-series family. -/
def fullPath (N : ℕ) (D : Module.End k V) (B : PowerSeriesModule k V) : ModulePath k V :=
  pathOperator (operatorPath N D) (constantPath B)

theorem fullPath_eval (N : ℕ) (D : Module.End k V) (B : PowerSeriesModule k V) (s : k) :
    PolynomialModuleCalculus.seriesEval s (fullPath N D B) =
      actV (exp (monomial N (s • D))) B := by
  change PolynomialModuleCalculus.seriesEval s
    (pathBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
      (operatorPath N D) (constantPath B)) = _
  rw [pathBilinear_eval, operatorPath_eval, constantPath_eval]
  exact operator_apply _ _

@[simp] theorem fullPath_eval_zero (N : ℕ) (D : Module.End k V) (B : PowerSeriesModule k V) :
    PolynomialModuleCalculus.seriesEval 0 (fullPath N D B) = B := by
  rw [fullPath_eval, zero_smul, map_zero, exp_zero, actV_one]

@[simp] theorem fullPath_eval_one (N : ℕ) (D : Module.End k V) (B : PowerSeriesModule k V) :
    PolynomialModuleCalculus.seriesEval 1 (fullPath N D B) = actV (exp (monomial N D)) B := by
  rw [fullPath_eval, one_smul]

theorem fullPath_agree (N : ℕ) (hN : 0 < N) (D : Module.End k V) (B : PowerSeriesModule k V) :
    AgreeBelow N (fullPath N D B) (constantPath B) := by
  intro n hn
  have h := coeffV_applyBilinear_left_agree
    (PolynomialModuleCalculus.extendBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V))
    (operatorPath N D) (constantPath B) (PolynomialModule.single k 0 (1 : Module.End k V))
    (operatorPath_below N hN D) n hn
  change coeffV n (fullPath N D B) = _ at h
  rw [h]
  change PolynomialModuleCalculus.extendBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
    (PolynomialModule.single k 0 (1 : Module.End k V)) (PolynomialModule.single k 0 (coeffV n B)) = _
  rw [PolynomialModuleCalculus.extendBilinear_single_single]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.MonomialOperatorPath

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

local instance : CharZero (Scalars K) := scalarCharZero
local instance : Module ℚ (Bivector K d) := bivectorRationalModule
local instance : IsScalarTower ℚ (Scalars K) (Bivector K d) := bivectorRationalTower
local instance : SMulCommClass (Scalars K) ℚ (Bivector K d) := bivectorRationalComm
local instance : Ring (Module.End (Scalars K) (Bivector K d)) :=
  @Module.End.instRing (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance
local instance : AddCommGroup (PowerSeriesModule (Scalars K) (Bivector K d)) :=
  @HahnModule.instAddCommGroup ℕ (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance

/-- The canonical full elementary path before subtracting the fixed Poisson base. -/
def elementaryFullPath (π : Bivector K d) (N : ℕ) (X : Vector K d) (b : Families K d) :
    ModulePath (Scalars K) (Bivector K d) :=
  MonomialOperatorPath.fullPath N (action X) (single 0 π + b)

/-- Actual affine elementary motion with polynomial parameter in every formal degree. -/
def elementaryPath (π : Bivector K d) (N : ℕ) (X : Vector K d) (b : Families K d) :
    ModulePath (Scalars K) (Bivector K d) :=
  elementaryFullPath π N X b - constantPath (single 0 π)

theorem elementaryPath_eval (π : Bivector K d) (N : ℕ) (X : Vector K d) (b : Families K d) (s : Scalars K) :
    PolynomialModuleCalculus.seriesEval s (elementaryPath π N X b) =
      actV (FormalSeries.exp (PowerSeries.monomial N (s • action X))) (single 0 π + b) - single 0 π := by
  rw [elementaryPath, map_sub, constantPath_eval]
  exact congrArg (fun F => F - single (k := Scalars K) 0 π)
    (MonomialOperatorPath.fullPath_eval N (action X) (single 0 π + b) s)

@[simp] theorem elementaryPath_eval_zero (π : Bivector K d) (N : ℕ) (X : Vector K d) (b : Families K d) :
    PolynomialModuleCalculus.seriesEval 0 (elementaryPath π N X b) = b := by
  rw [elementaryPath, map_sub, constantPath_eval]
  change PolynomialModuleCalculus.seriesEval 0 (MonomialOperatorPath.fullPath N (action X) (single 0 π + b)) - single 0 π = b
  rw [MonomialOperatorPath.fullPath_eval_zero]
  abel

@[simp] theorem elementaryPath_eval_one (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) :
    PolynomialModuleCalculus.seriesEval 1 (elementaryPath π N X b) = motion π N hN X b := by
  rw [elementaryPath, map_sub, constantPath_eval]
  change PolynomialModuleCalculus.seriesEval 1 (MonomialOperatorPath.fullPath N (action X) (single 0 π + b)) - single 0 π = _
  rw [MonomialOperatorPath.fullPath_eval_one]
  exact congrArg (fun F => F - single (k := Scalars K) 0 π) (sourceEquiv_apply N hN X (single 0 π + b)).symm

theorem elementaryPath_agree (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) :
    AgreeBelow N (elementaryPath π N X b) (constantPath b) := by
  intro n hn
  have h := MonomialOperatorPath.fullPath_agree N hN (action X) (single 0 π + b) n hn
  change coeffV n (elementaryFullPath π N X b) = _ at h
  rw [elementaryPath, coeffV_sub, h]
  change PolynomialModule.single (Scalars K) 0 (coeffV n (single 0 π + b)) -
    PolynomialModule.single (Scalars K) 0 (coeffV n (single 0 π)) = PolynomialModule.single (Scalars K) 0 (coeffV n b)
  rw [coeffV_add, PolynomialModule.single_add]
  abel

theorem elementaryPath_positive (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) (hb : coeffV 0 b = 0) :
    coeffV 0 (elementaryPath π N X b) = 0 := by
  rw [elementaryPath_agree π N hN X b 0 hN]
  change PolynomialModule.single (Scalars K) 0 (coeffV 0 b) = 0
  rw [hb, PolynomialModule.single_zero]

/-- Every parameter value is the same already verified elementary motion in the scaled direction. -/
theorem elementaryPath_eval_motion (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) (s : Scalars K) :
    PolynomialModuleCalculus.seriesEval s (elementaryPath π N X b) = motion π N hN (s • X) b := by
  rw [elementaryPath_eval, motion, sourceEquiv_apply, (action (K := K) (d := d)).map_smul s X]

/-- The constructed path consists of genuine MC solutions whenever its starting point does. -/
theorem elementaryPath_eval_MC (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (N : ℕ) (hN : 0 < N) (X : Vector K d) (b : MC π) (s : Scalars K) :
    quadraticCurvature (bivectorBracket π) ((2 : Scalars K)⁻¹ • bivectorBracket)
      (PolynomialModuleCalculus.seriesEval s (elementaryPath π N X b.val)) = 0 := by
  rw [elementaryPath_eval_motion π N hN X b.val s]
  exact motion_preserves_MC π hπ N hN (s • X) b.val b.property.2

end EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
