import EnvelopingIsomorphism.FormalSeries.PolynomialModuleCalculus
import EnvelopingIsomorphism.FormalSeries.PathOrderedExp

/-! Polynomial-module calculus agrees with ordinary polynomials over a possibly
noncommutative coefficient algebra. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PolynomialModuleRingBridge

open PolynomialModule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

/-- The coefficient-preserving equivalence; coefficient multiplication need not commute. -/
def toPolynomial : PolynomialModule k R ≃ₗ[k] Polynomial R where
  toAddEquiv := PolynomialModule.coeffAddEquiv.trans <|
    AddMonoidAlgebra.coeffAddEquiv.symm.trans (Polynomial.toFinsuppIso R).symm.toAddEquiv
  map_smul' _ _ := rfl

/-- Regard an ordinary polynomial as a polynomial with vector coefficients. -/
def toModule : Polynomial R ≃ₗ[k] PolynomialModule k R := toPolynomial.symm

@[simp] theorem coeff_toPolynomial (p : PolynomialModule k R) (n : ℕ) :
    (toPolynomial p).coeff n = p.coeff n := rfl

@[simp] theorem coeff_toModule (p : Polynomial R) (n : ℕ) :
    (toModule (k := k) p).coeff n = p.coeff n := rfl

@[simp] theorem toModule_monomial (n : ℕ) (r : R) :
    toModule (k := k) (Polynomial.monomial n r) = PolynomialModule.single k n r := rfl

@[simp] theorem toPolynomial_single (n : ℕ) (r : R) :
    toPolynomial (PolynomialModule.single k n r) = Polynomial.monomial n r := rfl

theorem toModule_derivative (p : Polynomial R) :
    toModule (k := k) p.derivative = PolynomialModuleCalculus.derivative (toModule p) := by
  apply PolynomialModule.ext
  ext n
  simp only [coeff_toModule, PolynomialModuleCalculus.coeff_derivative, Polynomial.coeff_derivative]
  simpa only [nsmul_eq_mul', Nat.cast_add, Nat.cast_one] using
    (Nat.cast_smul_eq_nsmul k (n + 1) (p.coeff (n + 1))).symm

theorem toPolynomial_derivative (p : PolynomialModule k R) :
    toPolynomial (PolynomialModuleCalculus.derivative p) = (toPolynomial p).derivative := by
  apply (toModule (k := k)).injective
  rw [toModule_derivative]
  simp only [toModule, LinearEquiv.symm_apply_apply]

theorem eval_toModule (p : Polynomial R) (s : k) :
    PolynomialModule.eval s (toModule p) = p.eval₂ (RingHom.id R) (algebraMap k R s) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n r =>
    simp only [toModule_monomial, PolynomialModule.eval_single,
      Polynomial.eval₂_monomial, RingHom.id_apply, Algebra.smul_def, map_pow]
    simpa only [map_pow] using Algebra.commutes (s ^ n) r

theorem toModule_mul (p q : Polynomial R) :
    toModule (k := k) (p * q) =
      PolynomialModuleCalculus.extendBilinear (LinearMap.mul k R) (toModule p) (toModule q) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => simp [add_mul, hp, hp']
  | monomial n r =>
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' => simp [mul_add, hq, hq']
    | monomial m s => simp [Polynomial.monomial_mul_monomial]

/-- Standard ring-valued power series as vector-valued Hahn power series. -/
def seriesEquiv : PowerSeries R ≃ₗ[k] PowerSeriesModule k R where
  toFun p := PowerSeriesModule.mk (fun n ↦ PowerSeries.coeff n p)
  invFun p := PowerSeries.mk (fun n ↦ PowerSeriesModule.coeffV n p)
  left_inv p := by ext n; simp
  right_inv p := by apply PowerSeriesModule.ext; intro n; simp
  map_add' p q := by ext n; simp
  map_smul' r p := by ext n; simp

@[simp] theorem coeff_seriesEquiv (p : PowerSeries R) (n : ℕ) :
    PowerSeriesModule.coeffV n (seriesEquiv (k := k) p) = PowerSeries.coeff n p := rfl

/-- The actual path-ordered-exponential space as completed polynomial-module paths. -/
def pathEquiv : PathOrderedExp.PathSeries R ≃ₗ[k] PowerSeriesModule k (PolynomialModule k R) where
  toFun p := PowerSeriesModule.mk (fun n ↦ toModule (PowerSeries.coeff n p))
  invFun p := PowerSeries.mk (fun n ↦ toPolynomial (PowerSeriesModule.coeffV n p))
  left_inv p := by ext n; simp [toModule]
  right_inv p := by apply PowerSeriesModule.ext; intro n; simp [toModule]
  map_add' p q := by ext n; simp
  map_smul' r p := by ext n; simp

@[simp] theorem coeff_pathEquiv (p : PathOrderedExp.PathSeries R) (n : ℕ) :
    PowerSeriesModule.coeffV n (pathEquiv (k := k) p) = toModule (PowerSeries.coeff n p) := rfl

/-- The coefficient-preserving map used for the actual conjugation path. -/
abbrev ofRingPath : PathOrderedExp.PathSeries R →ₗ[k] PowerSeriesModule k (PolynomialModule k R) :=
  pathEquiv.toLinearMap

theorem pathEquiv_mul (p q : PathOrderedExp.PathSeries R) :
    pathEquiv (k := k) (p * q) =
      PowerSeriesModule.extendBilinear
        (PolynomialModuleCalculus.extendBilinear (LinearMap.mul k R)) (pathEquiv p) (pathEquiv q) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeff_pathEquiv, PowerSeriesModule.extendBilinear_apply,
    PowerSeriesModule.coeffV_applyBilinear, PowerSeries.coeff_mul, map_sum, toModule_mul]

theorem pathEquiv_eval_zero (p : PathOrderedExp.PathSeries R) :
    PolynomialModuleCalculus.seriesEval 0 (pathEquiv (k := k) p) =
      seriesEquiv (PathOrderedExp.atZero p) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [PolynomialModuleCalculus.coeff_seriesEval, coeff_pathEquiv,
    PolynomialModuleCalculus.eval_zero, coeff_toModule, coeff_seriesEquiv, PathOrderedExp.coeff_atZero]

section Rational

variable [Algebra ℚ R]

theorem pathEquiv_derivative (p : PathOrderedExp.PathSeries R) :
    pathEquiv (k := k) (PathOrderedExp.parameterDerivative p) =
      PolynomialModuleCalculus.seriesDerivative (pathEquiv p) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeff_pathEquiv, PathOrderedExp.coeff_parameterDerivative,
    PolynomialModuleCalculus.coeff_seriesDerivative, toModule_derivative]

theorem ofRingPath_derivative (p : PathOrderedExp.PathSeries R) :
    PolynomialModuleCalculus.seriesDerivative (ofRingPath (k := k) p) =
      ofRingPath (PathOrderedExp.parameterDerivative p) :=
  (pathEquiv_derivative p).symm

theorem pathEquiv_eval_one (p : PathOrderedExp.PathSeries R) :
    PolynomialModuleCalculus.seriesEval 1 (pathEquiv (k := k) p) =
      seriesEquiv (PathOrderedExp.evaluation 1 p) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [PolynomialModuleCalculus.coeff_seriesEval, coeff_pathEquiv, eval_toModule,
    coeff_seriesEquiv, PathOrderedExp.coeff_evaluation, map_one]

end Rational

end EnvelopingIsomorphism.FormalSeries.PolynomialModuleRingBridge
