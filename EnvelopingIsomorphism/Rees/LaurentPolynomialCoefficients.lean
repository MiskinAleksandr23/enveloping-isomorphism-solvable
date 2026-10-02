import EnvelopingIsomorphism.Rees.Homogenization
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Algebra.Rat

/-!
# Two separate parameters: Laurent coefficients and outer polynomials

The polynomial parameter map preserves the outer variable. The inner Laurent
parameter appears only in coefficients. Scalar instances are explicitly tied
to this map, so they cannot use evaluation of the outer variable at the inner
Laurent parameter.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.LaurentPolynomialCoefficients

variable (k : Type*) [Field k]

abbrev ScalarRing := Polynomial (LaurentSeries k)

/-- Extend coefficients and preserve the polynomial variable itself. -/
def parameterMap : Polynomial k →+* ScalarRing k :=
  Polynomial.mapRingHom (algebraMap k (LaurentSeries k))

scoped instance parameterAlgebra : Algebra (Polynomial k) (ScalarRing k) :=
  (parameterMap k).toAlgebra

scoped instance parameterSMul : SMul (Polynomial k) (ScalarRing k) :=
  (parameterAlgebra k).toSMul

scoped instance parameterModule : Module (Polynomial k) (ScalarRing k) := Algebra.toModule

/-- Original scalars act coefficientwise in both parameters. -/
scoped instance coefficientAlgebra : Algebra k (ScalarRing k) := Polynomial.algebraOfAlgebra

scoped instance coefficientSMul : SMul k (ScalarRing k) := (coefficientAlgebra k).toSMul

scoped instance coefficientModule : Module k (ScalarRing k) := Algebra.toModule

@[simp] theorem algebraMap_parameter (p : Polynomial k) :
    algebraMap (Polynomial k) (ScalarRing k) p = parameterMap k p := rfl

@[simp] theorem parameterMap_X : parameterMap k Polynomial.X = Polynomial.X := by
  simp [parameterMap]

@[simp] theorem algebraMap_X :
    algebraMap (Polynomial k) (ScalarRing k) Polynomial.X = Polynomial.X := by
  rw [algebraMap_parameter, parameterMap_X]

@[simp] theorem parameterMap_C (c : k) :
    parameterMap k (Polynomial.C c) = Polynomial.C (algebraMap k (LaurentSeries k) c) := by
  simp [parameterMap]

@[simp] theorem coeff_parameterMap (p : Polynomial k) (r : ℕ) :
    (parameterMap k p).coeff r = algebraMap k (LaurentSeries k) (p.coeff r) := by
  simp [parameterMap]

@[simp] theorem parameter_smul (p : Polynomial k) (q : ScalarRing k) :
    p • q = parameterMap k p * q := rfl

scoped instance coefficientTower : IsScalarTower k (Polynomial k) (ScalarRing k) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change Polynomial.C (algebraMap k (LaurentSeries k) c) = parameterMap k (Polynomial.C c)
  exact (parameterMap_C k c).symm

/-- Rational scalars remain compatible with the chosen outer-parameter algebra. -/
scoped instance rationalTower [CharZero k] : IsScalarTower ℚ (Polynomial k) (ScalarRing k) :=
  by
    apply IsScalarTower.of_algebraMap_eq
    intro q
    exact ((parameterMap k).map_rat_algebraMap q).symm

/-- The inner Laurent parameter as a unit, with its explicit inverse. -/
def hbarUnit : (LaurentSeries k)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by simp [HahnSeries.single_mul_single]
  inv_val := by simp [HahnSeries.single_mul_single]

@[simp] theorem hbarUnit_val : (hbarUnit k : LaurentSeries k) = HahnSeries.single 1 1 := rfl

/-- The same inner unit viewed as a constant outer polynomial. -/
def hbarPolynomialUnit : (ScalarRing k)ˣ :=
  Units.map (Polynomial.C : LaurentSeries k →+* ScalarRing k).toMonoidHom (hbarUnit k)

@[simp] theorem hbarPolynomialUnit_val :
    (hbarPolynomialUnit k : ScalarRing k) = Polynomial.C (HahnSeries.single 1 (1 : k)) := rfl

theorem hbarUnit_zpow (z : ℤ) : ((hbarUnit k ^ z : (LaurentSeries k)ˣ) : LaurentSeries k) =
    HahnSeries.single z (1 : k) := by
  rw [Units.val_zpow_eq_zpow_val, hbarUnit_val]
  exact (RatFunc.single_zpow z).symm

/-- Every integer power is a constant outer polynomial with one Laurent coefficient. -/
theorem unitPower_hbarPolynomial (z : ℤ) :
    Homogenization.unitPower (hbarPolynomialUnit k) z =
      Polynomial.C (HahnSeries.single z (1 : k)) := by
  unfold Homogenization.unitPower hbarPolynomialUnit
  rw [← map_zpow]
  change Polynomial.C ((hbarUnit k ^ z : (LaurentSeries k)ˣ) : LaurentSeries k) = _
  rw [hbarUnit_zpow]

/-- Extract an outer polynomial coefficient and then an inner Laurent coefficient. -/
def doubleCoeff (r : ℕ) (j : ℤ) : ScalarRing k →ₗ[k] k where
  toFun q := (q.coeff r).coeff j
  map_add' p q := by simp [Polynomial.coeff_add, HahnSeries.coeff_add]
  map_smul' c q := by
    change ((c • q).coeff r).coeff j = c * (q.coeff r).coeff j
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
    have hc : algebraMap k (LaurentSeries k) c = HahnSeries.C c := by
      simp [HahnSeries.algebraMap_apply']
    rw [hc, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

@[simp] theorem doubleCoeff_apply (r : ℕ) (j : ℤ) (q : ScalarRing k) :
    doubleCoeff k r j q = (q.coeff r).coeff j := rfl

theorem doubleCoeff_algebraMap_mul (r : ℕ) (j : ℤ) (c : k) (q : ScalarRing k) :
    doubleCoeff k r j (algebraMap k (ScalarRing k) c * q) = c * doubleCoeff k r j q := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The outer parameter stays outer: multiplying by an inner monomial only shifts
the Laurent exponent of each independently extracted polynomial coefficient. -/
theorem doubleCoeff_unitPower_parameter (z : ℤ) (p : Polynomial k) (r : ℕ) (j : ℤ) :
    ((Homogenization.unitPower (hbarPolynomialUnit k) z *
      algebraMap (Polynomial k) (ScalarRing k) p).coeff r).coeff j =
        if j = z then p.coeff r else 0 := by
  rw [unitPower_hbarPolynomial, Polynomial.coeff_C_mul, algebraMap_parameter, coeff_parameterMap]
  have hc : algebraMap k (LaurentSeries k) (p.coeff r) = HahnSeries.C (p.coeff r) := by
    simp [HahnSeries.algebraMap_apply']
  rw [hc]
  simp [HahnSeries.C_apply, HahnSeries.single_mul_single, HahnSeries.coeff_single]

end EnvelopingIsomorphism.Rees.LaurentPolynomialCoefficients
