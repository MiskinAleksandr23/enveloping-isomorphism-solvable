import EnvelopingIsomorphism.Rees.UniformBound
import EnvelopingIsomorphism.Rees.SymmetricScalarCoordinates
import EnvelopingIsomorphism.Rees.LaurentPolynomialCoefficients

/-!
# The genuine completed comparison and its polynomial input values

The completed operator is built by the uniform bound. Its values on polynomial inputs are
then compared with the actual E1 conjugation over `k((h))[t]`. The latter is used only on
finite polynomial inputs; no rescaling map on the entire Laurent function algebra is asserted.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.CompletedComparison

open Module
open EnvelopingIsomorphism.FormalSeries
open scoped LaurentPolynomialCoefficients

variable {k ι L M : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Basis ι k L} {bM : Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- The actual homogenized Rees map on finite polynomial coordinates over `k((h))[t]`. -/
def homogenizedMap :
    MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k) →ₗ[LaurentPolynomialCoefficients.ScalarRing k]
      MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k) :=
  Homogenization.symPolynomialMap
    (Scaled.basis (LaurentPolynomialCoefficients.hbarPolynomialUnit k :
      LaurentPolynomialCoefficients.ScalarRing k)
        ((Family.basis dL).baseChange (LaurentPolynomialCoefficients.ScalarRing k)))
    (Scaled.basis (LaurentPolynomialCoefficients.hbarPolynomialUnit k :
      LaurentPolynomialCoefficients.ScalarRing k)
        ((Family.basis dM).baseChange (LaurentPolynomialCoefficients.ScalarRing k)))
    (Homogenization.baseChangedConjugate (LaurentPolynomialCoefficients.ScalarRing k)
      (LaurentPolynomialCoefficients.hbarPolynomialUnit k)
      (EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ'))

/-- E1 gives an exact coefficient identity before any completion is used. -/
theorem homogenized_monomial_coefficient (a m : ι →₀ ℕ) :
    MvPolynomial.coeff m (homogenizedMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial a 1)) =
      Homogenization.unitPower (LaurentPolynomialCoefficients.hbarPolynomialUnit k)
        ((a.degree : ℤ) - (m.degree : ℤ)) *
          algebraMap (Polynomial k) (LaurentPolynomialCoefficients.ScalarRing k)
            (MvPolynomial.coeff m (UniformBound.comparisonMap dL dM Φ hw hΦ hΦ'
              (MvPolynomial.monomial a 1))) := by
  rw [homogenizedMap, Homogenization.coeff_symPolynomialMap_monomial,
    Homogenization.baseChangedConjugate, Homogenization.conjugate_sym_coefficient]
  have he := SymmetricScalarCoordinates.coeff_symPolynomialMap_monomial_baseChange
    (Polynomial k) (LaurentPolynomialCoefficients.ScalarRing k) (Family.basis dL) (Family.basis dM)
    (EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ') a m
  rw [Homogenization.coeff_symPolynomialMap_monomial] at he
  rw [he]
  rfl

/-- The true two-parameter coefficient operator of the finite polynomial homogenized map. -/
def homogenizedCoefficientOperator (r : ℕ) (j : ℤ) : Module.End k ((ι →₀ ℕ) →₀ k) :=
  PolynomialCoefficientOperators.coefficientOperator (LaurentPolynomialCoefficients.doubleCoeff k r j)
    (homogenizedMap dL dM Φ hw hΦ hΦ')

theorem homogenizedCoefficientOperator_single (r : ℕ) (j : ℤ) (a m : ι →₀ ℕ) :
    homogenizedCoefficientOperator dL dM Φ hw hΦ hΦ' r j (Finsupp.single a 1) m =
      if j = (a.degree : ℤ) - (m.degree : ℤ) then
        (MvPolynomial.coeff m (UniformBound.comparisonMap dL dM Φ hw hΦ hΦ'
          (MvPolynomial.monomial a 1))).coeff r else 0 := by
  rw [homogenizedCoefficientOperator, PolynomialCoefficientOperators.coefficientOperator_single,
    homogenized_monomial_coefficient, LaurentPolynomialCoefficients.doubleCoeff_apply]
  exact LaurentPolynomialCoefficients.doubleCoeff_unitPower_parameter k _ _ _ _

/-- The actual homogenized matrix equals exactly the reweighted degree diagonal of `F_r`. -/
theorem homogenizedCoefficientOperator_eq_degreeDiagonal (r : ℕ) (j : ℤ) :
    homogenizedCoefficientOperator dL dM Φ hw hΦ hΦ' r j =
      degreeDiagonal (fun m : ι →₀ ℕ ↦ m.degree)
        (UniformBound.coefficientOperator dL dM Φ hw hΦ hΦ' r) j := by
  apply PolynomialCoefficientOperators.coordinate_end_ext
  intro a m
  rw [homogenizedCoefficientOperator_single, degreeDiagonal_single_one_apply,
    UniformBound.coefficientOperator_single]
  simp only [eq_comm]

/-- Every coefficient of the actual completed operator agrees with the finite homogenized map. -/
theorem completedOperator_coeff_agrees (r : ℕ) (j : ℤ) :
    (PowerSeries.coeff r (UniformBound.completedOperator dL dM Φ hw hΦ hΦ')).coeff j =
      homogenizedCoefficientOperator dL dM Φ hw hΦ hΦ' r j := by
  rw [UniformBound.completedOperator, coeff_reweightPowerSeries,
    homogenizedCoefficientOperator_eq_degreeDiagonal]

/-- Agreement holds on every polynomial input, after its actual scalar coefficient inclusion. -/
theorem completedOperator_polynomial_input (r : ℕ) (j : ℤ)
    (p : (ι →₀ ℕ) →₀ k) (m : ι →₀ ℕ) :
    ((PowerSeries.coeff r (UniformBound.completedOperator dL dM Φ hw hΦ hΦ')).coeff j p) m =
      LaurentPolynomialCoefficients.doubleCoeff k r j
        (MvPolynomial.coeff m (homogenizedMap dL dM Φ hw hΦ hΦ'
          (PolynomialCoefficientOperators.includePolynomial
            (S := LaurentPolynomialCoefficients.ScalarRing k) p))) := by
  rw [completedOperator_coeff_agrees, homogenizedCoefficientOperator,
    PolynomialCoefficientOperators.coefficientOperator_apply]

/-- The F4 Laurent-linear action is defined on all Laurent inputs and has these exact values
on constant polynomial inputs. It is not defined by applying an unbounded inverse dilation. -/
theorem completedLaurentAction_polynomial_input (r : ℕ) (j : ℤ)
    (p : (ι →₀ ℕ) →₀ k) (m : ι →₀ ℕ) :
    LaurentModule.coeff
      (actLaurent (reweightFamily (fun m : ι →₀ ℕ ↦ m.degree)
        (UniformBound.coefficientOperator dL dM Φ hw hΦ hΦ')
        (UniformBound.generatorDegreeBound (bL := bL) (bM := bM) Φ)
        (UniformBound.actual_degreeShift dL dM Φ hw hΦ hΦ') r)
        (LaurentModule.single 0 p)) j m =
      LaurentPolynomialCoefficients.doubleCoeff k r j
        (MvPolynomial.coeff m (homogenizedMap dL dM Φ hw hΦ hΦ'
          (PolynomialCoefficientOperators.includePolynomial
            (S := LaurentPolynomialCoefficients.ScalarRing k) p))) := by
  rw [actLaurent_constant, coeff_applyToConstant, coeff_reweightFamily,
    ← homogenizedCoefficientOperator_eq_degreeDiagonal, homogenizedCoefficientOperator,
    PolynomialCoefficientOperators.coefficientOperator_apply]

end EnvelopingIsomorphism.Rees.CompletedComparison
