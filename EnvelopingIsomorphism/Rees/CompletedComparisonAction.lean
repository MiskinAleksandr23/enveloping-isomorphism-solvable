import EnvelopingIsomorphism.Rees.CompletedComparisonData
import EnvelopingIsomorphism.FormalSeries.CompletedPolynomialInputs

/-! The actual completed E2/E3 operator agrees with the finite homogenized map
on every finite polynomial over `k((h))[t]`, under the genuine completion embedding. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.CompletedComparison

open FormalSeries CompletedOperator PolynomialCoefficientOperators
open scoped CompletedOperator LaurentPolynomialCoefficients CompletedPolynomialInputs

variable {k ι L M : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Module.Basis ι k L} {bM : Module.Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- Equality of completed vectors, not merely a statement about selected coefficients. -/
theorem completedAction_constant (p : Coordinates ι k) :
    actionHom (UniformBound.completedOperator dL dM Φ hw hΦ hΦ') (constant p) =
      CompletedPolynomialInputs.embed
        (homogenizedMap dL dM Φ hw hΦ hΦ' (includePolynomial p)) := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply Finsupp.ext
  intro m
  rw [coeff_action_constant, CompletedPolynomialInputs.coeff_embed]
  exact completedOperator_polynomial_input dL dM Φ hw hΦ hΦ' r j p m

/-- Full scalar-series linearity extends the proved constant-input identity to every
finite polynomial input with Laurent-polynomial scalar coefficients. -/
theorem completedAction_polynomial (p : MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k)) :
    actionHom (UniformBound.completedOperator dL dM Φ hw hΦ hΦ')
        (CompletedPolynomialInputs.embed p) =
      CompletedPolynomialInputs.embed (homogenizedMap dL dM Φ hw hΦ hΦ' p) :=
  CompletedPolynomialInputs.linear_extension _ _
    (completedAction_constant dL dM Φ hw hΦ hΦ') p

theorem completedUnitAction_polynomial
    (p : MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k)) :
    actionEquiv (UniformBound.completedUnit dL dM Φ hw hΦ hΦ')
        (CompletedPolynomialInputs.embed p) =
      CompletedPolynomialInputs.embed (homogenizedMap dL dM Φ hw hΦ hΦ' p) := by
  rw [actionEquiv_apply, UniformBound.completedUnit_val]
  exact completedAction_polynomial dL dM Φ hw hΦ hΦ' p

end EnvelopingIsomorphism.Rees.CompletedComparison
