import EnvelopingIsomorphism.Rees.CompletedComparisonAction
import EnvelopingIsomorphism.Rees.CompletedPBWProduct
import EnvelopingIsomorphism.Rees.StarComparison

/-! The actual completed Rees comparison intertwines the actual completed PBW
products. The equation is deduced from native enveloping multiplication, rather
than supplied as an extra comparison hypothesis. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace EnvelopingIsomorphism.Rees.CompletedPBWProduct

open FormalSeries CompletedOperator PolynomialCoefficientOperators
open scoped CompletedOperator LaurentPolynomialCoefficients CompletedPolynomialInputs

variable {k ι L : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] {b : Module.Basis ι k L} (d : WeightData b)

theorem completedAction_constants (p q : Coordinates ι k) :
    CompletedBinary.binaryAction (completedProduct d) (constant p) (constant q) =
      CompletedPolynomialInputs.embed
        (homogenizedProduct d (includePolynomial p) (includePolynomial q)) := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply Finsupp.ext
  intro m
  rw [CompletedPolynomialInputs.coeff_embed]
  exact completedProduct_polynomial_inputs d r j p q m

/-- Native finite polynomial inputs are included by the same true scalar-linear map. -/
theorem completedAction_polynomials
    (p q : MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k)) :
    CompletedBinary.binaryAction (completedProduct d)
        (CompletedPolynomialInputs.embed p) (CompletedPolynomialInputs.embed q) =
      CompletedPolynomialInputs.embed (homogenizedProduct d p q) :=
  CompletedPolynomialInputs.bilinear_extension _ _ (completedAction_constants d) p q

end EnvelopingIsomorphism.Rees.CompletedPBWProduct

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

/-- The finite homogenized comparison preserves the actual native PBW product. -/
theorem homogenizedMap_product
    (p q : MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k)) :
    homogenizedMap dL dM Φ hw hΦ hΦ' (CompletedPBWProduct.homogenizedProduct dL p q) =
      CompletedPBWProduct.homogenizedProduct dM
        (homogenizedMap dL dM Φ hw hΦ hΦ' p) (homogenizedMap dL dM Φ hw hΦ hΦ' q) := by
  unfold homogenizedMap CompletedPBWProduct.homogenizedProduct
  exact SymmetricPBWProduct.symPolynomialMap_product _ _ _ p q

/-- Multiplicativity of the original actual enveloping map implies intertwining
on the entire Laurent-then-power-series function module. -/
theorem completedAction_product (x y : Vectors k (Coordinates ι k)) :
    actionHom (UniformBound.completedOperator dL dM Φ hw hΦ hΦ')
        (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dL) x y) =
      CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dM)
        (actionHom (UniformBound.completedOperator dL dM Φ hw hΦ hΦ') x)
        (actionHom (UniformBound.completedOperator dL dM Φ hw hΦ hΦ') y) := by
  apply CompletedBinary.intertwines_of_constants
  intro p q
  rw [CompletedPBWProduct.completedAction_constants, completedAction_polynomial,
    completedAction_constant, completedAction_constant,
    CompletedPBWProduct.completedAction_polynomials, homogenizedMap_product]

theorem completedUnit_intertwines :
    StarComparison.Intertwines (UniformBound.completedUnit dL dM Φ hw hΦ hΦ')
      (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dL))
      (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dM)) := by
  intro x y
  simp only [actionEquiv_apply, UniformBound.completedUnit_val]
  exact completedAction_product dL dM Φ hw hΦ hΦ' x y

end EnvelopingIsomorphism.Rees.CompletedComparison

namespace EnvelopingIsomorphism.Rees.StarComparison

open FormalSeries CompletedOperator PolynomialCoefficientOperators
open scoped CompletedOperator

variable {k ι L M : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Module.Basis ι k L} {bM : Module.Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- Once the two graph comparisons intertwine their actual PBW products, their
conjugation by the actual Rees map intertwines the graph products. There is no
assumed equation for the middle comparison and no assumed existence of the result. -/
theorem ofRees_intertwines
    (J_L J_M : (Operators k (Coordinates ι k))ˣ)
    (σ_L σ_M : Deformation.Binary (PowerSeries (LaurentSeries k)) (Vectors k (Coordinates ι k)))
    (hJ_L : Intertwines J_L
      (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dL)) σ_L)
    (hJ_M : Intertwines J_M
      (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct dM)) σ_M) :
    Intertwines (ofRees dL dM Φ hw hΦ hΦ' J_L J_M) σ_L σ_M :=
  conjugatedUnit_intertwines _ _ _
    (CompletedComparison.completedUnit_intertwines dL dM Φ hw hΦ hΦ') hJ_L hJ_M

end EnvelopingIsomorphism.Rees.StarComparison
