import EnvelopingIsomorphism.Rees.CompletedGraphProduct
import EnvelopingIsomorphism.Rees.CompletedComparisonProduct
import EnvelopingIsomorphism.Rees.GraphStarComparison
import EnvelopingIsomorphism.Deformation.GraphLieGenerators

/-! The actual normalized graph comparisons intertwine their native PBW products.
Only the analytical associativity and unit laws of the specified graph products
are supplied; the Lie-generator maps and completed intertwining equations are proved. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace EnvelopingIsomorphism.Rees.GeometricStarComparison

open FormalSeries CompletedOperator PolynomialCoefficientOperators
open scoped CompletedOperator CompletedPBWProduct LaurentPolynomialCoefficients CompletedPolynomialInputs
open scoped TensorProduct

variable {k : Type*} [Field k] [CharZero k] [Algebra ℝ k] {n : ℕ}

omit [CharZero k] in
theorem scalarMap_real (r : ℝ) :
    GraphPBWScalarBridge.scalarMap k (algebraMap ℝ (Polynomial (Polynomial k)) r) =
      algebraMap ℝ (LaurentPolynomialCoefficients.ScalarRing k) r := by
  simp [Polynomial.algebraMap_apply, GraphPBWScalarBridge.scalarMap_C,
    LaurentPolynomialCoefficients.parameterMap_C, HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

variable
    (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 2)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 2) → Polynomial (Polynomial k))

def targetWeights : (j : ℕ) → Deformation.KontsevichGraph (j + 2) →
    LaurentPolynomialCoefficients.ScalarRing k :=
  fun j Γ ↦ GraphPBWScalarBridge.scalarMap k (w j Γ)

omit [CharZero k] in
theorem map_geometricWeights :
    (fun j Γ ↦ GraphPBWScalarBridge.scalarMap k
      (Deformation.KontsevichGraph.geometricFirstWeights w j Γ)) =
    Deformation.KontsevichGraph.geometricFirstWeights (targetWeights w) := by
  funext j Γ
  cases j with
  | zero => exact scalarMap_real _
  | succ j => rfl

variable {L : Type*} [LieRing L] [LieAlgebra k L]
    {b : Module.Basis (Fin n) k L} (d : WeightData b)

/-- The actual native homogenized Rees basis, over the finite coefficient ring. -/
abbrev scaledBasis :=
  Scaled.basis
    (L := LaurentPolynomialCoefficients.ScalarRing k ⊗[Polynomial k] Family d)
    (LaurentPolynomialCoefficients.hbarPolynomialUnit k : LaurentPolynomialCoefficients.ScalarRing k)
    ((Family.basis d).baseChange (LaurentPolynomialCoefficients.ScalarRing k))

omit [CharZero k] [Algebra ℝ k] in
theorem scaledBasis_coeff (i j r : Fin n) :
    Poisson.structureCoeff (scaledBasis d) i j r =
      GraphPBWScalarBridge.scalarMap k
        (Polynomial.X * GraphStarComparison.tensor d i j r) := by
  rw [Poisson.structureCoeff, scaledBasis, Scaled.structureCoeff,
    Family.baseChange_structureCoeff, map_mul, GraphPBWScalarBridge.scalarMap_X]
  simp only [LaurentPolynomialCoefficients.hbarPolynomialUnit_val,
    GraphStarComparison.tensor, GraphPBWScalarBridge.scalarMap_C,
    LaurentPolynomialCoefficients.algebraMap_parameter]

/-- The only remaining analytical input is the actual graph-product law. -/
abbrev ProductLaws :=
  Deformation.KontsevichGraph.ProductLaws
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights (targetWeights w))
    (Poisson.structureCoeff (scaledBasis d))

def graphFamily : CompletedBinary.Families k (Coordinates (Fin n) k) :=
  CompletedGraphProduct.completedProduct
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights w) (GraphStarComparison.tensor d)

def comparison : (Operators k (Coordinates (Fin n) k))ˣ :=
  GraphStarComparison.comparison
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights w) d

theorem finite_intertwines (laws : ProductLaws s w d)
    (p q : MvPolynomial (Fin n) (LaurentPolynomialCoefficients.ScalarRing k)) :
    GraphPBWScalarBridge.comparisonFinite k
        (Deformation.KontsevichGraph.geometricFirstSets s)
        (Deformation.KontsevichGraph.geometricFirstWeights w) (GraphStarComparison.tensor d)
        (CompletedPBWProduct.homogenizedProduct d p q) =
      CompletedGraphProduct.finiteProduct
        (Deformation.KontsevichGraph.geometricFirstSets s)
        (Deformation.KontsevichGraph.geometricFirstWeights w) (GraphStarComparison.tensor d)
        (GraphPBWScalarBridge.comparisonFinite k
          (Deformation.KontsevichGraph.geometricFirstSets s)
          (Deformation.KontsevichGraph.geometricFirstWeights w) (GraphStarComparison.tensor d) p)
        (GraphPBWScalarBridge.comparisonFinite k
          (Deformation.KontsevichGraph.geometricFirstSets s)
          (Deformation.KontsevichGraph.geometricFirstWeights w) (GraphStarComparison.tensor d) q) := by
  have hc : (fun i j r ↦ GraphPBWScalarBridge.scalarMap k
      (Polynomial.X * GraphStarComparison.tensor d i j r)) =
      Poisson.structureCoeff (scaledBasis d) := by
    funext i j r
    exact (scaledBasis_coeff d i j r).symm
  unfold GraphPBWScalarBridge.comparisonFinite CompletedGraphProduct.finiteProduct
  rw [map_geometricWeights, hc]
  exact Deformation.KontsevichGraph.comparisonMap_symProduct _ _ _ laws (scaledBasis d)
    (Deformation.KontsevichGraph.geometricGeneratorLieHom s (targetWeights w) (scaledBasis d) laws)
    (Deformation.KontsevichGraph.geometricGeneratorLieHom_basis s (targetWeights w) (scaledBasis d) laws) p q

/-- The actual completed comparison intertwines the actual completed products. -/
theorem comparison_intertwines (laws : ProductLaws s w d) :
    StarComparison.Intertwines (comparison s w d)
      (CompletedBinary.binaryAction (CompletedPBWProduct.completedProduct d))
      (CompletedBinary.binaryAction (graphFamily s w d)) := by
  intro x y
  simp only [comparison, GraphStarComparison.comparison, actionEquiv_apply,
    Deformation.KontsevichGraph.comparisonCompletedUnit_val]
  apply CompletedBinary.intertwines_of_constants
  intro p q
  rw [CompletedPBWProduct.completedAction_constants,
    GraphPBWScalarBridge.completedAction_polynomial,
    GraphPBWScalarBridge.completedAction_constant,
    GraphPBWScalarBridge.completedAction_constant]
  change CompletedPolynomialInputs.embed _ =
    CompletedBinary.binaryAction (CompletedGraphProduct.completedProduct _ _ _)
      (CompletedPolynomialInputs.embed _) (CompletedPolynomialInputs.embed _)
  rw [CompletedGraphProduct.completedAction_polynomials, finite_intertwines s w d laws]

section ReesComparison

variable {M : Type*} [LieRing M] [LieAlgebra k M]
    {bM : Module.Basis (Fin n) k M} (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : d.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators d dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM d Φ.symm.toAlgHom)

/-- The canonical graph comparisons and actual completed Rees map give one marked gauge. -/
def gauge : Deformation.Gauge.GaugeUnit
    (LaurentSeries (Module.End k (Coordinates (Fin n) k))) :=
  GraphStarComparison.gauge d dM Φ hw hΦ hΦ'
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights w)

/-- Actual completed graph products are intertwined; both comparison equations
and the middle PBW equation have been proved from their constructions. -/
theorem gauge_intertwines (lawsL : ProductLaws s w d) (lawsM : ProductLaws s w dM) :
    StarComparison.Intertwines (gauge s w d dM Φ hw hΦ hΦ').val
      (CompletedBinary.binaryAction (graphFamily s w d))
      (CompletedBinary.binaryAction (graphFamily s w dM)) :=
  StarComparison.ofRees_intertwines d dM Φ hw hΦ hΦ'
    (comparison s w d) (comparison s w dM) _ _
    (comparison_intertwines s w d lawsL) (comparison_intertwines s w dM lawsM)

/-- This is an equality of the genuine Laurent-cochain families, in the closed
coefficient action used by the formal gauge and Maurer--Cartan infrastructure. -/
theorem gauge_conjugates (lawsL : ProductLaws s w d) (lawsM : ProductLaws s w dM) :
    Deformation.Gauge.LaurentConjugation.conjugateFamily
        (gauge s w d dM Φ hw hΦ hΦ').val (graphFamily s w d) = graphFamily s w dM := by
  apply CompletedBinary.binaryAction_injective
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change CompletedBinary.binaryAction
      (CompletedBinary.post ((gauge s w d dM Φ hw hΦ hΦ').val : Operators k (Coordinates (Fin n) k))
        (CompletedBinary.preRight
          (CompletedBinary.preLeft (graphFamily s w d)
            (↑((gauge s w d dM Φ hw hΦ hΦ').val⁻¹) : Operators k (Coordinates (Fin n) k)))
          (↑((gauge s w d dM Φ hw hΦ hΦ').val⁻¹) : Operators k (Coordinates (Fin n) k)))) x y = _
  rw [CompletedBinary.binaryAction_post, CompletedBinary.binaryAction_preRight,
    CompletedBinary.binaryAction_preLeft]
  change actionEquiv (gauge s w d dM Φ hw hΦ hΦ').val
      (CompletedBinary.binaryAction (graphFamily s w d)
        ((actionEquiv (gauge s w d dM Φ hw hΦ hΦ').val).symm x)
        ((actionEquiv (gauge s w d dM Φ hw hΦ hΦ').val).symm y)) = _
  rw [gauge_intertwines s w d dM Φ hw hΦ hΦ' lawsL lawsM]
  simp only [LinearEquiv.apply_symm_apply]

@[simp] theorem gauge_constantCoeff :
    PowerSeries.constantCoeff (gauge s w d dM Φ hw hΦ hΦ').series = 1 := by
  exact Deformation.Gauge.GaugeUnit.constantCoeff_series
    (R := LaurentSeries (Module.End k (Coordinates (Fin n) k)))
    (gauge s w d dM Φ hw hΦ hΦ')

end ReesComparison

end EnvelopingIsomorphism.Rees.GeometricStarComparison
