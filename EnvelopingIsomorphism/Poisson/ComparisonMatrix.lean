import EnvelopingIsomorphism.ComparisonReduction
import EnvelopingIsomorphism.Poisson.CompletedFirstJet

/-!
# From a completed Poisson comparison to the exact G–H matrix interface

These constructions take an actual scalar algebra homomorphism and proved
Poisson/marking identities. They do not assert that such a homomorphism exists.
The function algebra is the genuine iterated completion from `CompletedFirstJet`.
-/

noncomputable section

namespace EnvelopingIsomorphism.Poisson.ComparisonMatrix

open EnvelopingIsomorphism.FormalSeries
open scoped TensorProduct LaurentAlgebra

universe v w
variable {L : Type v} {M : Type w}
  [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
  (D : Identification.RecoveredData ℂ L M)

-- Keep the Rees polynomial variable equal to the outer power-series parameter.
local instance comparisonScalarPolynomialModule :
    Module (Polynomial ℂ) (Completed.Scalars ℂ) := Algebra.toModule

/-- Actual source Rees coefficients in `ℂ((h))[[t]]`. -/
def sourceCoefficients : Fin D.size → Fin D.size → Fin D.size → Completed.Scalars ℂ :=
  structureCoeff (R := Completed.Scalars ℂ)
    (L := Completed.Scalars ℂ ⊗[Polynomial ℂ] Rees.Family D.sourceWeightData)
    ((Rees.Family.basis D.sourceWeightData).baseChange (Completed.Scalars ℂ))

/-- Actual target Rees coefficients in the same scalar ring. -/
def targetCoefficients : Fin D.size → Fin D.size → Fin D.size → Completed.Scalars ℂ :=
  structureCoeff (R := Completed.Scalars ℂ)
    (L := Completed.Scalars ℂ ⊗[Polynomial ℂ] Rees.Family D.targetWeightData)
    ((Rees.Family.basis D.targetWeightData).baseChange (Completed.Scalars ℂ))

/-- The completed first jet produces exactly the marked native matrix requested by `ComparisonHypothesis`. -/
def ofCompletedPoisson
    (Ψ : Completed.Functions (Fin D.size) ℂ →ₐ[Completed.Scalars ℂ]
      Completed.Functions (Fin D.size) ℂ)
    (hΨ : ∀ p q, Ψ (Completed.bracket (sourceCoefficients D) p q) =
      Completed.bracket (targetCoefficients D) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (Completed.coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) : ReesMatrixComparison D where
  matrix := Completed.matrix Ψ
  constantCoeff := Completed.matrix_constantCoeff Ψ hmark
  bracket := Completed.matrix_equation
    ((Rees.Family.basis D.sourceWeightData).baseChange (Completed.Scalars ℂ))
    ((Rees.Family.basis D.targetWeightData).baseChange (Completed.Scalars ℂ)) Ψ hΨ

@[simp]
theorem ofCompletedPoisson_matrix
    (Ψ : Completed.Functions (Fin D.size) ℂ →ₐ[Completed.Scalars ℂ]
      Completed.Functions (Fin D.size) ℂ)
    (hΨ : ∀ p q, Ψ (Completed.bracket (sourceCoefficients D) p q) =
      Completed.bracket (targetCoefficients D) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (Completed.coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) :
    (ofCompletedPoisson D Ψ hΨ hmark).matrix = Completed.matrix Ψ := rfl

/-- An invertible common scalar in front of the Poisson structures can be cancelled. -/
def ofUnitScaledCompletedPoisson
    (Ψ : Completed.Functions (Fin D.size) ℂ →ₐ[Completed.Scalars ℂ]
      Completed.Functions (Fin D.size) ℂ)
    (s : Completed.Scalars ℂ) (hs : IsUnit s)
    (hΨ : ∀ p q, Ψ (s • Completed.bracket (sourceCoefficients D) p q) =
      s • Completed.bracket (targetCoefficients D) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (Completed.coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) : ReesMatrixComparison D :=
  ofCompletedPoisson D Ψ
    (Completed.poisson_of_unit_scaled (sourceCoefficients D) (targetCoefficients D) Ψ s hs hΨ) hmark

/-- The inner Laurent parameter, viewed as a constant outer power series. -/
def hbar : Completed.Scalars ℂ :=
  PowerSeries.C (HahnSeries.single (1 : ℤ) (1 : ℂ) : LaurentSeries ℂ)

theorem isUnit_hbar : IsUnit hbar := by
  have h : IsUnit (HahnSeries.single (1 : ℤ) (1 : ℂ) : LaurentSeries ℂ) :=
    isUnit_iff_ne_zero.mpr (by simp)
  exact h.map PowerSeries.C

/-- The `hπ` comparison produced by deformation theory supplies the same actual first-jet matrix. -/
def ofHbarScaledCompletedPoisson
    (Ψ : Completed.Functions (Fin D.size) ℂ →ₐ[Completed.Scalars ℂ]
      Completed.Functions (Fin D.size) ℂ)
    (hΨ : ∀ p q, Ψ (hbar • Completed.bracket (sourceCoefficients D) p q) =
      hbar • Completed.bracket (targetCoefficients D) (Ψ p) (Ψ q))
    (hmark : ∀ i, PowerSeries.constantCoeff (Ψ (Completed.coordinate i)) =
      HahnSeries.C (MvPolynomial.X i)) : ReesMatrixComparison D :=
  ofUnitScaledCompletedPoisson D Ψ hbar isUnit_hbar hΨ hmark

end EnvelopingIsomorphism.Poisson.ComparisonMatrix
