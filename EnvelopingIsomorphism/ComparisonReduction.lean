import EnvelopingIsomorphism.FieldTheory.CountableReduction
import EnvelopingIsomorphism.Identification.RecoveredData
import EnvelopingIsomorphism.Descent.ReesSpecialization
import EnvelopingIsomorphism.Descent.MarkedGaloisDescent

/-!
# Conditional reduction to one marked comparison matrix over the complex numbers

`ComparisonHypothesis` is the remaining E–F–G producer obligation. It is not
proved or introduced as an axiom here. This file proves that this one explicit
hypothesis implies the full identification statement, using the already constructed
recovered data and the actual marked descent theorems.
-/

noncomputable section

namespace EnvelopingIsomorphism

open scoped TensorProduct BigOperators

universe u v w

section Matrix

variable {L : Type v} {M : Type w}
  [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]

-- The polynomial variable is the outer power-series parameter, not the Laurent parameter.
local instance comparisonScalarPolynomialModule :
    Module (Polynomial ℂ) (PowerSeries (LaurentSeries ℂ)) := Algebra.toModule

/-- The Rees polynomial parameter acts as the outer power-series variable. -/
theorem comparisonScalar_X_smul_one :
    (Polynomial.X : Polynomial ℂ) • (1 : PowerSeries (LaurentSeries ℂ)) = PowerSeries.X := by
  rw [Algebra.smul_def, mul_one, PowerSeries.algebraMap_apply']
  simp

/-- Precisely the marked native Rees matrix needed from the comparison argument.
Invertibility is a consequence of the constant coefficient, and is not an extra field. -/
structure ReesMatrixComparison (D : Identification.RecoveredData ℂ L M) where
  matrix : Matrix (Fin D.size) (Fin D.size) (PowerSeries (LaurentSeries ℂ))
  constantCoeff : matrix.map PowerSeries.constantCoeff = 1
  bracket : ∀ i j r,
    (∑ a, ∑ b,
      Poisson.structureCoeff (R := PowerSeries (LaurentSeries ℂ))
        (L := PowerSeries (LaurentSeries ℂ) ⊗[Polynomial ℂ] Rees.Family D.targetWeightData)
        ((Rees.Family.basis D.targetWeightData).baseChange (PowerSeries (LaurentSeries ℂ))) a b r *
          (matrix a i * matrix b j)) =
    ∑ d, Poisson.structureCoeff (R := PowerSeries (LaurentSeries ℂ))
        (L := PowerSeries (LaurentSeries ℂ) ⊗[Polynomial ℂ] Rees.Family D.sourceWeightData)
        ((Rees.Family.basis D.sourceWeightData).baseChange (PowerSeries (LaurentSeries ℂ))) i j d *
          matrix r d

namespace ReesMatrixComparison

/-- The real H1–H4 theorems turn the comparison matrix into a marked native complex Lie equivalence. -/
theorem exists_marked_complex_lieEquiv {D : Identification.RecoveredData ℂ L M}
    (P : ReesMatrixComparison D) :
    ∃ f : L ≃ₗ⁅ℂ⁆ M,
      Descent.IsMarkedMap D.sourceBasis D.targetBasis D.weight f.toLinearMap := by
  letI : Module.Finite ℂ L := Module.Finite.of_basis D.sourceBasis
  letI : Module.Finite ℂ M := Module.Finite.of_basis D.targetBasis
  obtain ⟨f, hf⟩ := Descent.MatrixGroup.exists_marked_native_isomorphism_of_family_matrix
    (E := LaurentSeries ℂ) D.sourceBasis D.targetBasis D.sourceWeightData D.targetWeightData
    rfl D.source_adapted D.target_adapted P.matrix P.constantCoeff P.bracket
  exact ⟨f, hf⟩

end ReesMatrixComparison
end Matrix

/-- The single unproved comparison producer, restricted to the complex numbers.

The carrier universe `u` is needed for scalar extensions of the countable
coordinate models. No finiteness, solvability, filtration, or scalar-descent
premises are added: the input is already genuine `RecoveredData`.
-/
def ComparisonHypothesis : Prop :=
  ∀ (L M : Type u) [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
    (D : Identification.RecoveredData ℂ L M), Nonempty (ReesMatrixComparison D)

/-- The comparison hypothesis gives identification over every countable characteristic-zero field.
The same recovered bases and marking are extended to the complex numbers and then descended. -/
theorem countable_of_comparison (h : ComparisonHypothesis.{u}) : CountableStatement.{u} := by
  intro k _ _ _ L _ _ _ M _ _ _ hL φ
  haveI : LieAlgebra.IsSolvable L := hL
  let σ : k →+* ℂ := FieldTheory.complexEmbeddingOfCountable k
  letI : Algebra k ℂ := σ.toAlgebra
  let D := Identification.recoveredData φ
  let DC := D.baseChange ℂ
  obtain ⟨P⟩ := h (ℂ ⊗[k] L) (ℂ ⊗[k] M) DC
  obtain ⟨f, hf⟩ := P.exists_marked_complex_lieEquiv
  have hmarked : Descent.IsMarkedMap (D.sourceBasis.baseChange ℂ)
      (D.targetBasis.baseChange ℂ) D.weight f.toLinearMap := hf
  obtain ⟨g, hg⟩ := Descent.exists_marked_lieEquiv_of_extension
    (E := ℂ) D.sourceBasis D.targetBasis D.weight f hmarked
  exact ⟨g⟩

/-- Conditional assembly of the full statement from the one remaining complex comparison producer.
This theorem does not prove `ComparisonHypothesis`. -/
theorem of_comparison (h : ComparisonHypothesis.{u}) : Statement.{u, v, w} :=
  of_countable (countable_of_comparison h)

end EnvelopingIsomorphism
