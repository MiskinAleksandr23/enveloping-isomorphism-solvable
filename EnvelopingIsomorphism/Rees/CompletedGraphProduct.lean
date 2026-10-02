import EnvelopingIsomorphism.Rees.CompletedPBWProduct
import EnvelopingIsomorphism.Rees.GraphPBWScalarBridge

/-! Complete the actual finite graph product in the prescribed two parameters.
The Laurent lower bound is proved for each entire binary-cochain coefficient,
using the same polynomial graph formula before coefficient extension. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Rees.CompletedGraphProduct

open FormalSeries CompletedOperator PolynomialCoefficientOperators CompletedPBWProduct
open scoped CompletedOperator CompletedPBWProduct LaurentPolynomialCoefficients CompletedPolynomialInputs

variable {k : Type*} [Field k] {d : ℕ}
    (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 1)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 1) → Polynomial (Polynomial k))
    (c : Fin d → Fin d → Fin d → Polynomial (Polynomial k))

/-- The finite graph product with the single inner parameter factor on its tensor. -/
def sourceProduct : Deformation.Binary (Polynomial (Polynomial k))
    (MvPolynomial (Fin d) (Polynomial (Polynomial k))) :=
  Deformation.KontsevichGraph.polynomialProductBilinear s w
    (fun i j r ↦ Polynomial.X * c i j r)

/-- The same finite graph product over the Laurent-polynomial scalar ring. -/
def finiteProduct : Deformation.Binary (LaurentPolynomialCoefficients.ScalarRing k)
    (MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k)) :=
  Deformation.KontsevichGraph.polynomialProductBilinear s
    (fun n Γ ↦ GraphPBWScalarBridge.scalarMap k (w n Γ))
    (fun i j r ↦ GraphPBWScalarBridge.scalarMap k (Polynomial.X * c i j r))

/-- The finite source and target products are related by the actual parameter map. -/
theorem map_sourceProduct
    (p q : MvPolynomial (Fin d) (Polynomial (Polynomial k))) :
    MvPolynomial.map (GraphPBWScalarBridge.scalarMap k) (sourceProduct s w c p q) =
      finiteProduct s w c
        (MvPolynomial.map (GraphPBWScalarBridge.scalarMap k) p)
        (MvPolynomial.map (GraphPBWScalarBridge.scalarMap k) q) := by
  unfold sourceProduct finiteProduct
  simp only [Deformation.KontsevichGraph.polynomialProductBilinear_apply]
  exact Deformation.KontsevichGraph.map_polynomialProduct s w
    (fun i j r ↦ Polynomial.X * c i j r) (GraphPBWScalarBridge.scalarMap k) p q

def coefficientBinary (r : ℕ) (j : ℤ) :
    Deformation.Binary k (Coordinates (Fin d) k) :=
  extractBinary (LaurentPolynomialCoefficients.doubleCoeff k r j) (finiteProduct s w c)

theorem coefficientBinary_apply (r : ℕ) (j : ℤ)
    (p q : Coordinates (Fin d) k) (m : Fin d →₀ ℕ) :
    coefficientBinary s w c r j p q m =
      LaurentPolynomialCoefficients.doubleCoeff k r j (MvPolynomial.coeff m
        (finiteProduct s w c (includePolynomial p) (includePolynomial q))) := rfl

/-- The coefficient is read from the very same finite graph expression over `k[t][h]`. -/
theorem coefficientBinary_source (r : ℕ) (j : ℤ)
    (p q : Coordinates (Fin d) k) (m : Fin d →₀ ℕ) :
    coefficientBinary s w c r j p q m =
      if j < 0 then 0 else
        ((MvPolynomial.coeff m (sourceProduct s w c
          (includePolynomial p) (includePolynomial q))).coeff j.natAbs).coeff r := by
  rw [coefficientBinary_apply]
  have he := congrArg (MvPolynomial.coeff m)
    (map_sourceProduct s w c
      (includePolynomial (S := Polynomial (Polynomial k)) p)
      (includePolynomial (S := Polynomial (Polynomial k)) q))
  simp only [MvPolynomial.coeff_map, GraphPBWScalarBridge.map_includePolynomial] at he
  rw [← he, GraphPBWScalarBridge.doubleCoeff_scalarMap]

/-- Negative inner exponents vanish as entire binary operators, uniformly in the inputs. -/
theorem coefficientBinary_eq_zero_of_neg (r : ℕ) (j : ℤ) (hj : j < 0) :
    coefficientBinary s w c r j = 0 := by
  apply coordinate_binary_ext
  intro p q m
  rw [coefficientBinary_source, if_pos hj]
  rfl

def laurentProduct (r : ℕ) : LaurentModule k (Deformation.Binary k (Coordinates (Fin d) k)) :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (coefficientBinary s w c r) (by
    refine ⟨0, ?_⟩
    intro j hj
    by_contra h
    exact hj (coefficientBinary_eq_zero_of_neg s w c r j (lt_of_not_ge h))))

@[simp] theorem coeff_laurentProduct (r : ℕ) (j : ℤ) :
    LaurentModule.coeff (laurentProduct s w c r) j = coefficientBinary s w c r j := rfl

/-- The actual graph binary family, in the full Laurent-cochain target of F11. -/
def completedProduct : CompletedBinary.Families k (Coordinates (Fin d) k) :=
  PowerSeriesModule.mk (laurentProduct s w c)

@[simp] theorem completedProduct_coeff (r : ℕ) (j : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r (completedProduct s w c)) j =
      coefficientBinary s w c r j := rfl

theorem completedProduct_nonnegative (r : ℕ) :
    LaurentModule.BoundedBelow 0 (PowerSeriesModule.coeffV r (completedProduct s w c)) :=
  fun j hj ↦ coefficientBinary_eq_zero_of_neg s w c r j hj

theorem completedProduct_polynomial_inputs (r : ℕ) (j : ℤ)
    (p q : Coordinates (Fin d) k) (m : Fin d →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r
      (CompletedBinary.binaryAction (completedProduct s w c) (constant p) (constant q))) j m =
      LaurentPolynomialCoefficients.doubleCoeff k r j (MvPolynomial.coeff m
        (finiteProduct s w c (includePolynomial p) (includePolynomial q))) := by
  rw [CompletedBinary.coeff_binaryAction_constants, completedProduct_coeff,
    coefficientBinary_apply]

theorem completedAction_constants (p q : Coordinates (Fin d) k) :
    CompletedBinary.binaryAction (completedProduct s w c) (constant p) (constant q) =
      CompletedPolynomialInputs.embed
        (finiteProduct s w c (includePolynomial p) (includePolynomial q)) := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply Finsupp.ext
  intro m
  rw [CompletedPolynomialInputs.coeff_embed]
  exact completedProduct_polynomial_inputs s w c r j p q m

theorem completedAction_polynomials
    (p q : MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k)) :
    CompletedBinary.binaryAction (completedProduct s w c)
        (CompletedPolynomialInputs.embed p) (CompletedPolynomialInputs.embed q) =
      CompletedPolynomialInputs.embed (finiteProduct s w c p q) :=
  CompletedPolynomialInputs.bilinear_extension _ _ (completedAction_constants s w c) p q

end EnvelopingIsomorphism.Rees.CompletedGraphProduct
