import EnvelopingIsomorphism.Rees.SymmetricPBWProduct
import EnvelopingIsomorphism.Rees.Family
import EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators
import EnvelopingIsomorphism.Rees.LaurentPolynomialCoefficients
import EnvelopingIsomorphism.FormalSeries.CompletedBinaryComposition

/-!
# Actual completed PBW product coefficients

The finite product is native enveloping multiplication in genuine symmetric
PBW coordinates. Its homogenized double coefficients form actual binary
cochain series with one uniform nonnegative Laurent bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Rees.CompletedPBWProduct

open Module
open EnvelopingIsomorphism.FormalSeries
open PolynomialCoefficientOperators SymmetricPBWProduct
open scoped BigOperators TensorProduct

section Extraction

variable {k S ι : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- Pin the native additive group on coordinate endomorphisms before forming
the second linear-map level; this avoids the competing endomorphism-ring projection. -/
scoped instance coordinateUnaryGroup : AddCommGroup (Module.End k (Coordinates ι k)) :=
  @LinearMap.addCommGroup k k (Coordinates ι k) (Coordinates ι k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

/-- Extract a scalar coefficient from an actual bilinear polynomial operation. -/
def extractBinary (c : S →ₗ[k] k) (B : Deformation.Binary S (MvPolynomial ι S)) :
    Deformation.Binary k (Coordinates ι k) where
  toFun p := coefficientOperator c (B (includePolynomial (S := S) p))
  map_add' p q := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro m
    change c (MvPolynomial.coeff m (B (includePolynomial (S := S) (p + q))
      (includePolynomial (S := S) x))) =
      c (MvPolynomial.coeff m (B (includePolynomial (S := S) p) (includePolynomial (S := S) x))) +
      c (MvPolynomial.coeff m (B (includePolynomial (S := S) q) (includePolynomial (S := S) x)))
    simp only [map_add, LinearMap.add_apply, MvPolynomial.coeff_add]
  map_smul' a p := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro m
    change c (MvPolynomial.coeff m (B (includePolynomial (S := S) (a • p))
      (includePolynomial (S := S) x))) =
      a • c (MvPolynomial.coeff m (B (includePolynomial (S := S) p) (includePolynomial (S := S) x)))
    rw [map_smul, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      MvPolynomial.coeff_smul, map_smul]

theorem extractBinary_apply (c : S →ₗ[k] k) (B : Deformation.Binary S (MvPolynomial ι S))
    (p q : Coordinates ι k) (m : ι →₀ ℕ) :
    extractBinary c B p q m = c (MvPolynomial.coeff m
      (B (includePolynomial (S := S) p) (includePolynomial (S := S) q))) := rfl

@[simp] theorem extractBinary_single (c : S →ₗ[k] k)
    (B : Deformation.Binary S (MvPolynomial ι S)) (p q m : ι →₀ ℕ) :
    extractBinary c B (Finsupp.single p 1) (Finsupp.single q 1) m =
      c (MvPolynomial.coeff m (B (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1))) := by
  rw [extractBinary_apply, includePolynomial_single, includePolynomial_single]

theorem coordinate_binary_ext {B C : Deformation.Binary k (Coordinates ι k)}
    (h : ∀ p q m, B (Finsupp.single p 1) (Finsupp.single q 1) m =
      C (Finsupp.single p 1) (Finsupp.single q 1) m) : B = C := by
  apply Finsupp.lhom_ext
  intro p a
  rw [← Finsupp.smul_single_one p a, map_smul, map_smul]
  congr 1
  apply Finsupp.lhom_ext
  intro q b
  rw [← Finsupp.smul_single_one q b, map_smul, map_smul]
  congr 1
  apply Finsupp.ext
  intro m
  exact h p q m

end Extraction

section Family

open scoped LaurentPolynomialCoefficients

variable {k ι L : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] {b : Basis ι k L} (d : WeightData b)

/-- The native Rees family's multiplication in actual symmetric polynomial coordinates. -/
def familyProduct : Deformation.Binary (Polynomial k) (MvPolynomial ι (Polynomial k)) :=
  symProduct (Family.basis d)

/-- The finite homogenized native product over the two distinct coefficient parameters. -/
def homogenizedProduct : Deformation.Binary (LaurentPolynomialCoefficients.ScalarRing k)
    (MvPolynomial ι (LaurentPolynomialCoefficients.ScalarRing k)) :=
  symProduct (Scaled.basis
    (L := LaurentPolynomialCoefficients.ScalarRing k ⊗[Polynomial k] Family d)
    (LaurentPolynomialCoefficients.hbarPolynomialUnit k : LaurentPolynomialCoefficients.ScalarRing k)
      ((Family.basis d).baseChange (LaurentPolynomialCoefficients.ScalarRing k)))

theorem homogenized_monomial_coefficient (p q m : ι →₀ ℕ) :
    MvPolynomial.coeff m (homogenizedProduct d (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) =
      Homogenization.unitPower (LaurentPolynomialCoefficients.hbarPolynomialUnit k)
        ((p.degree : ℤ) + (q.degree : ℤ) - (m.degree : ℤ)) *
          algebraMap (Polynomial k) (LaurentPolynomialCoefficients.ScalarRing k)
            (MvPolynomial.coeff m (familyProduct d (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1))) := by
  rw [homogenizedProduct, scaled_monomial_coefficient, baseChange_monomial_coefficient]
  rfl

/-- Each double coefficient is a genuine bilinear map on finite polynomial coordinates. -/
def coefficientBinary (r : ℕ) (j : ℤ) : Deformation.Binary k (Coordinates ι k) :=
  extractBinary (LaurentPolynomialCoefficients.doubleCoeff k r j) (homogenizedProduct d)

@[simp] theorem coefficientBinary_single (r : ℕ) (j : ℤ) (p q m : ι →₀ ℕ) :
    coefficientBinary d r j (Finsupp.single p 1) (Finsupp.single q 1) m =
      if j = (p.degree : ℤ) + (q.degree : ℤ) - (m.degree : ℤ) then
        (MvPolynomial.coeff m
          (familyProduct d (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1))).coeff r else 0 := by
  rw [coefficientBinary, extractBinary_single, homogenized_monomial_coefficient]
  exact LaurentPolynomialCoefficients.doubleCoeff_unitPower_parameter k _ _ r j

/-- The whole coefficient cochain vanishes at every negative Laurent exponent. -/
theorem coefficientBinary_eq_zero_of_neg (r : ℕ) (j : ℤ) (hj : j < 0) : coefficientBinary d r j = 0 := by
  apply coordinate_binary_ext
  intro p q m
  rw [coefficientBinary_single]
  by_cases hdeg : j = (p.degree : ℤ) + (q.degree : ℤ) - (m.degree : ℤ)
  · rw [if_pos hdeg]
    have hz : MvPolynomial.coeff m
        (familyProduct d (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) = 0 := by
      by_contra hn
      have h := coeff_symProduct_monomial_degree (Family.basis d) p q m hn
      omega
    rw [hz]
    rfl
  · rw [if_neg hdeg]
    rfl

/-- A true Laurent series of binary cochains with one common lower bound zero. -/
def laurentProduct (r : ℕ) : LaurentModule k (Deformation.Binary k (Coordinates ι k)) :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (coefficientBinary d r) (by
    refine ⟨0, ?_⟩
    intro j hj
    by_contra h
    exact hj (coefficientBinary_eq_zero_of_neg d r j (lt_of_not_ge h))))

@[simp] theorem coeff_laurentProduct (r : ℕ) (j : ℤ) :
    LaurentModule.coeff (k := k) (X := Deformation.Binary k (Coordinates ι k))
      (laurentProduct d r) j = coefficientBinary d r j := rfl

theorem laurentProduct_nonnegative (r : ℕ) :
    LaurentModule.BoundedBelow (k := k) (X := Deformation.Binary k (Coordinates ι k))
      0 (laurentProduct d r) :=
  fun j hj ↦ coefficientBinary_eq_zero_of_neg d r j hj

/-- The actual two-parameter completed PBW binary product coefficient family. -/
def completedProduct : CompletedBinary.Families k (Coordinates ι k) :=
  PowerSeriesModule.mk (laurentProduct d)

@[simp] theorem completedProduct_coeff (r : ℕ) (j : ℤ) :
    LaurentModule.coeff (k := k) (X := Deformation.Binary k (Coordinates ι k))
      (PowerSeriesModule.coeffV (k := LaurentSeries k)
        (V := LaurentModule k (Deformation.Binary k (Coordinates ι k))) r (completedProduct d)) j =
      coefficientBinary d r j := rfl

theorem completedProduct_nonnegative (r : ℕ) :
    LaurentModule.BoundedBelow (k := k) (X := Deformation.Binary k (Coordinates ι k)) 0
      (PowerSeriesModule.coeffV (k := LaurentSeries k)
        (V := LaurentModule k (Deformation.Binary k (Coordinates ι k))) r (completedProduct d)) :=
  laurentProduct_nonnegative d r

/-- Genuine completed evaluation agrees on every polynomial input with the finite
homogenized native product. The equality is coefficientwise in both parameters. -/
theorem completedProduct_polynomial_inputs (r : ℕ) (j : ℤ)
    (p q : Coordinates ι k) (m : ι →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r
      (CompletedBinary.binaryAction (completedProduct d)
        (CompletedOperator.constant p) (CompletedOperator.constant q))) j m =
      LaurentPolynomialCoefficients.doubleCoeff k r j (MvPolynomial.coeff m
        (homogenizedProduct d
          (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) p)
          (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) q))) := by
  rw [CompletedBinary.coeff_binaryAction_constants, completedProduct_coeff,
    coefficientBinary, extractBinary_apply]

end Family

end EnvelopingIsomorphism.Rees.CompletedPBWProduct
