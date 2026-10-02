import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Extract actual scalar coefficients of polynomial-linear maps, with all input polynomials
included by the genuine scalar algebra map. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators

variable {k S ι : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- Fixed finite-support monomial coordinates of the polynomial space. -/
abbrev Coordinates (ι k : Type*) [Zero k] := (ι →₀ ℕ) →₀ k

/-- Include an actual polynomial into the coefficient extension. -/
def includePolynomial : Coordinates ι k →ₗ[k] MvPolynomial ι S :=
  (MvPolynomial.mapAlgHom (Algebra.ofId k S)).toLinearMap.comp
    (MvPolynomial.basisMonomials ι k).repr.symm.toLinearMap

@[simp] theorem includePolynomial_single (a : ι →₀ ℕ) :
    includePolynomial (k := k) (S := S) (Finsupp.single a 1) = MvPolynomial.monomial a 1 := by
  change MvPolynomial.map (algebraMap k S) (MvPolynomial.monomial a 1) = _
  rw [MvPolynomial.map_monomial, map_one]

/-- Coefficient extraction is composed with the actual extended-input polynomial map. -/
def coefficientOperator (c : S →ₗ[k] k)
    (f : MvPolynomial ι S →ₗ[S] MvPolynomial ι S) : Module.End k (Coordinates ι k) :=
  (Finsupp.mapRange.linearMap c).comp
    (((MvPolynomial.basisMonomials ι S).repr.toLinearMap.restrictScalars k).comp
      ((f.restrictScalars k).comp (includePolynomial (k := k) (S := S))))

theorem coefficientOperator_apply (c : S →ₗ[k] k)
    (f : MvPolynomial ι S →ₗ[S] MvPolynomial ι S) (p : Coordinates ι k) (m : ι →₀ ℕ) :
    coefficientOperator c f p m = c (MvPolynomial.coeff m (f (includePolynomial (S := S) p))) := rfl

@[simp] theorem coefficientOperator_single (c : S →ₗ[k] k)
    (f : MvPolynomial ι S →ₗ[S] MvPolynomial ι S) (a m : ι →₀ ℕ) :
    coefficientOperator c f (Finsupp.single a 1) m = c (MvPolynomial.coeff m (f (MvPolynomial.monomial a 1))) := by
  rw [coefficientOperator_apply, includePolynomial_single]

/-- Equality of the actual coefficient maps may be checked on the monomial basis. -/
theorem coordinate_end_ext {F G : Module.End k (Coordinates ι k)}
    (h : ∀ a m, F (Finsupp.single a 1) m = G (Finsupp.single a 1) m) : F = G := by
  apply Finsupp.lhom_ext
  intro a c
  rw [← Finsupp.smul_single_one a c, map_smul, map_smul]
  congr 1
  ext m
  exact h a m

end EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators
