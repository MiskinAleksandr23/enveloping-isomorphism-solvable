import EnvelopingIsomorphism.Identification.PBWPolynomial
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Coordinate leading operators and Mathlib's actual weighted homogeneous components. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

variable {R σ : Type*} [CommRing R]
open MvPolynomial

theorem polynomial_homogeneous_iff_basis (ω : σ → ℕ) (d : ℕ) (p : MvPolynomial σ R) :
    p.IsWeightedHomogeneous ω d ↔
      p ∈ basisHomogeneous (basisMonomials σ R) (Finsupp.weight ω) d := by
  rw [basisHomogeneous, mem_basisSupport]
  simp only [IsWeightedHomogeneous, Finsupp.mem_support_iff, Set.mem_setOf_eq]
  rfl

theorem weightedComponent_mem_homogeneous (ω : σ → ℕ) (d : ℕ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent ω d p ∈
      basisHomogeneous (basisMonomials σ R) (Finsupp.weight ω) d :=
  (polynomial_homogeneous_iff_basis ω d _).mp (weightedHomogeneousComponent_isWeightedHomogeneous d p)

theorem weightedComponent_remainder_strict (ω : σ → ℕ) (d : ℕ)
    {p : MvPolynomial σ R}
    (hp : p ∈ basisUpper (basisMonomials σ R) (Finsupp.weight ω) d) :
    p - weightedHomogeneousComponent ω d p ∈
      basisStrict (basisMonomials σ R) (Finsupp.weight ω) d := by
  apply (mem_basisSupport (basisMonomials σ R) _ _).mpr
  intro m hm
  have hcoeff := Finsupp.mem_support_iff.mp hm
  change coeff m (p - weightedHomogeneousComponent ω d p) ≠ 0 at hcoeff
  rw [coeff_sub, coeff_weightedHomogeneousComponent] at hcoeff
  split_ifs at hcoeff with heq
  · exact (hcoeff (sub_self _)).elim
  · have hne : coeff m p ≠ 0 := by simpa using hcoeff
    have hle := (mem_basisSupport (basisMonomials σ R) _ _).mp hp m
      (Finsupp.mem_support_iff.mpr hne)
    exact lt_of_le_of_ne hle heq

theorem weightedComponent_eq_zero_of_strict (ω : σ → ℕ) (d : ℕ)
    {p : MvPolynomial σ R}
    (hp : p ∈ basisStrict (basisMonomials σ R) (Finsupp.weight ω) d) :
    weightedHomogeneousComponent ω d p = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro m hm
  exact ne_of_lt ((mem_basisSupport (basisMonomials σ R) _ _).mp hp m hm)

theorem weightedComponent_eq_of_homogeneous_remainder (ω : σ → ℕ) (d : ℕ)
    {p q : MvPolynomial σ R}
    (hq : q ∈ basisHomogeneous (basisMonomials σ R) (Finsupp.weight ω) d)
    (hpq : p - q ∈ basisStrict (basisMonomials σ R) (Finsupp.weight ω) d) :
    weightedHomogeneousComponent ω d p = q := by
  have hzero := weightedComponent_eq_zero_of_strict ω d hpq
  rw [map_sub, ((polynomial_homogeneous_iff_basis ω d q).mpr hq).weightedHomogeneousComponent_same]
    at hzero
  exact sub_eq_zero.mp hzero

theorem leadingOperator_polynomial_homogeneous (ω : σ → ℕ)
    (D : Module.End R (MvPolynomial σ R)) (r : ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsWeightedHomogeneous ω d) :
    leadingOperator (basisMonomials σ R) (Finsupp.weight ω) D r p =
      weightedHomogeneousComponent ω (d + r) (D p) := by
  let E := leadingOperator (basisMonomials σ R) (Finsupp.weight ω) D r
  let F := (weightedHomogeneousComponent ω (d + r)).comp D
  have hker : basisHomogeneous (basisMonomials σ R) (Finsupp.weight ω) d ≤
      LinearMap.ker (E - F) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    change E ((basisMonomials σ R) m) - F ((basisMonomials σ R) m) = 0
    apply sub_eq_zero.mpr
    ext n
    change ((basisMonomials σ R).repr (E ((basisMonomials σ R) m))) n = _
    rw [repr_leadingOperator_basis, Finsupp.filter_apply]
    change (if Finsupp.weight ω n = Finsupp.weight ω m + r then _ else 0) =
      coeff n (weightedHomogeneousComponent ω (d + r) (D ((basisMonomials σ R) m)))
    rw [coeff_weightedHomogeneousComponent]
    change Finsupp.weight ω m = d at hm
    rw [hm]
    rfl
  exact sub_eq_zero.mp (hker ((polynomial_homogeneous_iff_basis ω d p).mp hp))

/-- Standard multiplication as a bilinear map, for the generic leading-product theorem. -/
def polynomialProduct : MvPolynomial σ R →ₗ[R] MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  LinearMap.mul R (MvPolynomial σ R)

def polynomialLeadingDerivation (ω : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (r : ℕ)
    (hshift : ∀ m, D ((basisMonomials σ R) m) ∈
      basisUpper (basisMonomials σ R) (Finsupp.weight ω) (Finsupp.weight ω m + r)) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  leadingDerivationOfFilteredProduct (basisMonomials σ R) (Finsupp.weight ω)
    (polynomial_basis_mul_homogeneous ω) polynomialProduct
    (fun _ _ _ _ _ _ => by simp [polynomialProduct])
    D.toLinearMap r hshift (fun p q => by
      simpa only [polynomialProduct, LinearMap.mul_apply', Derivation.coeFn_coe,
        smul_eq_mul, mul_comm, add_comm] using
        D.leibniz p q)

theorem polynomialLeadingDerivation_isLocallyNilpotent (ω : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (r : ℕ) (hr : 0 < r)
    (hshift : ∀ m, D ((basisMonomials σ R) m) ∈
      basisUpper (basisMonomials σ R) (Finsupp.weight ω) (Finsupp.weight ω m + r))
    (hD : IsLocallyFinite D.toLinearMap) :
    IsLocallyNilpotent (polynomialLeadingDerivation ω D r hshift).toLinearMap :=
  leadingOperator_isLocallyNilpotent (basisMonomials σ R) (Finsupp.weight ω) D.toLinearMap r hr hD hshift

end EnvelopingIsomorphism.Identification
