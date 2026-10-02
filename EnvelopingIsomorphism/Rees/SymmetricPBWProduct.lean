import EnvelopingIsomorphism.Rees.SymmetricScalarCoordinates
import EnvelopingIsomorphism.PBW.SymmetrizationFiltration
import EnvelopingIsomorphism.Deformation.Cochains

/-! Actual multiplication in symmetric PBW polynomial coordinates. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Rees.SymmetricPBWProduct

open Module Homogenization
open scoped TensorProduct BigOperators

variable {R L M ι κ : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  [LinearOrder ι] [LinearOrder κ]

/-- Transport the native enveloping multiplication through actual PBW symmetrization. -/
def symProduct (b : Basis ι R L) : Deformation.Binary R (MvPolynomial ι R) :=
  ((LinearMap.mul R (UniversalEnvelopingAlgebra R L)).compl₁₂
    (symPolynomialEquiv b).toLinearMap (symPolynomialEquiv b).toLinearMap).compr₂
      (symPolynomialEquiv b).symm.toLinearMap

theorem symProduct_apply (b : Basis ι R L) (p q : MvPolynomial ι R) :
    symProduct b p q = (symPolynomialEquiv b).symm
      (symPolynomialEquiv b p * symPolynomialEquiv b q) := rfl

@[simp] theorem symPolynomialEquiv_product (b : Basis ι R L) (p q : MvPolynomial ι R) :
    symPolynomialEquiv b (symProduct b p q) = symPolynomialEquiv b p * symPolynomialEquiv b q :=
  (symPolynomialEquiv b).apply_symm_apply _

theorem symProduct_assoc (b : Basis ι R L) (p q r : MvPolynomial ι R) :
    symProduct b (symProduct b p q) r = symProduct b p (symProduct b q r) := by
  apply (symPolynomialEquiv b).injective
  simp only [symPolynomialEquiv_product, mul_assoc]

/-- Actual enveloping algebra maps intertwine the actual transported products. -/
theorem symPolynomialMap_product (bL : Basis ι R L) (bM : Basis κ R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (p q : MvPolynomial ι R) :
    symPolynomialMap bL bM Φ (symProduct bL p q) =
      symProduct bM (symPolynomialMap bL bM Φ p) (symPolynomialMap bL bM Φ q) := by
  apply (symPolynomialEquiv bM).injective
  rw [symPolynomialEquiv_product]
  change symPolynomialEquiv bM ((symPolynomialEquiv bM).symm
    (Φ (symPolynomialEquiv bL (symProduct bL p q)))) =
      symPolynomialEquiv bM ((symPolynomialEquiv bM).symm (Φ (symPolynomialEquiv bL p))) *
      symPolynomialEquiv bM ((symPolynomialEquiv bM).symm (Φ (symPolynomialEquiv bL q)))
  simp only [LinearEquiv.apply_symm_apply, symPolynomialEquiv_product, map_mul]

theorem coeff_symProduct_monomial (b : Basis ι R L) (p q m : ι →₀ ℕ) :
    MvPolynomial.coeff m (symProduct b (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) =
      (symBasis b).repr (symBasis b p * symBasis b q) m := by
  rw [symProduct_apply, symPolynomialEquiv_monomial, symPolynomialEquiv_monomial,
    coeff_symPolynomialEquiv_symm]

theorem symPolynomialEquiv_mem (b : Basis ι R L) (p : MvPolynomial ι R) (n : ℕ)
    (hp : ∀ m ∈ p.support, m.degree ≤ n) :
    symPolynomialEquiv b p ∈ PBW.weightedUpper b (fun _ ↦ 1) n := by
  apply PBW.symmetrizationEquiv_mem_weightedUpper b
  simpa [Basis.symmetricAlgebra, MvPolynomial.basisMonomials, MvPolynomial.coeff] using hp

/-- Native multiplication and both directions of symmetrization preserve the ordinary degree. -/
theorem coeff_symProduct_degree (b : Basis ι R L) (p q : MvPolynomial ι R)
    {n l : ℕ} (hp : ∀ m ∈ p.support, m.degree ≤ n) (hq : ∀ m ∈ q.support, m.degree ≤ l)
    {m : ι →₀ ℕ} (hm : MvPolynomial.coeff m (symProduct b p q) ≠ 0) : m.degree ≤ n + l := by
  apply PBW.symmetrizationEquiv_symm_polynomial_support_degree_le b
    (PBW.weightedUpper_mul_le b (fun _ ↦ 1) (fun _ _ _ _ ↦ by decide) n l
      (Submodule.mul_mem_mul (symPolynomialEquiv_mem b p n hp) (symPolynomialEquiv_mem b q l hq)))
  exact MvPolynomial.mem_support_iff.mpr hm

theorem symProduct_totalDegree_le (b : Basis ι R L) (p q : MvPolynomial ι R) :
    (symProduct b p q).totalDegree ≤ p.totalDegree + q.totalDegree := by
  apply Finset.sup_le
  intro m hm
  exact coeff_symProduct_degree b p q
    (fun _ h ↦ MvPolynomial.le_totalDegree h) (fun _ h ↦ MvPolynomial.le_totalDegree h)
    (MvPolynomial.mem_support_iff.mp hm)

theorem coeff_symProduct_monomial_degree (b : Basis ι R L) (p q m : ι →₀ ℕ)
    (hm : MvPolynomial.coeff m
      (symProduct b (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) ≠ 0) :
    m.degree ≤ p.degree + q.degree := by
  apply coeff_symProduct_degree b _ _ (n := p.degree) (l := q.degree) _ _ hm
  · intro a ha
    have h := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
    simp [h]
  · intro a ha
    have h := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
    simp [h]

/-- Scaling the native Lie bracket gives the exact input/output degree factor in multiplication. -/
theorem scaled_monomial_coefficient (u : Rˣ) (b : Basis ι R L) (p q m : ι →₀ ℕ) :
    MvPolynomial.coeff m
      (symProduct (Scaled.basis (u : R) b) (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) =
        unitPower u ((p.degree : ℤ) + (q.degree : ℤ) - (m.degree : ℤ)) *
          MvPolynomial.coeff m
            (symProduct b (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) := by
  rw [coeff_symProduct_monomial, coeff_symProduct_monomial]
  have hprod : symBasis (Scaled.basis (u : R) b) p * symBasis (Scaled.basis (u : R) b) q =
      (scaleEnveloping u L).symm
        ((unitPower u (p.degree : ℤ) • symBasis b p) *
          (unitPower u (q.degree : ℤ) • symBasis b q)) := by
    apply (scaleEnveloping u L).injective
    rw [AlgEquiv.apply_symm_apply, map_mul, scaleEnveloping_symBasis, scaleEnveloping_symBasis]
  rw [hprod, coeff_scaleEnveloping_symm_sym, smul_mul_smul_comm, map_smul,
    Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← unitPower_add]
  rw [← unitPower_add]
  congr 2
  omega

section BaseChange

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra ℚ S] [IsScalarTower ℚ R S]

/-- Actual symmetric-product coefficients extend by the coefficient algebra map. -/
theorem baseChange_monomial_coefficient (b : Basis ι R L) (p q m : ι →₀ ℕ) :
    MvPolynomial.coeff m
      (symProduct (b.baseChange S) (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1)) =
        algebraMap R S (MvPolynomial.coeff m
          (symProduct b (MvPolynomial.monomial p 1) (MvPolynomial.monomial q 1))) := by
  rw [coeff_symProduct_monomial, coeff_symProduct_monomial]
  have hprod : symBasis (b.baseChange S) p * symBasis (b.baseChange S) q =
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).symm
        (1 ⊗ₜ[R] (symBasis b p * symBasis b q)) := by
    apply (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).injective
    rw [AlgEquiv.apply_symm_apply, map_mul,
      SymmetricScalarCoordinates.baseChangeEquiv_symBasis,
      SymmetricScalarCoordinates.baseChangeEquiv_symBasis,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hprod, SymmetricScalarCoordinates.symCoeff_baseChange_symm_one_tmul]

end BaseChange

end EnvelopingIsomorphism.Rees.SymmetricPBWProduct
