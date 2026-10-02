import EnvelopingIsomorphism.Identification.PolynomialVectorField

/-! Intertwining polynomial vector fields with actual native inner derivations. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open MvPolynomial
variable {k A σ β : Type*} [Field k] [Ring A] [Algebra k A]
attribute [local instance 100] LieRing.ofAssociativeRing

theorem algHom_polynomials_commute (φ : MvPolynomial σ k →ₐ[k] A)
    (p q : MvPolynomial σ k) : Commute (φ p) (φ q) := by
  change φ p * φ q = φ q * φ p
  rw [← map_mul, ← map_mul, mul_comm p q]

theorem algHom_polynomials_lie_eq_zero (φ : MvPolynomial σ k →ₐ[k] A)
    (p q : MvPolynomial σ k) : ⁅φ p, φ q⁆ = 0 := by
  rw [Ring.lie_def, (algHom_polynomials_commute φ p q).eq, sub_self]

/-- Equality on polynomial variables extends the actual inner-derivation
intertwining to every polynomial. -/
theorem algHom_intertwines_polynomial_derivation_inner
    (φ : MvPolynomial σ k →ₐ[k] A)
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (a : A)
    (hX : ∀ i, φ (D (X i)) = ⁅a, φ (X i)⁆) :
    ∀ p, φ (D p) = ⁅a, φ p⁆ := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.derivation_C, map_zero]
    change 0 = ⁅a, φ (algebraMap k (MvPolynomial σ k) r)⁆
    rw [φ.commutes]
    simp [Ring.lie_def, Algebra.commutes]
  | add p q hp hq => simp only [map_add, hp, hq, lie_add]
  | mul_X p i hp =>
    rw [D.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hp, hX]
    have hcomm := (algHom_polynomials_commute φ (X i) (D p)).eq
    rw [hp] at hcomm
    simp only [Ring.lie_def] at hcomm ⊢
    simp only [mul_sub, sub_mul, mul_assoc] at hcomm ⊢
    rw [hcomm]
    abel

theorem lie_mul_left_of_commute (p q a : A) (hpq : Commute p q) :
    ⁅p * a, q⁆ = p * ⁅a, q⁆ := by
  simp only [Ring.lie_def, mul_sub, mul_assoc]
  rw [← mul_assoc q p a, hpq.eq.symm, mul_assoc]

variable [Fintype β]

/-- The actual affine polynomial expression acts on the polynomial subalgebra
as the polynomial vector field formed from its true coefficients. -/
theorem polynomialVectorField_intertwines_inner
    (φ : MvPolynomial σ k →ₐ[k] A)
    (p : β → MvPolynomial σ k) (p₀ : MvPolynomial σ k) (t : β → A)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hδ : ∀ i x, φ (δ i x) = ⁅t i, φ x⁆) :
    ∀ x, φ (polynomialVectorField p δ x) =
      ⁅φ p₀ + ∑ i, φ (p i) * t i, φ x⁆ := by
  intro x
  rw [polynomialVectorField_apply, map_sum, add_lie, algHom_polynomials_lie_eq_zero, zero_add,
    sum_lie]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, hδ,
    lie_mul_left_of_commute _ _ _ (algHom_polynomials_commute φ (p i) x)]

/-- Local finiteness transfers from the actual ambient inner derivation to
its polynomial vector field through an injective polynomial embedding. -/
theorem polynomialVectorField_isLocallyFinite_of_inner
    (φ : MvPolynomial σ k →ₐ[k] A) (hφ : Function.Injective φ)
    (p : β → MvPolynomial σ k) (p₀ : MvPolynomial σ k) (t : β → A)
    (δ : β → Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hδ : ∀ i x, φ (δ i x) = ⁅t i, φ x⁆)
    (hLF : φ p₀ + ∑ i, φ (p i) * t i ∈ LF k A) :
    IsLocallyFinite (polynomialVectorField p δ).toLinearMap := by
  apply locallyFinite_of_injective_intertwiner _ _ φ.toLinearMap _ hφ hLF
  exact polynomialVectorField_intertwines_inner φ p p₀ t δ hδ

end EnvelopingIsomorphism.Identification
