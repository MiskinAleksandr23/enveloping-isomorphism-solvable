import EnvelopingIsomorphism.Deformation.PolynomialGraphProduct
import EnvelopingIsomorphism.Deformation.GraphLinearParameters

/-! Extracting the inner parameter from the actual finite graph product.
Each graph order is separated by its proved homogeneity in the input tensors. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.GraphHbarCoefficients

open Deformation.KontsevichGraph
open scoped BigOperators

variable {R : Type*} [CommRing R] {d : ℕ}

theorem coeff_X_pow_smul_map (p : MvPolynomial (Fin d) R)
    (n h : ℕ) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m ((Polynomial.X ^ n : Polynomial R) •
      MvPolynomial.map Polynomial.C p)).coeff h =
      if h = n then MvPolynomial.coeff m p else 0 := by
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
    mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  simp only [eq_comm]

variable (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 1)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R)

/-- Actual homogeneity and scalar naturality give the finite expansion, without
an assumption that graph order equals parameter degree. -/
theorem finiteStar_scaled (N : ℕ) (p q : MvPolynomial (Fin d) R) :
    finiteStarOperator N s (fun j Γ ↦ Polynomial.C (w j Γ))
        (fun i j r ↦ Polynomial.X * Polynomial.C (c i j r))
        (MvPolynomial.map Polynomial.C p) (MvPolynomial.map Polynomial.C q) =
      MvPolynomial.map Polynomial.C (p * q) +
        ∑ j ∈ Finset.range N, (Polynomial.X ^ (j + 1) : Polynomial R) •
          MvPolynomial.map Polynomial.C (weightedOperator (s j) (w j) (fun _ ↦ c) p q) := by
  simp only [finiteStarOperator, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.mul_apply', map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [weightedOperator_mul_coefficients]
  congr 1
  exact (map_weightedOperator Polynomial.C (s j) (w j) (fun _ ↦ c) p q).symm

theorem finiteStar_coeff_zero (N : ℕ) (p q : MvPolynomial (Fin d) R) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (finiteStarOperator N s (fun j Γ ↦ Polynomial.C (w j Γ))
      (fun i j r ↦ Polynomial.X * Polynomial.C (c i j r))
      (MvPolynomial.map Polynomial.C p) (MvPolynomial.map Polynomial.C q))).coeff 0 =
      MvPolynomial.coeff m (p * q) := by
  rw [finiteStar_scaled]
  have hz : ∀ j : ℕ, ¬ 0 = j + 1 := by omega
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, coeff_X_pow_smul_map, MvPolynomial.coeff_map,
    Polynomial.coeff_C, ite_true, hz, ite_false,
    Finset.sum_const_zero, add_zero]

theorem finiteStar_coeff_succ (N n : ℕ) (p q : MvPolynomial (Fin d) R) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (finiteStarOperator N s (fun j Γ ↦ Polynomial.C (w j Γ))
      (fun i j r ↦ Polynomial.X * Polynomial.C (c i j r))
      (MvPolynomial.map Polynomial.C p) (MvPolynomial.map Polynomial.C q))).coeff (n + 1) =
      if n < N then MvPolynomial.coeff m (weightedOperator (s n) (w n) (fun _ ↦ c) p q) else 0 := by
  classical
  rw [finiteStar_scaled]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, coeff_X_pow_smul_map, MvPolynomial.coeff_map,
    Polynomial.coeff_C, Nat.add_one_ne_zero, ite_false, zero_add,
    Nat.add_right_cancel_iff]
  simp

variable [Nontrivial R]

omit [Nontrivial R] in
/-- The order-zero coefficient of the actual all-orders polynomial product is ordinary multiplication. -/
theorem polynomialProduct_coeff_zero (p q : MvPolynomial (Fin d) R) (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (polynomialProduct s (fun j Γ ↦ Polynomial.C (w j Γ))
      (fun i j r ↦ Polynomial.X * Polynomial.C (c i j r))
      (MvPolynomial.map Polynomial.C p) (MvPolynomial.map Polynomial.C q))).coeff 0 =
      MvPolynomial.coeff m (p * q) := by
  rw [polynomialProduct]
  exact finiteStar_coeff_zero s w c _ p q m

/-- Each positive inner coefficient of the all-orders product is exactly the
specified effective weighted graph operator at that order. -/
theorem polynomialProduct_coeff_succ (n : ℕ) (p q : MvPolynomial (Fin d) R)
    (m : Fin d →₀ ℕ) :
    (MvPolynomial.coeff m (polynomialProduct s (fun j Γ ↦ Polynomial.C (w j Γ))
      (fun i j r ↦ Polynomial.X * Polynomial.C (c i j r))
      (MvPolynomial.map Polynomial.C p) (MvPolynomial.map Polynomial.C q))).coeff (n + 1) =
      MvPolynomial.coeff m (weightedOperator (s n) (w n) (fun _ ↦ c) p q) := by
  let N := p.totalDegree + q.totalDegree + (n + 1)
  have hN : (MvPolynomial.map Polynomial.C p).totalDegree +
      (MvPolynomial.map Polynomial.C q).totalDegree ≤ N := by
    exact (Nat.add_le_add (totalDegree_map_coefficients_le Polynomial.C p)
      (totalDegree_map_coefficients_le Polynomial.C q)).trans (Nat.le_add_right _ _)
  rw [polynomialProduct_eq_finiteStarOperator _ _ _ _ _ N hN,
    finiteStar_coeff_succ, if_pos]
  dsimp [N]
  omega

end EnvelopingIsomorphism.Rees.GraphHbarCoefficients
