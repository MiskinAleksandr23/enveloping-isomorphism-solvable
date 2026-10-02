import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant

/-!
# Exact radial gain in a boundary-tangent determinant

The first stage is a purely algebraic column factorization. Its hypotheses
describe actual matrix entries, so the radial factor is retained before any
estimate or substitution of inverse radial parameters.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RadialBoundaryDeterminant

open scoped BigOperators Classical

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- Dividing one column by its displayed radial factor gives an exact
determinant identity, valid also when that factor is zero. -/
theorem det_factor_column (M N : Matrix I I R) (j₀ : I) (r : R) (b : I → R)
    (hM : ∀ i, M i j₀ = r * b i) (hN : ∀ i, N i j₀ = b i)
    (hrest : ∀ i j, j ≠ j₀ → M i j = N i j) : M.det = r * N.det := by
  have hupdate : M = N.updateCol j₀ (r • b) := by
    ext i j
    by_cases hj : j = j₀
    · subst j
      simpa only [Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul] using hM i
    · simpa only [Matrix.updateCol_ne hj] using hrest i j hj
  have hself : N.updateCol j₀ b = N := by
    ext i j
    by_cases hj : j = j₀
    · subst j
      simpa only [Matrix.updateCol_self] using (hN i).symm
    · simp only [Matrix.updateCol_ne hj]
  rw [hupdate, Matrix.det_updateCol_smul, hself]

theorem prod_max_update_zero {J : Type*} [Fintype J] [DecidableEq J]
    (t : J → ℝ) (ν₀ : J) :
    (∏ ν, max 1 (Function.update t ν₀ 0 ν)) =
      ∏ ν ∈ Finset.univ.erase ν₀, max 1 (t ν) := by
  rw [← Finset.prod_erase_mul Finset.univ (fun ν => max 1 (Function.update t ν₀ 0 ν))
    (Finset.mem_univ ν₀)]
  simp only [Function.update_self, max_eq_left zero_le_one, mul_one]
  apply Finset.prod_congr rfl
  intro ν hν
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]

section RadialRows

variable {J : Type*} [Fintype J] [DecidableEq J]

open RadialPoleDeterminant (matrix coefficientBound)

omit [Fintype I] [DecidableEq I] in
/-- A radial covector vanishing on the entire frame contributes nothing,
even if its formal singular parameter is arbitrarily large. -/
theorem matrix_update_zero_pole (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) (ν₀ : J) (hρ : ρ ν₀ = 0) :
    matrix B ρ c (Function.update t ν₀ 0) = matrix B ρ c t := by
  ext i j
  simp only [matrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hν : ν = ν₀
  · subst ν
    simp only [hρ, Pi.zero_apply, mul_zero]
  · rw [Function.update_of_ne hν]

omit [DecidableEq J] in
/-- All radial rows annihilate the angular tangent, so only the smooth
column supplies its factor r. This identity is valid also at r=0. -/
theorem det_eq_radius_mul (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) (j₀ : I) (r : R) (b : I → R)
    (hB : ∀ i, B i j₀ = r * b i) (hρ : ∀ ν, ρ ν j₀ = 0) :
    Matrix.det (matrix B ρ c t) = r * Matrix.det (matrix (B.updateCol j₀ b) ρ c t) := by
  apply det_factor_column _ _ j₀ r b
  · intro i
    simpa only [matrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hρ, mul_zero, Finset.sum_const_zero, add_zero] using hB i
  · intro i
    simp only [matrix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hρ, mul_zero, Finset.sum_const_zero, add_zero, Matrix.updateCol_self]
  · intro i j hj
    simp only [matrix, Pi.add_apply, Matrix.updateCol_ne hj]

/-- Exact factorization after deleting the distinguished radial pole from
the coefficient list. No inverse-radius substitution is made. -/
theorem det_eq_radius_mul_without_pole (B : Matrix I I R) (ρ : J → I → R)
    (c : I → J → R) (t : J → R) (j₀ : I) (ν₀ : J) (r : R) (b : I → R)
    (hB : ∀ i, B i j₀ = r * b i) (hρ : ∀ ν, ρ ν j₀ = 0) (hρ₀ : ρ ν₀ = 0) :
    Matrix.det (matrix B ρ c t) =
      r * Matrix.det (matrix (B.updateCol j₀ b) ρ c (Function.update t ν₀ 0)) := by
  rw [matrix_update_zero_pole _ _ _ _ ν₀ hρ₀]
  exact det_eq_radius_mul B ρ c t j₀ r b hB hρ

/-- The boundary determinant retains the radial gain and has only the other
simple radial poles. The displayed coefficient is independent of t. -/
theorem abs_det_le_radius_simple_poles (B : Matrix I I ℝ) (ρ : J → I → ℝ)
    (c : I → J → ℝ) (t : J → ℝ) (j₀ : I) (ν₀ : J) (r : ℝ) (b : I → ℝ)
    (hB : ∀ i, B i j₀ = r * b i) (hρ : ∀ ν, ρ ν j₀ = 0) (hρ₀ : ρ ν₀ = 0)
    (ht : ∀ ν, ν ≠ ν₀ → 0 ≤ t ν) :
    |Matrix.det (matrix B ρ c t)| ≤
      |r| * coefficientBound (B.updateCol j₀ b) ρ c *
        ∏ ν ∈ Finset.univ.erase ν₀, max 1 (t ν) := by
  have ht' : ∀ ν, 0 ≤ Function.update t ν₀ 0 ν := by
    intro ν
    by_cases hν : ν = ν₀
    · subst ν
      simp only [Function.update_self, le_refl]
    · rw [Function.update_of_ne hν]
      exact ht ν hν
  rw [det_eq_radius_mul_without_pole B ρ c t j₀ ν₀ r b hB hρ hρ₀, abs_mul]
  have hbound := RadialPoleDeterminant.abs_det_le_simple_poles
    (B.updateCol j₀ b) ρ c (Function.update t ν₀ 0) ht'
  simpa only [prod_max_update_zero, mul_assoc] using
    mul_le_mul_of_nonneg_left hbound (abs_nonneg r)

end RadialRows

end EnvelopingIsomorphism.Deformation.Kontsevich.RadialBoundaryDeterminant
