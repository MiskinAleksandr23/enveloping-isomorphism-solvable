import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Weight

/-!
# Finite polynomial tracking and the diagonal coefficient bound

An auxiliary polynomial variable tracks positive generator corrections.
It is evaluated at the central coefficient parameter in a possibly
noncommutative algebra. Only finite polynomial evaluation is used.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.PolynomialDiagonalBound

open scoped BigOperators

variable {k A α : Type*} [CommRing k] [Ring A] [Algebra (Polynomial k) A]

/-- Evaluate the auxiliary variable at the central polynomial coefficient parameter. -/
def trackingEval : Polynomial A →ₐ[Polynomial k] A :=
  Polynomial.eval₂AlgHom (AlgHom.id (Polynomial k) A)
    (algebraMap (Polynomial k) A Polynomial.X)
    (fun a ↦ (Algebra.commutes Polynomial.X a).symm)

@[simp] theorem trackingEval_C (a : A) : trackingEval (k := k) (Polynomial.C a) = a := by
  simp [trackingEval]

@[simp] theorem trackingEval_X :
    (trackingEval (k := k) (Polynomial.X : Polynomial A)) = algebraMap (Polynomial k) A Polynomial.X := by
  simp [trackingEval]

@[simp] theorem trackingEval_linear (a q : A) :
    trackingEval (k := k) (Polynomial.C a + Polynomial.X * Polynomial.C q) =
      a + (Polynomial.X : Polynomial k) • q := by
  rw [map_add, map_mul, trackingEval_C, trackingEval_X, trackingEval_C, Algebra.smul_def]

/-- Evaluation is a genuine finite sum of powers of the central scalar parameter. -/
theorem trackingEval_eq_sum (p : Polynomial A) :
    trackingEval (k := k) p = ∑ j ∈ p.support, (Polynomial.X ^ j : Polynomial k) • p.coeff j := by
  change Polynomial.eval₂ (RingHom.id A) (algebraMap (Polynomial k) A Polynomial.X) p = _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RingHom.id_apply, Algebra.smul_def, ← map_pow]
  exact (Algebra.commutes (Polynomial.X ^ j : Polynomial k) (p.coeff j)).symm

/-- Any polynomial-coefficient-linear coordinate map commutes with finite tracking evaluation. -/
theorem map_trackingEval (T : A →ₗ[Polynomial k] MvPolynomial α (Polynomial k))
    (p : Polynomial A) :
    T (trackingEval (k := k) p) = ∑ j ∈ p.support, (Polynomial.X ^ j : Polynomial k) • T (p.coeff j) := by
  rw [trackingEval_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact T.map_smul _ _

theorem mvCoeff_trackingEval (T : A →ₗ[Polynomial k] MvPolynomial α (Polynomial k))
    (p : Polynomial A) (m : α →₀ ℕ) :
    MvPolynomial.coeff m (T (trackingEval (k := k) p)) =
      ∑ j ∈ p.support, Polynomial.X ^ j * MvPolynomial.coeff m (T (p.coeff j)) := by
  rw [map_trackingEval, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]

/-- The two parameter degrees combine by finite diagonal coefficient extraction. -/
theorem coeff_trackingEval (T : A →ₗ[Polynomial k] MvPolynomial α (Polynomial k))
    (p : Polynomial A) (m : α →₀ ℕ) (r : ℕ) :
    Polynomial.coeff (MvPolynomial.coeff m (T (trackingEval (k := k) p))) r =
      ∑ j ∈ p.support, if j ≤ r then
        Polynomial.coeff (MvPolynomial.coeff m (T (p.coeff j))) (r - j) else 0 := by
  rw [mvCoeff_trackingEval]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']

/-- A bound `n+j*C` before evaluation becomes `n+r*C` at final coefficient `r`.
The algebra may be noncommutative; only its scalar parameter must be central. -/
theorem coeff_trackingEval_eq_zero_of_degree
    (T : A →ₗ[Polynomial k] MvPolynomial α (Polynomial k)) (p : Polynomial A) (n C : ℕ)
    (hdeg : ∀ j m, MvPolynomial.coeff m (T (p.coeff j)) ≠ 0 → m.degree ≤ n + j * C)
    (r : ℕ) (m : α →₀ ℕ) (hm : n + r * C < m.degree) :
    Polynomial.coeff (MvPolynomial.coeff m (T (trackingEval (k := k) p))) r = 0 := by
  rw [coeff_trackingEval]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjr : j ≤ r
  · rw [if_pos hjr]
    have hz : MvPolynomial.coeff m (T (p.coeff j)) = 0 := by
      by_contra hn
      have hd := hdeg j m hn
      have hmul := Nat.mul_le_mul_right C hjr
      omega
    simp [hz]
  · simp [hjr]

/-- At parameter zero, finite tracking evaluation retains exactly the auxiliary constant term. -/
theorem coeff_zero_trackingEval (T : A →ₗ[Polynomial k] MvPolynomial α (Polynomial k))
    (p : Polynomial A) (m : α →₀ ℕ) :
    Polynomial.coeff (MvPolynomial.coeff m (T (trackingEval (k := k) p))) 0 =
      Polynomial.coeff (MvPolynomial.coeff m (T (p.coeff 0))) 0 := by
  rw [coeff_trackingEval, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj₀
    simp [show ¬ j ≤ 0 by omega]
  · intro h₀
    have hp₀ : p.coeff 0 = 0 := by simpa using h₀
    simp [hp₀]

end EnvelopingIsomorphism.Rees.PolynomialDiagonalBound
