import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Reweighting of homogeneous blocks

An exact monomial coefficient reweighting gives the corresponding exact
homogeneous-component identity on every polynomial. The actual coefficient
formula is an explicit premise supplied by the Rees scaling producer.
-/

namespace EnvelopingIsomorphism.Rees.HomogeneousBlocks

open MvPolynomial

variable {R α β : Type*} [CommRing R]

/-- Extracting an input/output homogeneous block turns a degree-dependent
unit scaling into one scalar on the entire block. -/
theorem homogeneousComponent_comp
    (u : Rˣ) (f g : MvPolynomial α R →ₗ[R] MvPolynomial β R)
    (h : ∀ (p : α →₀ ℕ) (q : β →₀ ℕ),
      coeff q (f (monomial p 1)) =
        (((u ^ ((p.degree : ℤ) - (q.degree : ℤ))) : Rˣ) : R) *
          coeff q (g (monomial p 1))) (n m : ℕ) :
    (homogeneousComponent m).comp (f.comp (homogeneousComponent n)) =
      ((((u ^ ((n : ℤ) - (m : ℤ))) : Rˣ) : R)) •
        ((homogeneousComponent m).comp (g.comp (homogeneousComponent n))) := by
  classical
  apply MvPolynomial.linearMap_ext
  intro p
  apply LinearMap.ext
  intro a
  change homogeneousComponent m (f (homogeneousComponent n (monomial p a))) =
    (((u ^ ((n : ℤ) - (m : ℤ))) : Rˣ) : R) •
      homogeneousComponent m (g (homogeneousComponent n (monomial p a)))
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial a rfl)]
  by_cases hp : n = p.degree
  · rw [if_pos hp]
    apply MvPolynomial.ext
    intro q
    rw [coeff_smul, coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases hq : q.degree = m
    · rw [if_pos hq, if_pos hq]
      have hmon : monomial p a = a • (monomial p (1 : R) : MvPolynomial α R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hmon, map_smul, map_smul, coeff_smul, coeff_smul, h p q, ← hp, hq]
      simp only [smul_eq_mul]
      ring
    · simp [hq]
  · rw [if_neg hp]
    simp

/-- Pointwise form of the same exact block identity, for every input polynomial. -/
theorem homogeneousComponent_apply
    (u : Rˣ) (f g : MvPolynomial α R →ₗ[R] MvPolynomial β R)
    (h : ∀ (p : α →₀ ℕ) (q : β →₀ ℕ),
      coeff q (f (monomial p 1)) =
        (((u ^ ((p.degree : ℤ) - (q.degree : ℤ))) : Rˣ) : R) *
          coeff q (g (monomial p 1))) (n m : ℕ) (x : MvPolynomial α R) :
    homogeneousComponent m (f (homogeneousComponent n x)) =
      (((u ^ ((n : ℤ) - (m : ℤ))) : Rˣ) : R) •
        homogeneousComponent m (g (homogeneousComponent n x)) :=
  LinearMap.congr_fun (homogeneousComponent_comp u f g h n m) x

end EnvelopingIsomorphism.Rees.HomogeneousBlocks
