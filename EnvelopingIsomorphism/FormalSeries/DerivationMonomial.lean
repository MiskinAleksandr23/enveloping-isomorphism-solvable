import EnvelopingIsomorphism.FormalSeries.DerivationExp

/-! Actual monomial exponentials of derivations, with their coordinate formula. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.DerivationSeries

open PowerSeries

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

def monomialCoefficients (N : ℕ) (D : Derivation k A A) (j : ℕ) : Derivation k A A :=
  if j = N then D else 0

theorem operators_monomialCoefficients (N : ℕ) (D : Derivation k A A) :
    operators (monomialCoefficients N D) = monomial N D.toLinearMap := by
  apply PowerSeries.ext
  intro j
  rw [coeff_operators, coeff_monomial]
  by_cases h : j = N <;> simp [monomialCoefficients, h]

variable [Algebra ℚ k] [Algebra ℚ A]

def monomialAutomorphism (N : ℕ) (hN : 0 < N) (D : Derivation k A A) :
    PowerSeries A ≃ₐ[PowerSeries k] PowerSeries A :=
  expAutomorphism (monomialCoefficients N D)
    (by simp [monomialCoefficients, Nat.ne_of_lt hN])

theorem monomialAutomorphism_apply (N : ℕ) (hN : 0 < N) (D : Derivation k A A) (p : PowerSeries A) :
    monomialAutomorphism N hN D p = EndomorphismSeries.act (exp (monomial N D.toLinearMap)) p := by
  rw [monomialAutomorphism, expAutomorphism_apply, operators_monomialCoefficients]

end EnvelopingIsomorphism.FormalSeries.DerivationSeries
