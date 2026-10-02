import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# Powers of two-sided ideals as submodules over the coefficient ring

The ambient algebra is allowed to be noncommutative. Taking ideal powers before
restricting scalars gives the full algebra in degree zero, as required for an
adic filtration. Taking powers directly in `Submodule k A` would instead give
the scalar submodule in degree zero.
-/

namespace EnvelopingIsomorphism.Enveloping

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

/-- The `n`th ideal power, viewed as a submodule over the coefficient ring. -/
def adicPower (I : TwoSidedIdeal A) (n : ℕ) : Submodule k A :=
  (I.asIdeal ^ n).restrictScalars k

/-- Degree zero of the adic filtration is the full ambient algebra. -/
theorem adicPower_zero (I : TwoSidedIdeal A) :
    adicPower k A I 0 = ⊤ := by
  simp [adicPower, Submodule.pow_zero, Ideal.one_eq_top]

/-- Multiplication of filtration pieces adds their degrees, including degree zero. -/
theorem adicPower_mul (I : TwoSidedIdeal A) (m n : ℕ) :
    adicPower k A I (m + n) = adicPower k A I m * adicPower k A I n := by
  simp only [adicPower, Ideal.IsTwoSided.pow_add, Submodule.restrictScalars_mul]

/-- In positive degrees, ideal powers agree with powers of the underlying submodule. -/
theorem adicPower_positive (I : TwoSidedIdeal A) {n : ℕ} (hn : n ≠ 0) :
    adicPower k A I n = (I.asIdeal.restrictScalars k) ^ n := by
  exact Submodule.restrictScalars_pow hn

end EnvelopingIsomorphism.Enveloping
