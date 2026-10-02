import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing

/-!
# Formal endomorphism series

The coefficient ring throughout this file is allowed to be noncommutative. In
particular it can be a ring of linear endomorphisms, or Laurent series over such
a ring. No norm, topology, or finite-dimensionality hypothesis is needed.

The inverse construction reuses mathlib's coefficientwise recursive inverse.
The contracting-homotopy correction is the algebraic step in block F6.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

open PowerSeries

variable {R : Type*} [Ring R]

/-- Recursive formal inverse normalized to have constant coefficient one.
Its inverse identities require that the input has constant coefficient one. -/
def inverseOne (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.invOfUnit f 1

@[simp] theorem constantCoeff_inverseOne (f : PowerSeries R) :
    constantCoeff (inverseOne f) = 1 := by
  simp [inverseOne]

theorem mul_inverseOne {f : PowerSeries R} (hf : constantCoeff f = 1) :
    f * inverseOne f = 1 :=
  PowerSeries.mul_invOfUnit f 1 (by simpa using hf)

theorem inverseOne_mul {f : PowerSeries R} (hf : constantCoeff f = 1) :
    inverseOne f * f = 1 :=
  PowerSeries.invOfUnit_mul f 1 (by simpa using hf)

/-- A series `Id + O(t)` is a unit, even with noncommutative coefficients. -/
def unitOfConstantOne (f : PowerSeries R) (hf : constantCoeff f = 1) :
    (PowerSeries R)ˣ where
  val := f
  inv := inverseOne f
  val_inv := mul_inverseOne hf
  inv_val := inverseOne_mul hf

@[simp] theorem coe_unitOfConstantOne (f : PowerSeries R) (hf : constantCoeff f = 1) :
    (unitOfConstantOne f hf : PowerSeries R) = f := rfl

@[simp] theorem coe_inv_unitOfConstantOne (f : PowerSeries R)
    (hf : constantCoeff f = 1) :
    (↑((unitOfConstantOne f hf)⁻¹) : PowerSeries R) = inverseOne f := rfl

/-- A commuting operator also commutes with a two-sided inverse. -/
theorem commute_of_inverse {d K J : R} (hdK : d * K = K * d)
    (hKJ : K * J = 1) (hJK : J * K = 1) : d * J = J * d := by
  calc
    d * J = (J * K) * (d * J) := by rw [hJK, one_mul]
    _ = J * ((K * d) * J) := by simp only [mul_assoc]
    _ = J * ((d * K) * J) := by rw [hdK]
    _ = J * d := by simp only [mul_assoc, hKJ, mul_one]

/-- The ungraded operator identity behind correction of a contracting homotopy.
The grading of `d` and `H` is irrelevant to this identity: their products are
compositions, and `d² = 0` forces `dH + Hd` to commute with `d`. -/
theorem contractingHomotopy_correction {d H J : R} (hd : d * d = 0)
    (hKJ : (d * H + H * d) * J = 1)
    (hJK : J * (d * H + H * d) = 1) :
    d * (H * J) + (H * J) * d = 1 := by
  have hdK : d * (d * H + H * d) = (d * H + H * d) * d := by
    simp only [mul_add, add_mul, ← mul_assoc, hd, zero_mul, zero_add]
    simp only [mul_assoc, hd, mul_zero, add_zero]
  have hdJ := commute_of_inverse hdK hKJ hJK
  calc
    d * (H * J) + (H * J) * d = (d * H + H * d) * J := by
      simp only [add_mul, mul_assoc, ← hdJ]
    _ = 1 := hKJ

/-- Correct an approximate formal contracting homotopy to an exact one.
This holds for arbitrary endomorphism coefficient rings and therefore also for
infinite-dimensional complexes. -/
theorem formal_contractingHomotopy {d H : PowerSeries R} (hd : d * d = 0)
    (hH : constantCoeff (d * H + H * d) = 1) :
    let H' := H * inverseOne (d * H + H * d)
    d * H' + H' * d = 1 :=
  contractingHomotopy_correction hd (mul_inverseOne hH) (inverseOne_mul hH)

/-- A constant contracting homotopy for the constant differential corrects to
a contracting homotopy for the complete formal differential. -/
theorem formal_contractingHomotopy_of_constant {d : PowerSeries R} {H₀ : R}
    (hd : d * d = 0)
    (hH₀ : constantCoeff d * H₀ + H₀ * constantCoeff d = 1) :
    let H' := C H₀ * inverseOne (d * C H₀ + C H₀ * d)
    d * H' + H' * d = 1 := by
  apply formal_contractingHomotopy hd
  simpa using hH₀

/-- Powers of a positive-order series are coefficientwise eventually zero.
This gives the explicit finite bound used in formal geometric/log/exp sums. -/
theorem coeff_pow_eq_zero_of_lt {f : PowerSeries R} (hf : constantCoeff f = 0)
    {m n : ℕ} (hmn : n < m) : coeff n (f ^ m) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hmn)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hf)

/-- Every coefficient of the formal inverse is a finite geometric sum. -/
theorem coeff_inverseOne_one_sub {f : PowerSeries R} (hf : constantCoeff f = 0)
    (n : ℕ) :
    coeff n (inverseOne (1 - f)) = ∑ i ∈ Finset.range (n + 1), coeff n (f ^ i) := by
  have hunit : constantCoeff (1 - f) = 1 := by simp [hf]
  have hgeom :
      (∑ i ∈ Finset.range (n + 1), f ^ i) =
        (1 - f ^ (n + 1)) * inverseOne (1 - f) := by
    rw [← geom_sum_mul_neg, mul_assoc, mul_inverseOne hunit, mul_one]
  have hzero : coeff n (f ^ (n + 1) * inverseOne (1 - f)) = 0 := by
    apply PowerSeries.coeff_of_lt_order
    have hn : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    exact hn.trans_le ((PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hf).trans
      (le_self_add.trans (PowerSeries.le_order_mul _ _)))
  have hcoeff := congrArg (coeff n) hgeom
  simpa [sub_mul, hzero] using hcoeff.symm

/-- Congruence modulo the formal variable to the power `N`, defined directly
by equality of coefficients. This quotient works for noncommutative rings. -/
def jetCon (N : ℕ) : RingCon (PowerSeries R) where
  r f g := ∀ n < N, coeff n f = coeff n g
  iseqv := ⟨fun _ _ _ ↦ rfl, fun h n hn ↦ (h n hn).symm,
    fun h₁ h₂ n hn ↦ (h₁ n hn).trans (h₂ n hn)⟩
  add' hf hg n hn := by simp only [map_add, hf n hn, hg n hn]
  mul' hf hg n hn := by
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hij' := Finset.mem_antidiagonal.mp hij
    rw [hf i (by omega), hg j (by omega)]

/-- The finite-order quotient of the noncommutative formal series ring. -/
abbrev Jet (R : Type*) [Ring R] (N : ℕ) := (jetCon (R := R) N).Quotient

/-- Projection of a formal operator to its `N`-th finite-order quotient. -/
def toJet (N : ℕ) : PowerSeries R →+* Jet R N := (jetCon N).mk'

theorem toJet_eq_iff {N : ℕ} {f g : PowerSeries R} :
    toJet N f = toJet N g ↔ ∀ n < N, coeff n f = coeff n g :=
  (jetCon N).eq

/-- Positive-order formal operators become nilpotent in every finite quotient. -/
theorem toJet_pow_eq_zero {f : PowerSeries R} (hf : constantCoeff f = 0) (N : ℕ) :
    toJet N f ^ N = 0 := by
  rw [← map_pow, ← (toJet N).map_zero, toJet_eq_iff]
  intro n hn
  rw [coeff_pow_eq_zero_of_lt hf hn, map_zero]

theorem isNilpotent_toJet {f : PowerSeries R} (hf : constantCoeff f = 0) (N : ℕ) :
    IsNilpotent (toJet N f) := ⟨N, toJet_pow_eq_zero hf N⟩

/-- Equality in every finite quotient implies equality of complete series. -/
theorem ext_of_toJet_eq {f g : PowerSeries R}
    (h : ∀ N, toJet N f = toJet N g) : f = g := by
  ext n
  exact toJet_eq_iff.mp (h (n + 1)) n (Nat.lt_succ_self n)

section Rational

variable [Algebra ℚ R]

/-- Evaluate a scalar coefficient sequence at a formal operator by finite
coefficient sums. If `f(0) = 0`, coefficient `n` receives contributions only
from the powers with exponent at most `n`. -/
def sumPowers (c : ℕ → ℚ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ ∑ i ∈ Finset.range (n + 1), c i • coeff n (f ^ i)

@[simp] theorem coeff_sumPowers (c : ℕ → ℚ) (f : PowerSeries R) (n : ℕ) :
    coeff n (sumPowers c f) =
      ∑ i ∈ Finset.range (n + 1), c i • coeff n (f ^ i) :=
  PowerSeries.coeff_mk _ _

/-- Increasing a coefficient's finite summation bound adds only zero terms.
This makes the coefficientwise meaning of all formal sums explicit. -/
theorem coeff_sumPowers_eq_sum_of_le (c : ℕ → ℚ) {f : PowerSeries R}
    (hf : constantCoeff f = 0) {n N : ℕ} (hnN : n < N) :
    coeff n (sumPowers c f) = ∑ i ∈ Finset.range N, c i • coeff n (f ^ i) := by
  rw [coeff_sumPowers]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hnN))
  intro i hi hni
  rw [Finset.mem_range, not_lt] at hni
  rw [coeff_pow_eq_zero_of_lt hf (by omega), smul_zero]

/-- Formal exponential of a positive-order operator series. -/
def exp (f : PowerSeries R) : PowerSeries R :=
  sumPowers (fun i ↦ (1 : ℚ) / i.factorial) f

/-- Formal logarithm of `1 + f` for a positive-order operator series `f`. -/
def logOneAdd (f : PowerSeries R) : PowerSeries R :=
  sumPowers (fun i ↦ (-1 : ℚ) ^ (i + 1) / i) f

/-- Formal logarithm on operator series congruent to the identity. -/
def log (f : PowerSeries R) : PowerSeries R := logOneAdd (f - 1)

@[simp] theorem constantCoeff_sumPowers (c : ℕ → ℚ) (f : PowerSeries R) :
    constantCoeff (sumPowers c f) = algebraMap ℚ R (c 0) := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_sumPowers,
    Algebra.algebraMap_eq_smul_one]

@[simp] theorem constantCoeff_exp (f : PowerSeries R) : constantCoeff (exp f) = 1 := by
  simp [exp]

@[simp] theorem constantCoeff_logOneAdd (f : PowerSeries R) :
    constantCoeff (logOneAdd f) = 0 := by
  simp [logOneAdd]

@[simp] theorem constantCoeff_log (f : PowerSeries R) : constantCoeff (log f) = 0 := by
  simp [log]

/-- The formal exponential is invertible over an arbitrary noncommutative
`ℚ`-algebra. The inverse here is obtained by formal recursion. -/
theorem isUnit_exp (f : PowerSeries R) : IsUnit (exp f) :=
  (unitOfConstantOne (exp f) (constantCoeff_exp f)).isUnit

/-- In each finite quotient, the complete formal exponential is exactly
mathlib's polynomial exponential of a nilpotent element. -/
theorem toJet_exp {f : PowerSeries R} (hf : constantCoeff f = 0) (N : ℕ) :
    toJet N (exp f) = IsNilpotent.exp (toJet N f) := by
  rw [IsNilpotent.exp_eq_sum (toJet_pow_eq_zero hf N)]
  have htrunc : toJet N (exp f) =
      toJet N (∑ i ∈ Finset.range N, ((i.factorial : ℚ)⁻¹) • f ^ i) := by
    rw [toJet_eq_iff]
    intro n hn
    simp only [exp, coeff_sumPowers_eq_sum_of_le _ hf hn, map_sum,
      PowerSeries.coeff_smul, one_div]
  rw [htrunc, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_rat_smul, map_pow]

/-- Commuting positive-order formal operators satisfy the exponential law. -/
theorem exp_add_of_commute {f g : PowerSeries R} (hfg : Commute f g)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    exp (f + g) = exp f * exp g := by
  apply ext_of_toJet_eq
  intro N
  rw [map_mul, toJet_exp (by simp [hf, hg]), map_add, toJet_exp hf, toJet_exp hg]
  exact IsNilpotent.exp_add_of_commute (hfg.map (toJet N))
    (isNilpotent_toJet hf N) (isNilpotent_toJet hg N)

@[simp] theorem exp_zero : exp (0 : PowerSeries R) = 1 := by
  apply ext_of_toJet_eq
  intro N
  rw [toJet_exp (by simp), map_zero, IsNilpotent.exp_zero, map_one]

/-- The inverse of the formal exponential is the exponential of the negative
operator, without any commutativity assumption on the coefficient ring. -/
theorem exp_mul_exp_neg {f : PowerSeries R} (hf : constantCoeff f = 0) :
    exp f * exp (-f) = 1 := by
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl f)) hf (by simp [hf]),
    add_neg_cancel, exp_zero]

theorem exp_neg_mul_exp {f : PowerSeries R} (hf : constantCoeff f = 0) :
    exp (-f) * exp f = 1 := by
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl f)) (by simp [hf]) hf,
    neg_add_cancel, exp_zero]

end Rational

end EnvelopingIsomorphism.FormalSeries
