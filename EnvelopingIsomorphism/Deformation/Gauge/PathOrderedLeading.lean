import EnvelopingIsomorphism.Deformation.Gauge.UnitGroup
import EnvelopingIsomorphism.FormalSeries.PathOrderedExp

/-! The leading jet of the genuine path-ordered exponential. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries
open EnvelopingIsomorphism.FormalSeries
open PathOrderedExp

variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem solutionCoeff_zero_below (X : PathSeries R) (N : ℕ)
    (hX : ∀ i, i < N → coeff i X = 0) (n : ℕ) (hn : n < N) (hn0 : 0 < n) :
    solutionCoeff X n = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [solutionCoeff_succ]
    have hs : (∑ i ∈ Finset.range (n + 1), coeff (i + 1) X * solutionCoeff X (n - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hX (i + 1) (by have := Finset.mem_range.mp hi; omega), zero_mul]
    rw [hs, map_zero]

theorem solutionCoeff_leading (X : PathSeries R) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i, i < N → coeff i X = 0) :
    solutionCoeff X N = PolynomialIntegral.integral (coeff N X) := by
  cases N with
  | zero => omega
  | succ n =>
    rw [solutionCoeff_succ]
    congr 1
    rw [Finset.sum_eq_single n]
    · rw [Nat.sub_self, solutionCoeff_zero, mul_one]
    · intro i hi hin
      rw [hX (i + 1) (by have := Finset.mem_range.mp hi; omega), zero_mul]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (Nat.lt_succ_self n)))

theorem solution_nearIdentity (X : PathSeries R) (N : ℕ)
    (hX : ∀ i, i < N → coeff i X = 0) : NearIdentity N (solution X) := by
  change toJet N (solution X) = 1
  rw [← map_one (toJet N), toJet_eq_iff]
  intro i hi
  rw [coeff_solution]
  by_cases hz : i = 0
  · subst i
    simp [solutionCoeff_zero]
  · rw [solutionCoeff_zero_below X N hX i hi (Nat.pos_of_ne_zero hz)]
    simp [coeff_one, hz]

theorem endpoint_nearIdentity (X : PathSeries R) (N : ℕ)
    (hX : ∀ i, i < N → coeff i X = 0) :
    NearIdentity N (evaluation 1 (solution X)) := by
  change toJet N (evaluation 1 (solution X)) = 1
  rw [← map_one (toJet N), toJet_eq_iff]
  intro i hi
  rw [coeff_evaluation, (solution_nearIdentity X N hX).coeff i hi]
  by_cases hz : i = 0 <;> simp [coeff_one, hz]

theorem endpoint_leading (X : PathSeries R) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i, i < N → coeff i X = 0) (x : R) (hx : coeff N X = Polynomial.C x) :
    coeff N (evaluation 1 (solution X)) = x := by
  rw [coeff_evaluation, coeff_solution, solutionCoeff_leading X N hN hX, hx,
    ← Polynomial.monomial_zero_left, PolynomialIntegral.integral_monomial]
  simp

/-- The endpoint is an actual element of the near-identity gauge group. -/
def orderedGauge (X : PathSeries R) : GaugeUnit R :=
  ⟨endpointUnit X, by
    change toJet 1 (evaluation 1 (solution X)) = 1
    rw [← map_one (toJet 1), toJet_eq_iff]
    intro i hi
    have hz : i = 0 := by omega
    subst i
    rw [coeff_zero_eq_constantCoeff, constantCoeff_endpoint, map_one]⟩

@[simp] theorem orderedGauge_series (X : PathSeries R) :
    (orderedGauge X).series = evaluation 1 (solution X) := rfl

theorem orderedGauge_near (X : PathSeries R) (N : ℕ)
    (hX : ∀ i, i < N → coeff i X = 0) : NearIdentity N (orderedGauge X).series :=
  endpoint_nearIdentity X N hX

theorem orderedGauge_leading (X : PathSeries R) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i, i < N → coeff i X = 0) (x : R) (hx : coeff N X = Polynomial.C x) :
    coeff N (orderedGauge X).series = x := endpoint_leading X N hN hX x hx

end EnvelopingIsomorphism.Deformation.Gauge
