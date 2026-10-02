import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Nilpotence from the traces of positive powers

The argument constructs a polynomial idempotent with zero constant term from
a Bézout identity. Its trace vanishes by the hypotheses; an idempotent with
trace zero is zero in characteristic zero. This forces a power of the
endomorphism to vanish, without extending the ground field.
-/

namespace EnvelopingIsomorphism.LinearAlgebra

open Polynomial

variable {k V : Type*} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [CharZero k] [FiniteDimensional k V] in
/-- Vanishing traces of positive powers imply vanishing trace for every
polynomial expression with zero constant coefficient. -/
theorem trace_aeval_eq_zero_of_trace_pow_eq_zero (f : Module.End k V)
    (h : ∀ n : ℕ, 0 < n → LinearMap.trace k V (f ^ n) = 0)
    {p : k[X]} (hp : p.coeff 0 = 0) : LinearMap.trace k V (aeval f p) = 0 := by
  rw [aeval_eq_sum_range, map_sum]
  apply Finset.sum_eq_zero
  intro n _
  by_cases hn : n = 0
  · subst n
    simp [hp]
  · rw [map_smul, h n (Nat.pos_of_ne_zero hn), smul_zero]

/-- An endomorphism is nilpotent if the traces of all its positive powers vanish.
The ground field is arbitrary of characteristic zero. -/
theorem isNilpotent_of_trace_pow_eq_zero (f : Module.End k V)
    (h : ∀ n : ℕ, 0 < n → LinearMap.trace k V (f ^ n) = 0) : IsNilpotent f := by
  classical
  obtain ⟨p, hp, hpf⟩ := IsAlgebraic.of_finite k f
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  simp only [map_zero, sub_zero] at hpq hq
  let n := p.rootMultiplicity 0 + 1
  let g : k[X] := X ^ n
  have hgq : aeval f (g * q) = 0 := by
    have hpoly : g * q = X * p := by
      rw [hpq]
      simp only [g, n, pow_succ']
      ring
    rw [hpoly, map_mul, hpf, mul_zero]
  have hcop : IsCoprime g q :=
    (Polynomial.irreducible_X.isCoprime_or_dvd q).resolve_right hq |>.pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have hid : (a * g) * (a * g) - a * g = -(a * b) * (g * q) := by
    calc
      _ = (a * g) * (a * g + b * q - 1) - (a * b) * (g * q) := by ring
      _ = _ := by rw [hab]; ring
  have heid : IsIdempotentElem (aeval f (a * g)) := by
    change aeval f (a * g) * aeval f (a * g) = aeval f (a * g)
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub, hid, map_mul, hgq, mul_zero]
  have hezero : aeval f (a * g) = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero heid
      (trace_aeval_eq_zero_of_trace_pow_eq_zero f h (by simp [g, n]))
  have hunit : aeval f (b * q) = 1 := by
    have ht := congrArg (aeval f) hab
    simpa only [map_add, map_one, hezero, zero_add] using ht
  refine ⟨n, ?_⟩
  calc
    f ^ n = aeval f g := (aeval_X_pow f).symm
    _ = aeval f g * aeval f (b * q) := by rw [hunit, mul_one]
    _ = aeval f (b * (g * q)) := by rw [← map_mul, mul_left_comm g b q]
    _ = 0 := by rw [map_mul, hgq, mul_zero]

end EnvelopingIsomorphism.LinearAlgebra
