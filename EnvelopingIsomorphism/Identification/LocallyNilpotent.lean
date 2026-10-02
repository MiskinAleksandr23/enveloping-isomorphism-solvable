import EnvelopingIsomorphism.Identification.LocallyFinite
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum
import EnvelopingIsomorphism.Enveloping.UniversalProperties
import EnvelopingIsomorphism.Lie.NilpotentIdealAction

/-! Iterated Leibniz and the divisibility obstruction for locally nilpotent
derivations. The multiplication formula is also valid in a noncommutative algebra. -/

namespace EnvelopingIsomorphism.Identification

universe u v
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]

open Finset

/-- Iterated Leibniz for a linear endomorphism satisfying the product rule.
No commutativity of the target algebra is required. -/
theorem pow_apply_mul (D : Module.End R A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    (n : ℕ) (a b : A) :
    (D ^ n) (a * b) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ((D ^ ij.1) a * (D ^ ij.2) b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => (D ^ i) a * (D ^ j) b) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      hD, nsmul_add, sum_add_distrib]
    rw [add_comm, add_left_cancel_iff, sum_congr rfl]
    rintro ⟨i, j⟩ hij
    rw [mem_antidiagonal] at hij
    rw [Nat.choose_symm_of_eq_add hij.symm]

/-- Powers above the sum of two pointwise nilpotence bounds kill a product. -/
theorem pow_mul_eq_zero (D : Module.End R A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    {a b : A} {n m : ℕ} (ha : (D ^ n) a = 0) (hb : (D ^ m) b = 0) :
    (D ^ (n + m)) (a * b) = 0 := by
  rw [pow_apply_mul D hD]
  apply sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' := mem_antidiagonal.mp hij
  by_cases hi : n ≤ i
  · rw [pow_apply_eq_zero_of_le D ha hi, zero_mul, nsmul_zero]
  · have hj : m ≤ j := by omega
    rw [pow_apply_eq_zero_of_le D hb hj, mul_zero, nsmul_zero]

/-- At the sum of the last possible degrees, only one Leibniz term survives. -/
theorem top_pow_apply_mul (D : Module.End R A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    {a b : A} {n m : ℕ} (ha : (D ^ (n + 1)) a = 0)
    (hb : (D ^ (m + 1)) b = 0) :
    (D ^ (n + m)) (a * b) = (n + m).choose n • ((D ^ n) a * (D ^ m) b) := by
  rw [pow_apply_mul D hD]
  apply sum_eq_single_of_mem (n, m) (mem_antidiagonal.mpr rfl)
  rintro ⟨i, j⟩ hij hne
  have hij' := mem_antidiagonal.mp hij
  by_cases hi : n + 1 ≤ i
  · rw [pow_apply_eq_zero_of_le D ha hi, zero_mul, nsmul_zero]
  · have hj : m + 1 ≤ j := by
      by_contra! hj
      have hpair : (i, j) = (n, m) := by congr 1 <;> omega
      exact hne hpair
    rw [pow_apply_eq_zero_of_le D hb hj, mul_zero, nsmul_zero]

theorem exists_last_nonzero_pow {V : Type v} [AddCommGroup V] [Module R V]
    (D : Module.End R V) (hD : IsLocallyNilpotent D) {x : V} (hx : x ≠ 0) :
    ∃ n : ℕ, (D ^ n) x ≠ 0 ∧ (D ^ (n + 1)) x = 0 := by
  classical
  have h := hD x
  have hn : Nat.find h ≠ 0 := by
    intro hn
    have hz := Nat.find_spec h
    rw [hn, pow_zero, Module.End.one_apply] at hz
    exact hx hz
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨n, ?_, ?_⟩
  · exact Nat.find_min h (by omega)
  · simpa only [hn] using Nat.find_spec h

section Commutative

variable {B : Type v} [CommRing B] [IsDomain B] [CharZero B] [Algebra R B]

/-- A locally nilpotent derivation of a characteristic-zero domain cannot
map an element to a nonzero multiple of that same element. -/
theorem locallyNilpotent_eq_zero_of_eq_mul (D : Derivation R B B)
    (hD : IsLocallyNilpotent D.toLinearMap) {a b : B} (hab : D a = a * b) :
    D a = 0 := by
  classical
  by_contra hDa
  have ha : a ≠ 0 := by
    intro h
    apply hDa
    simp [h]
  have hb : b ≠ 0 := by
    intro h
    apply hDa
    simp [hab, h]
  obtain ⟨n, hn, hn1⟩ := exists_last_nonzero_pow D.toLinearMap hD ha
  obtain ⟨m, hm, hm1⟩ := exists_last_nonzero_pow D.toLinearMap hD hb
  have hmul (x y : B) : D.toLinearMap (x * y) = D.toLinearMap x * y + x * D.toLinearMap y := by
    simpa only [Derivation.coeFn_coe, smul_eq_mul, mul_comm, add_comm] using D.leibniz x y
  have htop := top_pow_apply_mul D.toLinearMap hmul hn1 hm1
  have hzero : (D.toLinearMap ^ (n + m)) (a * b) = 0 := by
    rw [← hab]
    change (D.toLinearMap ^ (n + m)) (D.toLinearMap a) = 0
    rw [← Module.End.mul_apply, ← pow_succ]
    exact pow_apply_eq_zero_of_le D.toLinearMap hn1 (by omega)
  rw [hzero, nsmul_eq_mul] at htop
  have hchoose : ((n + m).choose n : B) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ n + m)).ne'
  exact (mul_ne_zero hchoose (mul_ne_zero hn hm)) htop.symm

theorem locallyNilpotent_eq_zero_of_dvd (D : Derivation R B B)
    (hD : IsLocallyNilpotent D.toLinearMap) {a : B} (ha : a ∣ D a) : D a = 0 := by
  obtain ⟨b, hab⟩ := ha
  exact locallyNilpotent_eq_zero_of_eq_mul D hD hab

end Commutative

section Enveloping

variable {L : Type v} [LieRing L] [LieAlgebra R L]
attribute [local instance 100] LieRing.ofAssociativeRing

open UniversalEnvelopingAlgebra

/-- A nilpotent adjoint operator on the Lie generators induces a locally
nilpotent inner derivation on the entire universal enveloping algebra. -/
theorem ι_mem_LN_of_isNilpotent_ad (x : L)
    (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    ι R x ∈ LN R (UniversalEnvelopingAlgebra R L) := by
  let D := LieAlgebra.ad R (UniversalEnvelopingAlgebra R L) (ι R x)
  have hD (a b : UniversalEnvelopingAlgebra R L) :
      D (a * b) = D a * b + a * D b := by
    simp only [D, LieAlgebra.ad_apply, Ring.lie_def, mul_sub, sub_mul, mul_assoc]
    abel
  obtain ⟨n, hn⟩ := hx
  have hι (y : L) : (ι R) ((LieAlgebra.ad R L x) y) = D ((ι R) y) :=
    (ι R).map_lie x y
  intro a
  induction a using EnvelopingIsomorphism.Enveloping.induction with
  | scalar r =>
    refine ⟨1, ?_⟩
    simp [LieAlgebra.ad_apply, Ring.lie_def, Algebra.commutes]
  | generator y =>
    refine ⟨n, ?_⟩
    change (D ^ n) ((ι R).toLinearMap y) = 0
    rw [← intertwine_pow_apply (LieAlgebra.ad R L x) D (ι R).toLinearMap hι,
      hn, LinearMap.zero_apply, map_zero]
  | mul a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, pow_mul_eq_zero D hD hp hq⟩
  | add a b ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    refine ⟨p + q, ?_⟩
    rw [map_add, pow_apply_eq_zero_of_le D hp (Nat.le_add_right p q),
      pow_apply_eq_zero_of_le D hq (Nat.le_add_left q p), add_zero]

/-- Every element of a nilpotent Lie ideal belongs to the intrinsic LN set
of its enveloping algebra. This is block A5, without PBW or finite dimension. -/
theorem ι_mem_LN_of_mem_nilpotentIdeal (I : LieIdeal R L)
    [LieRing.IsNilpotent I] {x : L} (hx : x ∈ I) :
    ι R x ∈ LN R (UniversalEnvelopingAlgebra R L) := by
  letI := EnvelopingIsomorphism.Lie.isNilpotent_ideal_action I
  apply ι_mem_LN_of_isNilpotent_ad
  exact LieModule.isNilpotent_toEnd_of_isNilpotent R I L ⟨x, hx⟩

end Enveloping
end EnvelopingIsomorphism.Identification
