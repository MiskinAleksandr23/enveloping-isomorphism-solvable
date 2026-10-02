import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Detecting nilpotent derivations on the abelianization

The proof uses the higher Leibniz rule directly. If a power `D^s` maps the whole
algebra into its commutator ideal, and `D^t` maps the whole algebra into the
`n`th lower central term, then `D^(s + 2*t)` maps it into the next term.
This avoids building tensor powers or quotient actions on each graded layer.
-/

namespace EnvelopingIsomorphism.Lie

variable {R N : Type*} [CommRing R] [LieRing N] [LieAlgebra R N]

private theorem iterate_mem_lowerCentralSeries_succ
    (D : LieDerivation R N N) (n t : ℕ)
    (ht : ∀ x, D^[t] x ∈ LieModule.lowerCentralSeries R N N n)
    {z : N} (hz : z ∈ LieModule.lowerCentralSeries R N N 1) :
    D^[2 * t] z ∈ LieModule.lowerCentralSeries R N N (n + 1) := by
  rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero,
    ← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hz
  suffices (D.toLinearMap ^ (2 * t)) z ∈ LieModule.lowerCentralSeries R N N (n + 1) by
    simpa only [Module.End.pow_apply, LieDerivation.coeFn_coe] using this
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    simp only [Module.End.pow_apply, LieDerivation.coeFn_coe]
    rw [D.iterate_apply_lie]
    rw [← LieSubmodule.mem_toSubmodule]
    apply Submodule.sum_mem
    intro ij hij
    apply nsmul_mem
    rw [LieSubmodule.mem_toSubmodule]
    have hsum := Finset.mem_antidiagonal.mp hij
    rw [LieModule.lowerCentralSeries_succ]
    by_cases hi : t ≤ ij.1
    · rw [← lie_skew]
      rw [← LieSubmodule.mem_toSubmodule]
      apply Submodule.neg_mem
      rw [LieSubmodule.mem_toSubmodule]
      apply LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      have heq : ij.1 = t + (ij.1 - t) := by omega
      rw [heq, Function.iterate_add_apply]
      exact ht _
    · apply LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      have heq : ij.2 = t + (ij.2 - t) := by omega
      rw [heq, Function.iterate_add_apply]
      exact ht _
  | zero => simp
  | add x y hx hy hdx hdy =>
    simpa only [map_add, LieSubmodule.mem_toSubmodule] using
      (LieModule.lowerCentralSeries R N N (n + 1)).add_mem hdx hdy
  | smul r x hx hdx =>
    simpa only [map_smul, LieSubmodule.mem_toSubmodule] using
      (LieModule.lowerCentralSeries R N N (n + 1)).smul_mem r hdx

/-- A derivation of a nilpotent Lie algebra is nilpotent if some power sends every
element into the commutator ideal. -/
theorem isNilpotent_derivation_of_pow_mem_commutator [LieRing.IsNilpotent N]
    (D : LieDerivation R N N)
    (hD : ∃ s, ∀ x, D^[s] x ∈ LieModule.lowerCentralSeries R N N 1) :
    IsNilpotent D.toLinearMap := by
  obtain ⟨s, hs⟩ := hD
  have hbound (n : ℕ) : ∃ t, ∀ x, D^[t] x ∈ LieModule.lowerCentralSeries R N N n := by
    induction n with
    | zero => exact ⟨0, fun _ => LieSubmodule.mem_top _⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨2 * t + s, fun x => ?_⟩
      rw [Function.iterate_add_apply]
      exact iterate_mem_lowerCentralSeries_succ D n t ht (hs x)
  obtain ⟨n, hn⟩ := LieModule.IsNilpotent.nilpotent R N N
  obtain ⟨t, ht⟩ := hbound n
  refine ⟨t, LinearMap.ext fun x => ?_⟩
  simpa only [Module.End.pow_apply, LieDerivation.coeFn_coe, LinearMap.zero_apply] using
    (show D^[t] x = 0 by simpa only [hn, LieSubmodule.mem_bot] using ht x)

section IdealAction

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- The action of an ambient element on a Lie ideal, bundled as a derivation. -/
def idealActionDerivation (I : LieIdeal R L) (x : L) : LieDerivation R I I where
  toLinearMap := LieModule.toEnd R L I x
  leibniz' y z := by
    apply Subtype.ext
    change ⁅x, ⁅(y : L), (z : L)⁆⁆ = ⁅(y : L), ⁅x, (z : L)⁆⁆ - ⁅(z : L), ⁅x, (y : L)⁆⁆
    rw [leibniz_lie, sub_eq_add_neg, ← lie_skew (z : L), add_comm]
    simp

/-- Nilpotence of the action on the abelianization of a nilpotent ideal detects
nilpotence of that action on the ideal itself. The quotient retains the ambient
Lie algebra action. -/
theorem isNilpotent_ideal_action_of_abelianization
    (I : LieIdeal R L) [LieRing.IsNilpotent I] (x : L)
    (h : IsNilpotent (LieModule.toEnd R L
      (I ⧸ ⁅I, (⊤ : LieSubmodule R L I)⁆) x)) :
    IsNilpotent (LieModule.toEnd R L I x) := by
  let K : LieSubmodule R L I := ⁅I, (⊤ : LieSubmodule R L I)⁆
  let D := idealActionDerivation I x
  apply isNilpotent_derivation_of_pow_mem_commutator D
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun y => ?_⟩
  have hpow : (LieSubmodule.Quotient.mk' K) (D^[s] y) = 0 := by
    have heq : ∀ n, (LieSubmodule.Quotient.mk' K) (D^[n] y) =
        ((LieModule.toEnd R L (I ⧸ K) x) ^ n) ((LieSubmodule.Quotient.mk' K) y) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ← ih]
        exact (LieSubmodule.Quotient.mk' K).map_lie x _
    rw [heq, hs]
    rfl
  have hmem : D^[s] y ∈ K := by
    exact (LieSubmodule.Quotient.mk_eq_zero K).mp hpow
  have hK : K.toSubmodule = (LieModule.lowerCentralSeries R I I 1).toSubmodule := by
    exact I.coe_lcs_eq I 1
  rw [← LieSubmodule.mem_toSubmodule, ← hK]
  exact hmem

end IdealAction

end EnvelopingIsomorphism.Lie
