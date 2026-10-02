import EnvelopingIsomorphism.Lie.NilpotentIdealAction

/-!
# Sums of nilpotent Lie ideals

Nilpotence of an ideal here always means nilpotence as a Lie ring. This differs
from nilpotence as a module for the ambient Lie algebra.
-/

namespace EnvelopingIsomorphism.Lie

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M]

private def iteratedLie (I : LieIdeal R L) (N : LieSubmodule R L M) (n : ℕ) :=
  (fun P : LieSubmodule R L M => ⁅I, P⁆)^[n] N

private theorem iteratedLie_zero (I : LieIdeal R L) (N : LieSubmodule R L M) :
    iteratedLie I N 0 = N := rfl

private theorem iteratedLie_succ (I : LieIdeal R L) (N : LieSubmodule R L M) (n : ℕ) :
    iteratedLie I N (n + 1) = ⁅I, iteratedLie I N n⁆ :=
  Function.iterate_succ_apply' _ _ _

private theorem iteratedLie_mono (I : LieIdeal R L) (n : ℕ) :
    Monotone (fun N : LieSubmodule R L M => iteratedLie I N n) :=
  (show Monotone (fun N : LieSubmodule R L M => ⁅I, N⁆) from
    fun _ _ h => LieSubmodule.mono_lie_right I h).iterate n

private theorem iteratedLie_le_self (I : LieIdeal R L) (N : LieSubmodule R L M) (n : ℕ) :
    iteratedLie I N n ≤ N := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [iteratedLie_succ]
    exact (LieSubmodule.lie_le_right _ _).trans ih

private theorem iteratedLie_sup_le (I J : LieIdeal R L) (N : LieSubmodule R L M) (n : ℕ) :
    iteratedLie (I ⊔ J) N n ≤ ⁅I, N⁆ ⊔ iteratedLie J N n := by
  induction n with
  | zero => exact le_sup_right
  | succ n ih =>
    rw [iteratedLie_succ, LieSubmodule.sup_lie, iteratedLie_succ]
    apply sup_le
    · exact le_sup_of_le_left (LieSubmodule.mono_lie_right I (iteratedLie_le_self _ _ _))
    · refine (LieSubmodule.mono_lie_right J ih).trans ?_
      rw [LieSubmodule.lie_sup]
      exact sup_le_sup (LieSubmodule.lie_le_right _ _) le_rfl

private theorem iteratedLie_sup_le_lie (I J : LieIdeal R L) (N : LieSubmodule R L M)
    (q : ℕ) (hq : J.lcs M q = ⊥) :
    iteratedLie (I ⊔ J) N q ≤ ⁅I, N⁆ := by
  have h : iteratedLie J N q = ⊥ := by
    apply le_bot_iff.mp
    exact (iteratedLie_mono J q le_top).trans (le_of_eq hq)
  simpa only [h, sup_bot_eq] using iteratedLie_sup_le I J N q

/-- A quantitative bound for the action of the sum of two Lie ideals. -/
theorem sup_lcs_mul_le (I J : LieIdeal R L) (p q : ℕ) (hq : J.lcs M q = ⊥) :
    (I ⊔ J).lcs M (q * p) ≤ I.lcs M p := by
  induction p with
  | zero => simp
  | succ p ih =>
    change iteratedLie (I ⊔ J) ⊤ (q * (p + 1)) ≤ _
    rw [Nat.mul_succ, Nat.add_comm, iteratedLie, Function.iterate_add_apply]
    change iteratedLie (I ⊔ J) ((I ⊔ J).lcs M (q * p)) q ≤ _
    rw [LieIdeal.lcs_succ]
    exact (iteratedLie_mono (I ⊔ J) q ih).trans (iteratedLie_sup_le_lie I J _ q hq)

/-- The sum of ideals acting nilpotently on a module acts nilpotently on it. -/
theorem isNilpotent_sup_action [LieModule R L M] (I J : LieIdeal R L)
    [LieModule.IsNilpotent I M] [LieModule.IsNilpotent J M] :
    LieModule.IsNilpotent (I ⊔ J : LieIdeal R L) M := by
  obtain ⟨p, hp⟩ := LieModule.IsNilpotent.nilpotent R I M
  obtain ⟨q, hq⟩ := LieModule.IsNilpotent.nilpotent R J M
  have hp' : I.lcs M p = ⊥ := by
    simp only [← LieSubmodule.toSubmodule_inj, I.coe_lcs_eq, hp, LieSubmodule.bot_toSubmodule]
  have hq' : J.lcs M q = ⊥ := by
    simp only [← LieSubmodule.toSubmodule_inj, J.coe_lcs_eq, hq, LieSubmodule.bot_toSubmodule]
  apply (LieModule.isNilpotent_iff R (I ⊔ J : LieIdeal R L) M).mpr
  refine ⟨q * p, ?_⟩
  rw [← LieSubmodule.toSubmodule_inj, ← (I ⊔ J).coe_lcs_eq]
  have h := sup_lcs_mul_le I J p q hq'
  rw [hp', le_bot_iff] at h
  simp only [h, LieSubmodule.bot_toSubmodule]

/-- The sum of two intrinsically nilpotent Lie ideals is intrinsically nilpotent. -/
theorem isNilpotent_sup (I J : LieIdeal R L)
    [LieRing.IsNilpotent I] [LieRing.IsNilpotent J] :
    LieRing.IsNilpotent (I ⊔ J : LieIdeal R L) := by
  haveI := isNilpotent_ideal_action I
  haveI := isNilpotent_ideal_action J
  haveI := isNilpotent_sup_action (M := L) I J
  exact isNilpotent_of_ideal_action (I ⊔ J)

end EnvelopingIsomorphism.Lie
