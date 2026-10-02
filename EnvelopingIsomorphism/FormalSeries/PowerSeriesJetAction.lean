import EnvelopingIsomorphism.FormalSeries.PowerSeriesAction

/-! Formal operator actions descend to every finite-order quotient. Positive
operators become nilpotent there, and their formal exponentials become the
ordinary finite nilpotent exponentials. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.EndomorphismSeries

open PowerSeries

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

theorem act_congr {N : ℕ} {F G : PowerSeries (Module.End k A)}
    {p q : PowerSeries A}
    (hFG : ∀ n < N, coeff n F = coeff n G) (hpq : ∀ n < N, coeff n p = coeff n q) :
    ∀ n < N, coeff n (act F p) = coeff n (act G q) := by
  intro n hn
  rw [coeff_act, coeff_act]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hFG i (by omega), hpq j (by omega)]

/-- An endomorphism series acts on every finite jet of an algebra-valued series. -/
def actJet (N : ℕ) (F : PowerSeries (Module.End k A)) : Module.End k (Jet A N) where
  toFun z := Quotient.liftOn z (fun p ↦ toJet N (act F p)) (by
    intro p q hpq
    apply toJet_eq_iff.mpr
    exact act_congr (fun _ _ ↦ rfl) hpq)
  map_add' z w := Quotient.inductionOn₂ z w fun p q ↦ by
    change toJet N (act F (p + q)) = toJet N (act F p) + toJet N (act F q)
    rw [act_add_right, map_add]
  map_smul' c z := Quotient.inductionOn z fun p ↦ by
    change toJet N (act F (c • p)) = c • toJet N (act F p)
    rw [act_smul_right]
    rfl

@[simp] theorem actJet_toJet (N : ℕ) (F : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    actJet N F (toJet N p) = toJet N (act F p) := rfl

/-- Composition of actions on a finite jet is multiplication of formal
endomorphism series. -/
def actionJetHom (N : ℕ) : PowerSeries (Module.End k A) →+* Module.End k (Jet A N) where
  toFun := actJet N
  map_one' := by
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn with | h p =>
      change toJet N (act (1 : PowerSeries (Module.End k A)) p) = toJet N p
      rw [act_one]
  map_mul' F G := by
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn with | h p =>
      change toJet N (act (F * G) p) = toJet N (act F (act G p))
      rw [act_mul]
  map_zero' := by
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn with | h p =>
      change toJet N (act (0 : PowerSeries (Module.End k A)) p) = 0
      rw [act_zero_left, map_zero]
  map_add' F G := by
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn with | h p =>
      change toJet N (act (F + G) p) = toJet N (act F p) + toJet N (act G p)
      rw [act_add_left, map_add]

@[simp] theorem actionJetHom_toJet (N : ℕ) (F : PowerSeries (Module.End k A))
    (p : PowerSeries A) : actionJetHom N F (toJet N p) = toJet N (act F p) := rfl

theorem actionJetHom_eq_of_toJet_eq {N : ℕ} {F G : PowerSeries (Module.End k A)}
    (hFG : toJet N F = toJet N G) : actionJetHom N F = actionJetHom N G := by
  apply LinearMap.ext
  intro z
  induction z using Quotient.inductionOn with | h p =>
    change toJet N (act F p) = toJet N (act G p)
    exact toJet_eq_iff.mpr (act_congr (toJet_eq_iff.mp hFG) (fun _ _ ↦ rfl))

theorem actionJetHom_pow_eq_zero {F : PowerSeries (Module.End k A)}
    (hF : constantCoeff F = 0) (N : ℕ) : actionJetHom N F ^ N = 0 := by
  rw [← map_pow, ← (actionJetHom (k := k) (A := A) N).map_zero]
  apply actionJetHom_eq_of_toJet_eq
  rw [map_pow, toJet_pow_eq_zero hF, map_zero]

theorem isNilpotent_actionJetHom {F : PowerSeries (Module.End k A)}
    (hF : constantCoeff F = 0) (N : ℕ) : IsNilpotent (actionJetHom N F) :=
  ⟨N, actionJetHom_pow_eq_zero hF N⟩

section Rational

variable [Algebra ℚ k] [Algebra ℚ A]

/-- The full formal exponential specializes to the finite nilpotent exponential
on every jet. -/
theorem actionJetHom_exp {F : PowerSeries (Module.End k A)}
    (hF : constantCoeff F = 0) (N : ℕ) :
    actionJetHom N (exp F) = IsNilpotent.exp (actionJetHom N F) := by
  rw [IsNilpotent.exp_eq_sum (actionJetHom_pow_eq_zero hF N)]
  have htrunc : toJet N (exp F) =
      toJet N (∑ i ∈ Finset.range N, ((i.factorial : ℚ)⁻¹) • F ^ i) := by
    rw [toJet_eq_iff]
    intro n hn
    simp only [exp, coeff_sumPowers_eq_sum_of_le _ hF hn, map_sum,
      PowerSeries.coeff_smul, one_div]
  rw [actionJetHom_eq_of_toJet_eq htrunc, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_rat_smul, map_pow]

/-- The formal exponential fixes every vector killed by its generator. -/
theorem act_exp_of_act_eq_zero {F : PowerSeries (Module.End k A)}
    (hF : constantCoeff F = 0) {p : PowerSeries A} (hp : act F p = 0) :
    act (exp F) p = p := by
  apply ext_of_toJet_eq
  intro N
  have hy : (actionJetHom N F ^ 1) • toJet N p = 0 := by
    change actionJetHom N F (toJet N p) = 0
    rw [actionJetHom_toJet, hp, map_zero]
  have h := IsNilpotent.exp_smul_eq_sum
    (A := Module.End k (Jet A N)) (M := Jet A N) (a := actionJetHom N F)
    (m := toJet N p) hy (isNilpotent_actionJetHom hF N)
  have h' : IsNilpotent.exp (actionJetHom N F) (toJet N p) = toJet N p := by
    simpa using h
  rw [← actionJetHom_exp hF N, actionJetHom_toJet] at h'
  exact h'

/-- The exponential acts as the identity modulo the formal parameter. -/
theorem constantCoeff_act_exp (F : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    constantCoeff (act (exp F) p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff, coeff_act]
  simp only [Finset.HasAntidiagonal.antidiagonal_zero, Finset.sum_singleton,
    coeff_zero_eq_constantCoeff, constantCoeff_exp, Module.End.one_apply]

/-- A positive formal operator exponentiates to a genuine invertible linear
map of the full power-series module. -/
def expLinearEquiv (F : PowerSeries (Module.End k A)) (hF : constantCoeff F = 0) :
    PowerSeries A ≃ₗ[k] PowerSeries A where
  toFun := act (exp F)
  invFun := act (exp (-F))
  left_inv p := by
    rw [← act_mul, exp_neg_mul_exp hF, act_one]
  right_inv p := by
    rw [← act_mul, exp_mul_exp_neg hF, act_one]
  map_add' := act_add_right (exp F)
  map_smul' := act_smul_right (exp F)

@[simp] theorem expLinearEquiv_apply (F : PowerSeries (Module.End k A))
    (hF : constantCoeff F = 0) (p : PowerSeries A) :
    expLinearEquiv F hF p = act (exp F) p := rfl

@[simp] theorem expLinearEquiv_symm_apply (F : PowerSeries (Module.End k A))
    (hF : constantCoeff F = 0) (p : PowerSeries A) :
    (expLinearEquiv F hF).symm p = act (exp (-F)) p := rfl

end Rational

end EnvelopingIsomorphism.FormalSeries.EndomorphismSeries
