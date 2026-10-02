import EnvelopingIsomorphism.FormalSeries.PowerSeriesJetAction
import EnvelopingIsomorphism.FormalSeries.PowerSeriesDifferential

/-! Formal positive series of derivations exponentiate to automorphisms of the
complete power-series algebra. No dimension or analytic hypothesis is used. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.DerivationSeries

open PowerSeries EndomorphismSeries

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Encode an arbitrary series of coefficient derivations as an operator series. -/
def operators (D : ℕ → Derivation k A A) : PowerSeries (Module.End k A) :=
  PowerSeries.mk fun n ↦ (D n).toLinearMap

@[simp] theorem coeff_operators (D : ℕ → Derivation k A A) (n : ℕ) :
    coeff n (operators D) = (D n).toLinearMap := PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_operators (D : ℕ → Derivation k A A) :
    constantCoeff (operators D) = (D 0).toLinearMap := rfl

/-- A finite coefficient truncation is already a derivation over the entire
power-series scalar ring. -/
def truncation (D : ℕ → Derivation k A A) (N : ℕ) :
    Derivation (PowerSeries k) (PowerSeries A) (PowerSeries A) :=
  ∑ i ∈ Finset.range N, (X ^ i : PowerSeries A) • PowerSeriesAlgebra.derivation (D i)

private theorem sum_derivation_apply {ι : Type*} (s : Finset ι)
    (g : ι → Derivation (PowerSeries k) (PowerSeries A) (PowerSeries A)) (p : PowerSeries A) :
    (∑ i ∈ s, g i) p = ∑ i ∈ s, g i p := by
  change Derivation.coeFnAddMonoidHom (∑ i ∈ s, g i) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

theorem coeff_truncation (D : ℕ → Derivation k A A) (N : ℕ) (p : PowerSeries A) (n : ℕ) :
    coeff n (truncation D N p) =
      ∑ i ∈ Finset.range N, if i ≤ n then D i (coeff (n - i) p) else 0 := by
  rw [truncation, sum_derivation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Derivation.smul_apply, smul_eq_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeriesAlgebra.coeff_derivation]

/-- At every finite order, the full formal action equals a finite derivation. -/
theorem toJet_act_eq_truncation (D : ℕ → Derivation k A A) (N : ℕ) (p : PowerSeries A) :
    toJet N (act (operators D) p) = toJet N (truncation D N p) := by
  rw [toJet_eq_iff]
  intro n hn
  rw [coeff_act, coeff_truncation,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_operators]
  calc
    ∑ i ∈ Finset.range (n + 1), D i (coeff (n - i) p) =
        ∑ i ∈ Finset.range (n + 1), if i ≤ n then D i (coeff (n - i) p) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (by simpa using hi)]
    _ = ∑ i ∈ Finset.range N, if i ≤ n then D i (coeff (n - i) p) else 0 := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hn))
      intro i hi hni
      rw [if_neg (by simpa using hni)]

theorem act_mul (D : ℕ → Derivation k A A) (p q : PowerSeries A) :
    act (operators D) (p * q) = p * act (operators D) q + act (operators D) p * q := by
  apply ext_of_toJet_eq
  intro N
  rw [toJet_act_eq_truncation, (truncation D N).leibniz]
  simp only [smul_eq_mul, map_add, map_mul, toJet_act_eq_truncation]
  rw [mul_comm (toJet N q)]

theorem act_one (D : ℕ → Derivation k A A) : act (operators D) (1 : PowerSeries A) = 0 := by
  apply ext_of_toJet_eq
  intro N
  rw [toJet_act_eq_truncation, Derivation.map_one_eq_zero, map_zero]

theorem act_algebraMap (D : ℕ → Derivation k A A) (c : PowerSeries k) :
    act (operators D) (algebraMap (PowerSeries k) (PowerSeries A) c) = 0 := by
  apply ext_of_toJet_eq
  intro N
  rw [toJet_act_eq_truncation, Derivation.map_algebraMap, map_zero]

/-- The complete operator is a derivation; arbitrary positive-order coefficient
corrections are included, not just a single fixed coefficient derivation. -/
def derivation (D : ℕ → Derivation k A A) :
    Derivation k (PowerSeries A) (PowerSeries A) where
  toLinearMap := actionHom (operators D)
  map_one_eq_zero' := act_one D
  leibniz' p q := by
    simpa only [actionHom_apply, smul_eq_mul, mul_comm (q : PowerSeries A)] using act_mul D p q

theorem jet_leibniz (D : ℕ → Derivation k A A) (N : ℕ) (p q : Jet A N) :
    actionJetHom N (operators D) (p * q) =
      p * actionJetHom N (operators D) q + actionJetHom N (operators D) p * q := by
  induction p using Quotient.inductionOn with | h p =>
    induction q using Quotient.inductionOn with | h q =>
      change toJet N (act (operators D) (p * q)) =
        toJet N p * toJet N (act (operators D) q) +
          toJet N (act (operators D) p) * toJet N q
      rw [act_mul, map_add, map_mul, map_mul]

section Rational

variable [Algebra ℚ k] [Algebra ℚ A]

theorem positive_operators {D : ℕ → Derivation k A A} (hD : D 0 = 0) :
    constantCoeff (operators D) = 0 := by simp [hD]

/-- The exponential of a positive series of derivations preserves multiplication
on the complete power-series algebra. -/
theorem exp_act_mul (D : ℕ → Derivation k A A) (hD : D 0 = 0)
    (p q : PowerSeries A) :
    act (exp (operators D)) (p * q) = act (exp (operators D)) p * act (exp (operators D)) q := by
  apply ext_of_toJet_eq
  intro N
  have h := Module.End.exp_mul_of_derivation k (Jet A N) (actionJetHom N (operators D))
    (jet_leibniz D N) (isNilpotent_actionJetHom (positive_operators hD) N)
    (toJet N p) (toJet N q)
  rw [← actionJetHom_exp (positive_operators hD) N] at h
  simpa only [← map_mul, actionJetHom_toJet] using h

theorem exp_act_one (D : ℕ → Derivation k A A) (hD : D 0 = 0) :
    act (exp (operators D)) (1 : PowerSeries A) = 1 :=
  act_exp_of_act_eq_zero (positive_operators hD) (act_one D)

/-- Every formal scalar is fixed, so the result is an automorphism over `k[[t]]`. -/
theorem exp_act_algebraMap (D : ℕ → Derivation k A A) (hD : D 0 = 0)
    (c : PowerSeries k) :
    act (exp (operators D)) (algebraMap (PowerSeries k) (PowerSeries A) c) =
      algebraMap (PowerSeries k) (PowerSeries A) c :=
  act_exp_of_act_eq_zero (positive_operators hD) (act_algebraMap D c)

/-- The formal exponential of an arbitrary positive derivation series is an
algebra automorphism of the complete power-series algebra. -/
def expAutomorphism (D : ℕ → Derivation k A A) (hD : D 0 = 0) :
    PowerSeries A ≃ₐ[PowerSeries k] PowerSeries A where
  toEquiv := (expLinearEquiv (operators D) (positive_operators hD)).toEquiv
  map_mul' := exp_act_mul D hD
  map_add' := act_add_right (exp (operators D))
  commutes' := exp_act_algebraMap D hD

@[simp] theorem expAutomorphism_apply (D : ℕ → Derivation k A A) (hD : D 0 = 0)
    (p : PowerSeries A) : expAutomorphism D hD p = act (exp (operators D)) p := rfl

@[simp] theorem expAutomorphism_symm_apply (D : ℕ → Derivation k A A) (hD : D 0 = 0)
    (p : PowerSeries A) :
    (expAutomorphism D hD).symm p = act (exp (-operators D)) p := rfl

@[simp] theorem constantCoeff_expAutomorphism (D : ℕ → Derivation k A A) (hD : D 0 = 0)
    (p : PowerSeries A) : constantCoeff (expAutomorphism D hD p) = constantCoeff p :=
  constantCoeff_act_exp (operators D) p

end Rational

end EnvelopingIsomorphism.FormalSeries.DerivationSeries
