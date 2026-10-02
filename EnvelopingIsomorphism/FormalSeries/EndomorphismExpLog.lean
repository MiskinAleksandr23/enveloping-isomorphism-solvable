import EnvelopingIsomorphism.FormalSeries.Endomorphism
import EnvelopingIsomorphism.FormalSeries.ScalarExpLog
import EnvelopingIsomorphism.FormalSeries.NilpotentEvaluation

/-! The complete formal exponential and logarithm are mutually inverse for
positive-order series in arbitrary noncommutative rational algebras. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

open PowerSeries

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- Formal scalar evaluation agrees in every finite quotient with evaluation
at the corresponding nilpotent element. -/
theorem toJet_sumPowers {f : PowerSeries R} (hf : constantCoeff f = 0)
    (F : PowerSeries ℚ) (N : ℕ) :
    toJet N (sumPowers (fun i ↦ coeff i F) f) =
      nilEval (isNilpotent_toJet hf N) F := by
  rw [nilEval_eq_sum _ (toJet_pow_eq_zero hf N)]
  have htrunc : toJet N (sumPowers (fun i ↦ coeff i F) f) =
      toJet N (∑ i ∈ Finset.range N, coeff i F • f ^ i) := by
    rw [toJet_eq_iff]
    intro n hn
    simp only [coeff_sumPowers_eq_sum_of_le _ hf hn, map_sum, PowerSeries.coeff_smul]
  rw [htrunc, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_rat_smul, map_pow]

theorem exp_eq_sumPowers (f : PowerSeries R) :
    exp f = sumPowers (fun i ↦ coeff i (PowerSeries.exp ℚ)) f := by
  simp only [exp, PowerSeries.coeff_exp, Algebra.algebraMap_self_apply]

theorem logOneAdd_eq_sumPowers (f : PowerSeries R) :
    logOneAdd f = sumPowers (fun i ↦ coeff i (PowerSeries.log ℚ)) f := by
  unfold logOneAdd
  congr 1
  funext i
  simp only [PowerSeries.coeff_log, Algebra.algebraMap_self_apply]
  split_ifs with hi
  · simp [hi]
  · rfl

theorem toJet_exp_nilEval {f : PowerSeries R} (hf : constantCoeff f = 0) (N : ℕ) :
    toJet N (exp f) = nilEval (isNilpotent_toJet hf N) (PowerSeries.exp ℚ) := by
  rw [exp_eq_sumPowers, toJet_sumPowers hf]

theorem toJet_logOneAdd_nilEval {f : PowerSeries R} (hf : constantCoeff f = 0) (N : ℕ) :
    toJet N (logOneAdd f) = nilEval (isNilpotent_toJet hf N) (PowerSeries.log ℚ) := by
  rw [logOneAdd_eq_sumPowers, toJet_sumPowers hf]

/-- Exponentiating the formal logarithm of `1+f` recovers `1+f` for any
positive-order series with possibly noncommuting operator coefficients. -/
theorem exp_logOneAdd {f : PowerSeries R} (hf : constantCoeff f = 0) :
    exp (logOneAdd f) = 1 + f := by
  apply ext_of_toJet_eq
  intro N
  let hx := isNilpotent_toJet hf N
  calc
    toJet N (exp (logOneAdd f)) =
        nilEval (isNilpotent_toJet (constantCoeff_logOneAdd f) N) (PowerSeries.exp ℚ) :=
      toJet_exp_nilEval (constantCoeff_logOneAdd f) N
    _ = nilEval (isNilpotent_nilEval hx PowerSeries.constantCoeff_log) (PowerSeries.exp ℚ) :=
      nilEval_congr _ _ (toJet_logOneAdd_nilEval hf N) _
    _ = nilEval hx ((PowerSeries.exp ℚ).subst (PowerSeries.log ℚ)) :=
      (nilEval_subst hx _ PowerSeries.constantCoeff_log).symm
    _ = toJet N (1 + f) := by
      rw [Scalar.exp_subst_log, map_add, map_one, nilEval_X, map_add, map_one]

/-- The formal logarithm of the exponential recovers a positive-order series. -/
theorem log_exp {f : PowerSeries R} (hf : constantCoeff f = 0) : log (exp f) = f := by
  apply ext_of_toJet_eq
  intro N
  let hx := isNilpotent_toJet hf N
  have hE : constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp
  have hfE : constantCoeff (exp f - 1) = 0 := by simp
  have hsub : toJet N (exp f - 1) = nilEval hx (PowerSeries.exp ℚ - 1) := by
    rw [map_sub, toJet_exp_nilEval hf, map_one, map_sub, map_one]
  calc
    toJet N (log (exp f)) = nilEval (isNilpotent_toJet hfE N) (PowerSeries.log ℚ) :=
      toJet_logOneAdd_nilEval hfE N
    _ = nilEval (isNilpotent_nilEval hx hE) (PowerSeries.log ℚ) :=
      nilEval_congr _ _ hsub _
    _ = nilEval hx ((PowerSeries.log ℚ).subst (PowerSeries.exp ℚ - 1)) :=
      (nilEval_subst hx _ hE).symm
    _ = toJet N f := by rw [Scalar.log_subst_exp_sub_one, nilEval_X]

/-- The formal exponential and logarithm are inverse on series congruent to
the identity, in the full complete noncommutative series ring. -/
theorem exp_log {f : PowerSeries R} (hf : constantCoeff f = 1) : exp (log f) = f := by
  change exp (logOneAdd (f - 1)) = f
  calc
    exp (logOneAdd (f - 1)) = 1 + (f - 1) := exp_logOneAdd (by simp [hf])
    _ = f := by abel

end EnvelopingIsomorphism.FormalSeries
