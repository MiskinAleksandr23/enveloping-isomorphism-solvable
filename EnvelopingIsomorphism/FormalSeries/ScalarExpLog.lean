import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.NoncommRing

/-! Universal scalar identities for transporting exp/log to noncommutative
formal operator series through their finite quotients. -/

noncomputable section
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.FormalSeries.Scalar

open PowerSeries

private theorem subst_one {a : PowerSeries ℚ} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries ℚ).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

/-- The logarithmic derivative is the inverse of `1+X`. -/
theorem derivative_log_mul_one_add_X :
    derivative ℚ (PowerSeries.log ℚ) * (1 + X) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have hshift (p : PowerSeries ℚ) : coeff (n + 1) (p * X) = coeff n p := by
      simpa using PowerSeries.coeff_mul_X_pow p 1 n
    simp only [mul_add, mul_one, map_add, coeff_mk,
      Nat.succ_eq_add_one, hshift, Algebra.algebraMap_self_apply]
    simp [pow_succ]

/-- The universal formal logarithm is a left compositional inverse of `exp-1`. -/
theorem log_subst_exp_sub_one :
    (PowerSeries.log ℚ).subst (PowerSeries.exp ℚ - 1) = X := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst ℚ PowerSeries.HasSubst.exp_sub_one,
      map_sub, PowerSeries.derivative_exp, Derivation.map_one_eq_zero, sub_zero,
      PowerSeries.derivative_X]
    have he : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1) := PowerSeries.HasSubst.exp_sub_one
    have h := congrArg (PowerSeries.substAlgHom (R := ℚ) he)
      derivative_log_mul_one_add_X
    simpa only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom,
      show (1 : PowerSeries ℚ) + (PowerSeries.exp ℚ - 1) = PowerSeries.exp ℚ by abel] using h
  · rw [PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_eq]
    exact
      PowerSeries.constantCoeff_subst_eq_zero
        (show MvPowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0 by
          simp [← PowerSeries.constantCoeff_eq])
        (PowerSeries.log ℚ) PowerSeries.constantCoeff_log

/-- The two universal scalar series are also inverse in the other order. -/
theorem exp_sub_one_subst_log :
    (PowerSeries.exp ℚ - 1).subst (PowerSeries.log ℚ) = X := by
  let E := PowerSeries.exp ℚ - 1
  have hE : constantCoeff E = 0 := by simp [E]
  have hE₁ : IsUnit (coeff 1 E) := by simp [E, PowerSeries.coeff_exp]
  let Q := E.substInvOfIsUnit hE₁
  have hQ : PowerSeries.HasSubst Q := PowerSeries.HasSubst.substInvOfIsUnit E hE₁
  have hEQ : E.subst Q = X := PowerSeries.subst_substInvOfIsUnit_right E hE hE₁
  have hlogQ : PowerSeries.log ℚ = Q := by
    calc
      PowerSeries.log ℚ = (PowerSeries.log ℚ).subst (E.subst Q) := by rw [hEQ, X_subst]
      _ = PowerSeries.subst Q (PowerSeries.subst E (PowerSeries.log ℚ)) :=
        (PowerSeries.subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := ℚ)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hE) hQ _).symm
      _ = Q := by rw [show (PowerSeries.log ℚ).subst E = X from log_subst_exp_sub_one,
        PowerSeries.subst_X hQ]
  rw [hlogQ]
  exact hEQ

/-- Scalar exponential of the scalar logarithm is `1+X`. -/
theorem exp_subst_log :
    (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) = 1 + X := by
  have h := exp_sub_one_subst_log
  rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, subst_one PowerSeries.HasSubst.log] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end EnvelopingIsomorphism.FormalSeries.Scalar
