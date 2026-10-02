import EnvelopingIsomorphism.FormalSeries.MonomialExpAction
import EnvelopingIsomorphism.Deformation.NilpotentConjugation
import EnvelopingIsomorphism.Deformation.Gauge.ElementaryOperators

/-! A genuine positive monomial adjoint exponential on formal cochain families
is the genuine complete conjugation by the corresponding operator exponential.
The coefficient endomorphism itself need not be nilpotent. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.AdjointMonomialExp

set_option backward.isDefEq.respectTransparency false

open PowerSeries PowerSeriesModule
open EnvelopingIsomorphism.Deformation
open EnvelopingIsomorphism.Deformation.NilpotentConjugation
open EnvelopingIsomorphism.Deformation.Gauge

variable {k V : Type*} [CommRing k] [Algebra ℚ k]
variable [AddCommGroup V] [Module k V] [Module ℚ V]
variable [IsScalarTower ℚ k V] [SMulCommClass k ℚ V]

local instance cochainEndRing : Ring (Module.End k (Binary k V)) :=
  @Module.End.instRing k (Binary k V) inferInstance inferInstance inferInstance

local instance vectorEndRing : Ring (Module.End k V) :=
  @Module.End.instRing k V inferInstance inferInstance inferInstance

theorem coeff_exp_output (D : Module.End k V) (N m : ℕ)
    (B : Binary k V) (x y : V) :
    (coeff m (exp (monomial N (output D)))) B x y =
      (coeff m (exp (monomial N D))) (B x y) := by
  simp only [exp, sumPowers, PowerSeries.coeff_mk, noncomm_monomial_pow, coeff_monomial,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [output_pow_apply]

theorem coeff_exp_inputLeft (D : Module.End k V) (N m : ℕ)
    (B : Binary k V) (x y : V) :
    (coeff m (exp (monomial N (inputLeft D)))) B x y =
      B ((coeff m (exp (monomial N D))) x) y := by
  simp only [exp, sumPowers, PowerSeries.coeff_mk, noncomm_monomial_pow, coeff_monomial,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_rat_smul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [inputLeft_pow_apply]

theorem coeff_exp_inputRight (D : Module.End k V) (N m : ℕ)
    (B : Binary k V) (x y : V) :
    (coeff m (exp (monomial N (inputRight D)))) B x y =
      B x ((coeff m (exp (monomial N D))) y) := by
  simp only [exp, sumPowers, PowerSeries.coeff_mk, noncomm_monomial_pow, coeff_monomial,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_rat_smul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [inputRight_pow_apply]

theorem act_exp_output (D : Module.End k V) (N : ℕ) (B : PowerSeriesModule k (Binary k V)) :
    actV (exp (monomial N (output D))) B =
      postcomposeBinary (operatorSeries (exp (monomial N D))) B := by
  apply PowerSeriesModule.ext
  intro n
  ext x y
  simp only [coeffV_actV, LinearMap.sum_apply, coeff_exp_output, postcomposeBinary,
    linearCompose, extendBilinear_apply, coeffV_applyBilinear, coeffV_map,
    coeffV_operatorSeries, LinearMap.llcomp_apply]

theorem act_exp_inputLeft (D : Module.End k V) (N : ℕ) (B : PowerSeriesModule k (Binary k V)) :
    actV (exp (monomial N (inputLeft D))) B =
      linearCompose B (operatorSeries (exp (monomial N D))) := by
  apply PowerSeriesModule.ext
  intro n
  ext x y
  simp only [coeffV_actV, LinearMap.sum_apply, coeff_exp_inputLeft,
    linearCompose, extendBilinear_apply, coeffV_applyBilinear,
    coeffV_operatorSeries, LinearMap.llcomp_apply]
  exact Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij ↦ (coeffV ij.1 B) ((coeff ij.2 (exp (monomial N D))) x) y)

theorem act_exp_inputRight (D : Module.End k V) (N : ℕ) (B : PowerSeriesModule k (Binary k V)) :
    actV (exp (monomial N (inputRight D))) B =
      precomposeBinaryRight B (operatorSeries (exp (monomial N D))) := by
  apply PowerSeriesModule.ext
  intro n
  ext x y
  simp only [coeffV_actV, LinearMap.sum_apply, coeff_exp_inputRight,
    precomposeBinaryRight, coeffV_flipBinarySeries, LinearMap.flip_apply,
    linearCompose, extendBilinear_apply, coeffV_applyBilinear,
    coeffV_operatorSeries, LinearMap.llcomp_apply]
  exact Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij ↦ (coeffV ij.1 B) x ((coeff ij.2 (exp (monomial N D))) y))

private theorem commute_monomial {A : Type*} [Semiring A] (N : ℕ) {x y : A} (h : Commute x y) :
    Commute (monomial N x) (monomial N y) := by
  change monomial N x * monomial N y = monomial N y * monomial N x
  rw [monomial_mul_monomial, monomial_mul_monomial, h.eq]

/-- Full formal adjoint transport equals actual formal conjugation. Positivity
of the monomial degree replaces any nilpotence assumption on the coefficient D. -/
theorem adjoint_monomial_exp_eq_conjugate (D : Module.End k V) (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k V)) :
    actV (k := k) (V := Binary k V) (exp (R := Module.End k (Binary k V))
      (monomial N (unaryActionEnd D))) B =
      conjugateBinarySeries (k := k) (V := V)
        (formalExpUnit (R := Module.End k V) (monomial N D)
          (monomial_constantCoeff_zero (R := Module.End k V) hN D)) B := by
  have hsplit : monomial N (unaryActionEnd D) =
      monomial N (output D) + monomial N (inputRight (-D)) + monomial N (inputLeft (-D)) := by
    have h : unaryActionEnd D = output D + inputRight (-D) + inputLeft (-D) := by
      rw [unaryActionEnd, inputRight_neg, inputLeft_neg]
      abel
    rw [h, map_add, map_add]
  have h₁ : Commute (monomial N (output D)) (monomial N (inputRight (-D))) :=
    commute_monomial N (output_inputRight_commute D (-D))
  have h₂ : Commute (monomial N (output D) + monomial N (inputRight (-D)))
      (monomial N (inputLeft (-D))) :=
    (commute_monomial N (output_inputLeft_commute D (-D))).add_left
      (commute_monomial N (inputLeft_inputRight_commute (-D) (-D)).symm)
  have ho : constantCoeff (monomial N (output D)) = 0 := by
    simp only [← coeff_zero_eq_constantCoeff, coeff_monomial, if_neg (Nat.ne_of_lt hN)]
  have hr : constantCoeff (monomial N (inputRight (-D))) = 0 :=
    by simp only [← coeff_zero_eq_constantCoeff, coeff_monomial, if_neg (Nat.ne_of_lt hN)]
  have hl : constantCoeff (monomial N (inputLeft (-D))) = 0 :=
    by simp only [← coeff_zero_eq_constantCoeff, coeff_monomial, if_neg (Nat.ne_of_lt hN)]
  have hor : constantCoeff (monomial N (output D) + monomial N (inputRight (-D))) = 0 := by
    rw [map_add, ho, hr, zero_add]
  have he₂ := exp_add_of_commute (R := Module.End k (Binary k V)) h₂ hor hl
  have he₁ := exp_add_of_commute (R := Module.End k (Binary k V)) h₁ ho hr
  rw [hsplit, he₂, he₁]
  rw [actV_mul, actV_mul]
  rw [act_exp_output, act_exp_inputRight, act_exp_inputLeft]
  simp only [conjugateBinarySeries, coe_formalExpUnit, coe_formalExpUnit_inv, map_neg]

end EnvelopingIsomorphism.FormalSeries.AdjointMonomialExp
