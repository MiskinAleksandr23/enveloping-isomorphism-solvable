import EnvelopingIsomorphism.Deformation.Gauge.CompatibleCorrections

/-! Genuine scalar-series-linear gauge equivalences and passage of product transport to the limit. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries
open EnvelopingIsomorphism.FormalSeries

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Formal operator convolution is linear over the whole formal scalar ring. -/
def operator (F : PowerSeries (Module.End k V)) :
    PowerSeriesModule k V →ₗ[PowerSeries k] PowerSeriesModule k V :=
  PowerSeriesModule.linearApply (PowerSeriesModule.mk fun n => coeff n F)

@[simp] theorem operator_apply (F : PowerSeries (Module.End k V)) (x : PowerSeriesModule k V) :
    operator F x = PowerSeriesModule.actV F x := by
  apply PowerSeriesModule.ext
  intro n
  rw [PowerSeriesModule.coeffV_actV]
  rfl

theorem operator_mul (F G : PowerSeries (Module.End k V)) :
    operator (F * G) = (operator F).comp (operator G) := by
  ext x n
  simp only [operator_apply, LinearMap.comp_apply, PowerSeriesModule.actV_mul]

@[simp] theorem operator_one : operator (1 : PowerSeries (Module.End k V)) = LinearMap.id := by
  ext x n
  simp only [operator_apply, PowerSeriesModule.actV_one, LinearMap.id_apply]

/-- A formal operator unit induces an actual equivalence of completed vector modules. -/
def operatorUnitEquiv (F : (PowerSeries (Module.End k V))ˣ) :
    PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k V :=
  LinearEquiv.ofLinear (operator (F : PowerSeries (Module.End k V)))
    (operator (↑(F⁻¹) : PowerSeries (Module.End k V)))
    (by rw [← operator_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, operator_one])
    (by rw [← operator_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, operator_one])

@[simp] theorem operatorUnitEquiv_apply (F : (PowerSeries (Module.End k V))ˣ)
    (x : PowerSeriesModule k V) : operatorUnitEquiv F x = operator F x := rfl

def AgreeBelow (N : ℕ) (x y : PowerSeriesModule k V) : Prop :=
  ∀ i, i < N → PowerSeriesModule.coeffV i x = PowerSeriesModule.coeffV i y

theorem AgreeBelow.symm {N : ℕ} {x y : PowerSeriesModule k V} (h : AgreeBelow N x y) :
    AgreeBelow N y x := fun i hi => (h i hi).symm

theorem operator_congr {N : ℕ} {F G : PowerSeries (Module.End k V)}
    (hFG : toJet N F = toJet N G) (x : PowerSeriesModule k V) :
    AgreeBelow N (operator F x) (operator G x) := by
  intro n hn
  simp only [operator_apply, PowerSeriesModule.coeffV_actV]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [(toJet_eq_iff.mp hFG) i (by omega)]

theorem compatibleLimit_agrees {F : ℕ → PowerSeries (Module.End k V)} (hF : Compatible F)
    (N : ℕ) (x : PowerSeriesModule k V) :
    AgreeBelow N (operator (compatibleLimit F) x) (operator (F N) x) :=
  operator_congr (compatibleLimit_toJet hF N) x

theorem extendBinary_congr {N : ℕ}
    (B : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V))
    {x x' y y' : PowerSeriesModule k V} (hx : AgreeBelow N x x') (hy : AgreeBelow N y y') :
    AgreeBelow N (PowerSeriesModule.extendBinary B x y) (PowerSeriesModule.extendBinary B x' y') := by
  intro n hn
  rw [PowerSeriesModule.coeffV_extendBinary, PowerSeriesModule.coeffV_extendBinary]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [hx b (by omega), hy j (by omega)]

/-- Finite-order product transport by one compatible sequence becomes exact at the limit. -/
theorem compatibleLimit_intertwines {F : ℕ → PowerSeries (Module.End k V)} (hF : Compatible F)
    (B C : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V))
    (hBC : ∀ N x y, AgreeBelow N
      (operator (F N) (PowerSeriesModule.extendBinary B x y))
      (PowerSeriesModule.extendBinary C (operator (F N) x) (operator (F N) y)))
    (x y : PowerSeriesModule k V) :
    operator (compatibleLimit F) (PowerSeriesModule.extendBinary B x y) =
      PowerSeriesModule.extendBinary C (operator (compatibleLimit F) x) (operator (compatibleLimit F) y) := by
  apply PowerSeriesModule.ext
  intro n
  exact ((compatibleLimit_agrees hF (n + 1) (PowerSeriesModule.extendBinary B x y)) n
    (Nat.lt_succ_self n)).trans ((hBC (n + 1) x y n (Nat.lt_succ_self n)).trans
      ((extendBinary_congr C (compatibleLimit_agrees hF (n + 1) x).symm
        (compatibleLimit_agrees hF (n + 1) y).symm) n (Nat.lt_succ_self n)))

/-- The completed gauge map is a linear equivalence over k[[t]], not just an existence of jets. -/
def compatibleGaugeEquiv (F : ℕ → PowerSeries (Module.End k V))
    (hF₀ : constantCoeff (F 1) = 1) :
    PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k V :=
  operatorUnitEquiv (compatibleUnit F hF₀)

theorem compatibleGaugeEquiv_intertwines {F : ℕ → PowerSeries (Module.End k V)}
    (hF : Compatible F) (hF₀ : constantCoeff (F 1) = 1)
    (B C : PowerSeriesModule k (V →ₗ[k] V →ₗ[k] V))
    (hBC : ∀ N x y, AgreeBelow N
      (operator (F N) (PowerSeriesModule.extendBinary B x y))
      (PowerSeriesModule.extendBinary C (operator (F N) x) (operator (F N) y)))
    (x y : PowerSeriesModule k V) :
    compatibleGaugeEquiv F hF₀ (PowerSeriesModule.extendBinary B x y) =
      PowerSeriesModule.extendBinary C (compatibleGaugeEquiv F hF₀ x) (compatibleGaugeEquiv F hF₀ y) :=
  compatibleLimit_intertwines hF B C hBC x y

end EnvelopingIsomorphism.Deformation.Gauge
