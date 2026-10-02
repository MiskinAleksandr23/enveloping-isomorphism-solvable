import EnvelopingIsomorphism.FormalSeries.Endomorphism
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

/-!
Compatible finite-order corrections give one genuine complete gauge operator.
The construction is coefficientwise and does not choose unrelated isomorphisms
at different truncation orders.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries
open EnvelopingIsomorphism.FormalSeries

variable {R : Type*} [Ring R]

/-- Consecutive approximations agree in all previously settled coefficients. -/
def Compatible (F : ℕ → PowerSeries R) : Prop :=
  ∀ N i, i < N → coeff i (F N) = coeff i (F (N + 1))

theorem Compatible.coeff_mono {F : ℕ → PowerSeries R} (hF : Compatible F)
    {a b i : ℕ} (hab : a ≤ b) (hi : i < a) : coeff i (F a) = coeff i (F b) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih => exact ih.trans (hF b i (hi.trans_le hab))

/-- The nth coefficient is read at a stage at which it has settled. -/
def compatibleLimit (F : ℕ → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => coeff n (F (n + 1))

@[simp] theorem coeff_compatibleLimit (F : ℕ → PowerSeries R) (n : ℕ) :
    coeff n (compatibleLimit F) = coeff n (F (n + 1)) := PowerSeries.coeff_mk _ _

theorem compatibleLimit_coeff {F : ℕ → PowerSeries R} (hF : Compatible F)
    (N i : ℕ) (hi : i < N) : coeff i (compatibleLimit F) = coeff i (F N) := by
  rw [coeff_compatibleLimit]
  exact hF.coeff_mono (Nat.succ_le_of_lt hi) (Nat.lt_succ_self i)

theorem compatibleLimit_toJet {F : ℕ → PowerSeries R} (hF : Compatible F) (N : ℕ) :
    toJet N (compatibleLimit F) = toJet N (F N) := by
  rw [toJet_eq_iff]
  exact compatibleLimit_coeff hF N

theorem compatibleLimit_unique {F : ℕ → PowerSeries R} (hF : Compatible F)
    {G : PowerSeries R} (hG : ∀ N, toJet N G = toJet N (F N)) : G = compatibleLimit F := by
  ext n
  exact ((toJet_eq_iff.mp (hG (n + 1))) n (Nat.lt_succ_self n)).trans
    (compatibleLimit_coeff hF (n + 1) n (Nat.lt_succ_self n)).symm

theorem compatibleLimit_constantCoeff (F : ℕ → PowerSeries R) :
    constantCoeff (compatibleLimit F) = constantCoeff (F 1) := by
  simpa only [coeff_zero_eq_constantCoeff] using coeff_compatibleLimit F 0

/-- A compatible sequence starting at identity modulo t has a genuine unit limit. -/
def compatibleUnit (F : ℕ → PowerSeries R) (hF₀ : constantCoeff (F 1) = 1) :
    (PowerSeries R)ˣ := unitOfConstantOne (compatibleLimit F)
      ((compatibleLimit_constantCoeff F).trans hF₀)

@[simp] theorem coe_compatibleUnit (F : ℕ → PowerSeries R) (hF₀ : constantCoeff (F 1) = 1) :
    (compatibleUnit F hF₀ : PowerSeries R) = compatibleLimit F := rfl

/-- Compose corrections on the left, in their actual noncommutative order. -/
def partialCorrections (C : ℕ → PowerSeries R) : ℕ → PowerSeries R
  | 0 => 1
  | N + 1 => C N * partialCorrections C N

theorem partialCorrections_compatible (C : ℕ → PowerSeries R)
    (hC : ∀ N, toJet (N + 1) (C N) = 1) : Compatible (partialCorrections C) := by
  intro N i hi
  have hCN : toJet N (C N) = 1 := by
    rw [← map_one (toJet N), toJet_eq_iff]
    intro j hj
    have hc := (toJet_eq_iff.mp ((hC N).trans (map_one (toJet (N + 1))).symm)) j (by omega)
    exact hc
  have hs : toJet N (partialCorrections C (N + 1)) = toJet N (partialCorrections C N) := by
    rw [partialCorrections, map_mul, hCN, one_mul]
  exact ((toJet_eq_iff.mp hs) i hi).symm

theorem partialCorrections_constantCoeff (C : ℕ → PowerSeries R)
    (hC : ∀ N, toJet (N + 1) (C N) = 1) : constantCoeff (partialCorrections C 1) = 1 := by
  have hc := (toJet_eq_iff.mp ((hC 0).trans (map_one (toJet 1)).symm)) 0 (by omega)
  simpa only [partialCorrections, mul_one, coeff_zero_eq_constantCoeff, map_one] using hc

/-- An infinite sequence of successively higher-order corrections defines one unit. -/
def correctionUnit (C : ℕ → PowerSeries R) (hC : ∀ N, toJet (N + 1) (C N) = 1) :
    (PowerSeries R)ˣ := compatibleUnit (partialCorrections C) (partialCorrections_constantCoeff C hC)

theorem correctionUnit_toJet (C : ℕ → PowerSeries R) (hC : ∀ N, toJet (N + 1) (C N) = 1)
    (N : ℕ) : toJet N (correctionUnit C hC : PowerSeries R) = toJet N (partialCorrections C N) :=
  compatibleLimit_toJet (partialCorrections_compatible C hC) N

section ModuleAction

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Compatible exact finite-order transports converge to an actual equality of vector series. -/
theorem actV_compatibleLimit {F : ℕ → PowerSeries (Module.End k V)} (hF : Compatible F)
    (x y : PowerSeriesModule k V)
    (hxy : ∀ N i, i < N → PowerSeriesModule.coeffV i (PowerSeriesModule.actV (F N) x) =
      PowerSeriesModule.coeffV i y) : PowerSeriesModule.actV (compatibleLimit F) x = y := by
  apply PowerSeriesModule.ext
  intro n
  calc
    PowerSeriesModule.coeffV n (PowerSeriesModule.actV (compatibleLimit F) x) =
        PowerSeriesModule.coeffV n (PowerSeriesModule.actV (F (n + 1)) x) := by
      rw [PowerSeriesModule.coeffV_actV, PowerSeriesModule.coeffV_actV]
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ hij
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [compatibleLimit_coeff hF (n + 1) i (by omega)]
    _ = PowerSeriesModule.coeffV n y := hxy (n + 1) n (Nat.lt_succ_self n)

end ModuleAction

end EnvelopingIsomorphism.Deformation.Gauge
