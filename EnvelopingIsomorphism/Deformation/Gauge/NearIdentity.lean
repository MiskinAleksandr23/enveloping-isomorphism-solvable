import EnvelopingIsomorphism.Deformation.Gauge.CompatibleCorrections
import Mathlib.Tactic.Abel

/-! Finite-order linearization of the genuine noncommutative formal unit group. -/

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries
open EnvelopingIsomorphism.FormalSeries

variable {R : Type*} [Ring R]

def NearIdentity (N : ℕ) (F : PowerSeries R) : Prop := toJet N F = 1

theorem NearIdentity.coeff {N : ℕ} {F : PowerSeries R} (hF : NearIdentity N F)
    (i : ℕ) (hi : i < N) : coeff i F = coeff i (1 : PowerSeries R) :=
  (toJet_eq_iff.mp (hF.trans (map_one (toJet N)).symm)) i hi

theorem NearIdentity.mono {N M : ℕ} {F : PowerSeries R} (hF : NearIdentity M F) (hNM : N ≤ M) :
    NearIdentity N F := by
  change toJet N F = 1
  rw [← map_one (toJet N), toJet_eq_iff]
  exact fun i hi => hF.coeff i (hi.trans_le hNM)

@[simp] theorem nearIdentity_one (N : ℕ) : NearIdentity N (1 : PowerSeries R) := map_one _

theorem NearIdentity.mul {N : ℕ} {F G : PowerSeries R}
    (hF : NearIdentity N F) (hG : NearIdentity N G) : NearIdentity N (F * G) := by
  change toJet N (F * G) = 1
  rw [map_mul, hF, hG, one_mul]

theorem NearIdentity.inv {N : ℕ} {F : (PowerSeries R)ˣ} (hF : NearIdentity N (F : PowerSeries R)) :
    NearIdentity N (↑(F⁻¹) : PowerSeries R) := by
  have hu : toJet N (F : PowerSeries R) * toJet N (↑(F⁻¹) : PowerSeries R) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [hF, one_mul] at hu
  exact hu

/-- At positive order, multiplication adds the first nontrivial coefficients. -/
theorem coeff_mul_nearIdentity {N : ℕ} (hN : 0 < N) {F G : PowerSeries R}
    (hF : NearIdentity N F) (hG : NearIdentity N G) :
    coeff N (F * G) = coeff N F + coeff N G := by
  have hz : coeff N ((F - 1) * (G - 1)) = 0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hi : i < N
    · rw [map_sub, hF.coeff i hi, sub_self, zero_mul]
    · have hj : j < N := by omega
      rw [(PowerSeries.coeff (R := R) j).map_sub G 1, hG.coeff j hj, sub_self, mul_zero]
  have he : (F - 1) * (G - 1) = F * G - F - G + 1 := by noncomm_ring
  rw [he, map_add, map_sub, map_sub] at hz
  have hone : coeff N (1 : PowerSeries R) = 0 := by simp [coeff_one, Nat.ne_of_gt hN]
  rw [hone, add_zero, sub_sub] at hz
  exact sub_eq_zero.mp hz

theorem coeff_inv_nearIdentity {N : ℕ} (hN : 0 < N) {F : (PowerSeries R)ˣ}
    (hF : NearIdentity N (F : PowerSeries R)) :
    coeff N (↑(F⁻¹) : PowerSeries R) = -coeff N (F : PowerSeries R) := by
  have hc := coeff_mul_nearIdentity hN hF hF.inv
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hc
  have hone : coeff N (1 : PowerSeries R) = 0 := by simp [coeff_one, Nat.ne_of_gt hN]
  rw [hone] at hc
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact hc.symm

/-- Killing the next coefficient really advances the congruence by one order. -/
theorem NearIdentity.succ_of_coeff_zero {N : ℕ} (hN : 0 < N) {F : PowerSeries R}
    (hF : NearIdentity N F) (hnext : PowerSeries.coeff N F = 0) : NearIdentity (N + 1) F := by
  change toJet (N + 1) F = 1
  rw [← map_one (toJet (N + 1)), toJet_eq_iff]
  intro i hi
  by_cases h : i < N
  · exact hF.coeff i h
  · have hEq : i = N := by omega
    subst i
    rw [hnext]
    simp [coeff_one, Nat.ne_of_gt hN]

/-- Remove the two leading pieces from a residual target gauge. -/
theorem corrected_residual_nearIdentity {N : ℕ} (hN : 0 < N)
    (G H B : (PowerSeries R)ˣ)
    (hG : NearIdentity N (G : PowerSeries R))
    (hH : NearIdentity N (H : PowerSeries R))
    (hB : NearIdentity N (B : PowerSeries R))
    (hcoeff : coeff N (G : PowerSeries R) = coeff N (H : PowerSeries R) + coeff N (B : PowerSeries R)) :
    NearIdentity (N + 1) (↑(B⁻¹ * G * H⁻¹) : PowerSeries R) := by
  have hBG : NearIdentity N ((↑(B⁻¹) : PowerSeries R) * (G : PowerSeries R)) := hB.inv.mul hG
  have hall : NearIdentity N (↑(B⁻¹ * G * H⁻¹) : PowerSeries R) := hBG.mul hH.inv
  apply NearIdentity.succ_of_coeff_zero hN hall
  change coeff N (((↑(B⁻¹) : PowerSeries R) * (G : PowerSeries R)) * (↑(H⁻¹) : PowerSeries R)) = 0
  rw [coeff_mul_nearIdentity hN hBG hH.inv, coeff_mul_nearIdentity hN hB.inv hG,
    coeff_inv_nearIdentity hN hB, coeff_inv_nearIdentity hN hH, hcoeff]
  abel

end EnvelopingIsomorphism.Deformation.Gauge
