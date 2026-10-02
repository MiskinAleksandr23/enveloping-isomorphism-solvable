import EnvelopingIsomorphism.Deformation.Gauge.OperatorLimit

/-! Closedness of the first unsettled coefficient of two genuine quadratic MC equations. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def quadraticCurvature (d : V →ₗ[k] W) (B : V →ₗ[k] V →ₗ[k] W)
    (b : PowerSeriesModule k V) : PowerSeriesModule k W :=
  map d b + applyBilinear B b b

def MCSeries (d : V →ₗ[k] W) (B : V →ₗ[k] V →ₗ[k] W) :=
  {b : PowerSeriesModule k V // coeffV 0 b = 0 ∧ quadraticCurvature d B b = 0}

theorem quadratic_coeff_agree (B : V →ₗ[k] V →ₗ[k] W) (N : ℕ)
    (b c : PowerSeriesModule k V) (hb : coeffV 0 b = 0) (hc : coeffV 0 c = 0)
    (hbc : AgreeBelow N b c) :
    coeffV N (applyBilinear B b b) = coeffV N (applyBilinear B c c) := by
  rw [coeffV_applyBilinear, coeffV_applyBilinear]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : i = 0
  · subst i
    rw [hb, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  · by_cases hj : j = 0
    · subst j
      rw [hb, hc, map_zero, map_zero]
    · rw [hbc i (by omega), hbc j (by omega)]

/-- The nonlinear quadratic term drops out at the leading difference. -/
theorem quadratic_MC_leading_closed (d : V →ₗ[k] W) (B : V →ₗ[k] V →ₗ[k] W) (N : ℕ)
    (b c : PowerSeriesModule k V) (hb : coeffV 0 b = 0) (hc : coeffV 0 c = 0)
    (hbc : AgreeBelow N b c) (hMb : quadraticCurvature d B b = 0)
    (hMc : quadraticCurvature d B c = 0) : d (coeffV N b - coeffV N c) = 0 := by
  have h₁ := congrArg (coeffV N) hMb
  have h₂ := congrArg (coeffV N) hMc
  simp only [quadraticCurvature, coeffV_add, coeffV_map, coeffV_zero] at h₁ h₂
  rw [quadratic_coeff_agree B N b c hb hc hbc] at h₁
  have hd : d (coeffV N b) = d (coeffV N c) := add_right_cancel (h₁.trans h₂.symm)
  rw [map_sub, hd, sub_self]

theorem MCSeries.leading_closed {d : V →ₗ[k] W} {B : V →ₗ[k] V →ₗ[k] W}
    (b c : MCSeries d B) (N : ℕ) (hbc : AgreeBelow N b.val c.val) :
    d (coeffV N b.val - coeffV N c.val) = 0 :=
  quadratic_MC_leading_closed d B N b.val c.val b.property.1 c.property.1 hbc
    b.property.2 c.property.2

end EnvelopingIsomorphism.Deformation.Gauge
