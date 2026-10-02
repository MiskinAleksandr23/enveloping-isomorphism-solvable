import EnvelopingIsomorphism.Deformation.Gauge.Taylor

/-! Restricted Taylor data for infinitesimal gauge velocities and its leading coefficient. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule

variable {k V₀ V₁ W₀ : Type*} [CommRing k]
variable [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
variable [AddCommGroup W₀] [Module k W₀]

/-- Taylor operations with one degree-zero velocity and positive-degree base inputs.
The actual producer supplies these normalized multilinear maps; no path or gauge
preservation statement is assumed in this data type. -/
structure TangentFamily where
  linear : V₀ →ₗ[k] W₀
  higher : TaylorFamily (k := k) (V := V₁) (W := V₀ →ₗ[k] W₀)

def tangentApply (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : PowerSeriesModule k V₁) (v : PowerSeriesModule k V₀) : PowerSeriesModule k W₀ :=
  map T.linear v + linearApply (taylorApply T.higher b) v

/-- A velocity of order N is mapped at order N by precisely the linear tangent map. -/
theorem tangentApply_leading (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : PowerSeriesModule k V₁) (v : PowerSeriesModule k V₀) (N : ℕ)
    (hv : ∀ i, i < N → coeffV i v = 0) :
    coeffV N (tangentApply T b v) = T.linear (coeffV N v) := by
  rw [tangentApply, coeffV_add, coeffV_map, coeffV_linearApply]
  have hzero : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
      (coeffV ij.1 (taylorApply T.higher b)) (coeffV ij.2 v)) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hi : i = 0
    · subst i
      rw [taylorApply_constantCoeff, LinearMap.zero_apply]
    · rw [hv j (by omega), map_zero]
  rw [hzero, add_zero]

theorem tangentApply_preserves_order
    (T : TangentFamily (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀))
    (b : PowerSeriesModule k V₁) (v : PowerSeriesModule k V₀) (N : ℕ)
    (hv : ∀ i, i < N → coeffV i v = 0) :
    ∀ i, i < N → coeffV i (tangentApply T b v) = 0 := by
  intro i hi
  rw [tangentApply_leading T b v i (fun j hj => hv j (hj.trans hi)), hv i hi, map_zero]

end EnvelopingIsomorphism.Deformation.Gauge
