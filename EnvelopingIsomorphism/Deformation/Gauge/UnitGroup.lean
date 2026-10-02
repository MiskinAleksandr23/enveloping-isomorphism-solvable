import EnvelopingIsomorphism.Deformation.Gauge.NearIdentity
import Mathlib.Algebra.Group.Subgroup.Defs

/-! The actual group of formal operator units equal to identity modulo t. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries

variable (R : Type*) [Ring R]

def identitySubgroup : Subgroup (PowerSeries R)ˣ where
  carrier F := NearIdentity 1 (F : PowerSeries R)
  one_mem' := nearIdentity_one 1
  mul_mem' hF hG := hF.mul hG
  inv_mem' hF := hF.inv

abbrev GaugeUnit : Type _ := identitySubgroup R

namespace GaugeUnit

variable {R}

def series (F : GaugeUnit R) : PowerSeries R := ((F : (PowerSeries R)ˣ) : PowerSeries R)

@[simp] theorem series_one : series (1 : GaugeUnit R) = 1 := rfl
@[simp] theorem series_mul (F G : GaugeUnit R) : series (F * G) = series F * series G := rfl

@[simp] theorem series_inv (F : GaugeUnit R) :
    series (F⁻¹) = (↑((F : (PowerSeries R)ˣ)⁻¹) : PowerSeries R) := rfl

theorem near_one (F : GaugeUnit R) : NearIdentity 1 F.series := F.property

@[simp] theorem constantCoeff_series (F : GaugeUnit R) : constantCoeff F.series = 1 := by
  have h := F.near_one.coeff 0 (by omega)
  simpa only [coeff_zero_eq_constantCoeff, map_one] using h

theorem corrected_near {N : ℕ} (hN : 0 < N) (G H B : GaugeUnit R)
    (hG : NearIdentity N G.series) (hH : NearIdentity N H.series) (hB : NearIdentity N B.series)
    (hcoeff : coeff N G.series = coeff N H.series + coeff N B.series) :
    NearIdentity (N + 1) (B⁻¹ * G * H⁻¹).series :=
  corrected_residual_nearIdentity hN G.val H.val B.val hG hH hB hcoeff

end GaugeUnit

end EnvelopingIsomorphism.Deformation.Gauge
