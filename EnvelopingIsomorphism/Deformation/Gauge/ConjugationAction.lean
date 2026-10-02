import EnvelopingIsomorphism.Deformation.Gauge.ElementaryOperators

/-! The genuine conjugation action on complete coefficient families satisfies
the unit, multiplication, and inverse laws. No global action instance is chosen. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

@[simp] theorem operatorUnitEquiv_one :
    operatorUnitEquiv (1 : (PowerSeries (Module.End k V))ˣ) =
      LinearEquiv.refl (PowerSeries k) (PowerSeriesModule k V) := by
  apply LinearEquiv.ext
  intro x
  change operator (1 : PowerSeries (Module.End k V)) x = x
  rw [operator_one]
  rfl

theorem operatorUnitEquiv_mul (F G : (PowerSeries (Module.End k V))ˣ) :
    operatorUnitEquiv (F * G) = (operatorUnitEquiv G).trans (operatorUnitEquiv F) := by
  apply LinearEquiv.ext
  intro x
  change operator ((F : PowerSeries (Module.End k V)) * (G : PowerSeries (Module.End k V))) x =
    operator (F : PowerSeries (Module.End k V)) (operator (G : PowerSeries (Module.End k V)) x)
  rw [operator_mul]
  rfl

/-- Equality of the actual extended bilinear maps, not merely evaluation at
one choice of inputs. -/
theorem extendBinary_conjugateBinarySeries_eq (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) :
    extendBinary (conjugateBinarySeries G B) = conjugate (operatorUnitEquiv G) (extendBinary B) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact extendBinary_conjugateBinarySeries G B x y

@[simp] theorem conjugateBinarySeries_one (B : PowerSeriesModule k (Binary k V)) :
    conjugateBinarySeries (1 : (PowerSeries (Module.End k V))ˣ) B = B := by
  apply extendBinary_injective
  rw [extendBinary_conjugateBinarySeries_eq, operatorUnitEquiv_one, conjugate_refl]

/-- Multiplication of formal units acts in its actual left-action order. -/
theorem conjugateBinarySeries_mul (F G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) :
    conjugateBinarySeries (F * G) B = conjugateBinarySeries F (conjugateBinarySeries G B) := by
  apply extendBinary_injective
  rw [extendBinary_conjugateBinarySeries_eq, extendBinary_conjugateBinarySeries_eq,
    extendBinary_conjugateBinarySeries_eq, operatorUnitEquiv_mul, conjugate_trans]

@[simp] theorem conjugateBinarySeries_inv (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) :
    conjugateBinarySeries G⁻¹ (conjugateBinarySeries G B) = B := by
  rw [← conjugateBinarySeries_mul, inv_mul_cancel, conjugateBinarySeries_one]

@[simp] theorem conjugateBinarySeries_inv_right (G : (PowerSeries (Module.End k V))ˣ)
    (B : PowerSeriesModule k (Binary k V)) :
    conjugateBinarySeries G (conjugateBinarySeries G⁻¹ B) = B := by
  rw [← conjugateBinarySeries_mul, mul_inv_cancel, conjugateBinarySeries_one]

end EnvelopingIsomorphism.Deformation.Gauge
