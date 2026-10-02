import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Coefficientwise maps and derivations on the outer power-series algebra

These maps are linear over the full power-series scalar ring. The variable of these
series is fixed by the extended derivation: differentiation acts on the coefficients.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PowerSeriesAlgebra

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]

/-- Coefficientwise extension of a linear map to the full power-series scalar ring. -/
def mapLinear (f : A →ₗ[k] B) : PowerSeries A →ₗ[PowerSeries k] PowerSeries B where
  toFun p := PowerSeries.mk (fun n ↦ f (PowerSeries.coeff n p))
  map_add' p q := by ext n; simp
  map_smul' c p := by
    ext n
    simp only [PowerSeries.coeff_mk, RingHom.id_apply, Algebra.smul_def,
      PowerSeries.algebraMap_apply'', PowerSeries.coeff_mul,
      PowerSeries.coeff_map, PowerSeries.coeff_mk, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simpa only [Algebra.smul_def] using
      f.map_smul (PowerSeries.coeff d.1 c) (PowerSeries.coeff d.2 p)

@[simp] theorem coeff_mapLinear (f : A →ₗ[k] B) (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (mapLinear f p) = f (PowerSeries.coeff n p) := by
  simp [mapLinear]

@[simp] theorem mapLinear_C (f : A →ₗ[k] B) (a : A) :
    mapLinear f (PowerSeries.C a) = PowerSeries.C (f a) := by
  ext n
  by_cases h : n = 0 <;> simp [PowerSeries.coeff_C, h]

/-- Coefficientwise extension of an algebra map over the full power-series scalar ring. -/
def mapAlgHom (f : A →ₐ[k] B) : PowerSeries A →ₐ[PowerSeries k] PowerSeries B where
  toRingHom := PowerSeries.map f.toRingHom
  commutes' p := by
    ext n
    simp [PowerSeries.algebraMap_apply'']

@[simp] theorem coeff_mapAlgHom (f : A →ₐ[k] B) (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (mapAlgHom f p) = f (PowerSeries.coeff n p) := rfl

@[simp] theorem mapAlgHom_C (f : A →ₐ[k] B) (a : A) :
    mapAlgHom f (PowerSeries.C a) = PowerSeries.C (f a) :=
  PowerSeries.map_C _ _

/-- The scalar-valued specialization, using the canonical scalar algebra on the target. -/
def augmentation (ε : A →ₐ[k] k) : PowerSeries A →ₐ[PowerSeries k] PowerSeries k where
  toRingHom := PowerSeries.map ε.toRingHom
  commutes' p := by
    ext n
    simp [PowerSeries.algebraMap_apply'']

@[simp] theorem coeff_augmentation (ε : A →ₐ[k] k) (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (augmentation ε p) = ε (PowerSeries.coeff n p) := rfl

@[simp] theorem augmentation_C (ε : A →ₐ[k] k) (a : A) :
    augmentation ε (PowerSeries.C a) = PowerSeries.C (ε a) :=
  PowerSeries.map_C _ _

/-- Equality of constant terms means equality modulo the outer scalar parameter. -/
theorem exists_eq_add_parameter_smul (p q : PowerSeries A)
    (h : PowerSeries.constantCoeff p = PowerSeries.constantCoeff q) :
    ∃ w : PowerSeries A, p = q + (PowerSeries.X : PowerSeries k) • w := by
  have hz : PowerSeries.constantCoeff (p - q) = 0 := by simp [h]
  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.mpr hz
  refine ⟨w, ?_⟩
  rw [Algebra.smul_def, PowerSeries.algebraMap_apply'', PowerSeries.map_X]
  rw [← hw]
  simp [sub_eq_add_neg, add_left_comm]

/-- Extend a coefficient derivation while fixing every power-series scalar. -/
def derivation (D : Derivation k A A) :
    Derivation (PowerSeries k) (PowerSeries A) (PowerSeries A) where
  __ := mapLinear D.toLinearMap
  map_one_eq_zero' := by
    ext n
    rw [coeff_mapLinear]
    by_cases h : n = 0 <;> simp [h]
  leibniz' p q := by
    ext n
    rw [coeff_mapLinear]
    change D (PowerSeries.coeff n (p * q)) =
      PowerSeries.coeff n (p * mapLinear D.toLinearMap q + q * mapLinear D.toLinearMap p)
    rw [mul_comm q (mapLinear D.toLinearMap p)]
    simp only [PowerSeries.coeff_mul, map_sum, map_add, coeff_mapLinear,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp [Derivation.leibniz, smul_eq_mul, mul_comm]

@[simp] theorem coeff_derivation (D : Derivation k A A) (p : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (derivation D p) = D (PowerSeries.coeff n p) :=
  coeff_mapLinear D.toLinearMap p n

@[simp] theorem derivation_C (D : Derivation k A A) (a : A) :
    derivation D (PowerSeries.C a) = PowerSeries.C (D a) :=
  mapLinear_C D.toLinearMap a

end EnvelopingIsomorphism.FormalSeries.PowerSeriesAlgebra
