import EnvelopingIsomorphism.FormalSeries.Module
import Mathlib.RingTheory.Derivation.Basic

/-!
# Coefficientwise algebra maps and derivations on actual Laurent series

The scalar extension here is `LaurentSeries A`, with convolution multiplication
and one common lower bound for the support. It is not an algebraic tensor
product. The Laurent scalar action is induced by the coefficient algebra map.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentAlgebra

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- Apply a ring homomorphism to every coefficient of a Laurent series. -/
def mapRingHom (f : A →+* B) : LaurentSeries A →+* LaurentSeries B where
  toFun x := x.map f
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem coeff_mapRingHom (f : A →+* B) (x : LaurentSeries A) (n : ℤ) :
    (mapRingHom f x).coeff n = f (x.coeff n) := rfl

/-- Laurent coefficients extend the algebra map by convolution. -/
scoped instance algebra : Algebra (LaurentSeries k) (LaurentSeries A) :=
  (mapRingHom (algebraMap k A)).toAlgebra

@[simp] theorem coeff_algebraMap (x : LaurentSeries k) (n : ℤ) :
    (algebraMap (LaurentSeries k) (LaurentSeries A) x).coeff n =
      algebraMap k A (x.coeff n) := rfl

/-- The scalar action agrees with the previously constructed Laurent module. -/
def moduleEquiv : LaurentModule k A ≃ₗ[LaurentSeries k] LaurentSeries A where
  toEquiv := (HahnModule.of k).symm
  map_add' _ _ := rfl
  map_smul' a x := by
    apply HahnSeries.ext
    funext n
    change (((HahnModule.of k).symm (a • x)).coeff n) =
      (a.map (algebraMap k A) * (HahnModule.of k).symm x).coeff n
    have hs : (a.map (algebraMap k A)).support ⊆ a.support := by
      intro d hd
      change algebraMap k A (a.coeff d) ≠ 0 at hd
      exact fun h ↦ hd (by rw [h, map_zero])
    rw [HahnModule.coeff_smul]
    rw [HahnSeries.coeff_mul_left' a.isPWO_support hs]
    apply Finset.sum_congr rfl
    intro p hp
    exact Algebra.smul_def _ _

@[simp] theorem coeff_moduleEquiv (x : LaurentModule k A) (n : ℤ) :
    (moduleEquiv x).coeff n = LaurentModule.coeff x n := rfl

/-- Coefficientwise extension is linear over the complete Laurent scalar field. -/
def mapLinear (f : A →ₗ[k] B) : LaurentSeries A →ₗ[LaurentSeries k] LaurentSeries B :=
  moduleEquiv.toLinearMap.comp ((LaurentModule.map f).comp moduleEquiv.symm.toLinearMap)

@[simp] theorem coeff_mapLinear (f : A →ₗ[k] B) (x : LaurentSeries A) (n : ℤ) :
    (mapLinear f x).coeff n = f (x.coeff n) := rfl

theorem support_mapLinear_subset (f : A →ₗ[k] B) (x : LaurentSeries A) :
    (mapLinear f x).support ⊆ x.support := by
  intro n hn
  change f (x.coeff n) ≠ 0 at hn
  exact fun h ↦ hn (by rw [h, map_zero])

@[simp] theorem mapLinear_single (f : A →ₗ[k] B) (n : ℤ) (a : A) :
    mapLinear f (HahnSeries.single n a) = HahnSeries.single n (f a) := by
  ext m
  by_cases h : m = n <;> simp [h]

/-- Extension of a coefficient algebra homomorphism to Laurent series. -/
def mapAlgHom (f : A →ₐ[k] B) : LaurentSeries A →ₐ[LaurentSeries k] LaurentSeries B where
  __ := mapRingHom f.toRingHom
  commutes' a := by
    ext n
    change f (algebraMap k A (a.coeff n)) = algebraMap k B (a.coeff n)
    exact f.commutes _

@[simp] theorem coeff_mapAlgHom (f : A →ₐ[k] B) (x : LaurentSeries A) (n : ℤ) :
    (mapAlgHom f x).coeff n = f (x.coeff n) := rfl

@[simp] theorem mapAlgHom_single (f : A →ₐ[k] B) (n : ℤ) (a : A) :
    mapAlgHom f (HahnSeries.single n a) = HahnSeries.single n (f a) := by
  ext m
  by_cases h : m = n <;> simp [h]

@[simp] theorem mapAlgHom_C (f : A →ₐ[k] B) (a : A) :
    mapAlgHom f (HahnSeries.C a) = HahnSeries.C (f a) :=
  mapAlgHom_single f 0 a

/-- Extend a coefficient derivation while fixing every Laurent scalar. -/
def derivation (D : Derivation k A A) :
    Derivation (LaurentSeries k) (LaurentSeries A) (LaurentSeries A) where
  __ := mapLinear D.toLinearMap
  map_one_eq_zero' := by
    ext n
    change D ((1 : LaurentSeries A).coeff n) = (0 : LaurentSeries A).coeff n
    by_cases h : n = 0 <;> simp [h]
  leibniz' x y := by
    ext n
    change D ((x * y).coeff n) =
      (x * mapLinear D.toLinearMap y + y * mapLinear D.toLinearMap x).coeff n
    rw [mul_comm y (mapLinear D.toLinearMap x)]
    rw [HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add]
    rw [HahnSeries.coeff_mul_right' y.isPWO_support
      (support_mapLinear_subset D.toLinearMap y)]
    rw [HahnSeries.coeff_mul_left' x.isPWO_support
      (support_mapLinear_subset D.toLinearMap x)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp [Derivation.leibniz, smul_eq_mul, mul_comm]

@[simp] theorem coeff_derivation (D : Derivation k A A) (x : LaurentSeries A) (n : ℤ) :
    (derivation D x).coeff n = D (x.coeff n) := rfl

@[simp] theorem derivation_single (D : Derivation k A A) (n : ℤ) (a : A) :
    derivation D (HahnSeries.single n a) = HahnSeries.single n (D a) :=
  mapLinear_single D.toLinearMap n a

@[simp] theorem derivation_C (D : Derivation k A A) (a : A) :
    derivation D (HahnSeries.C a) = HahnSeries.C (D a) :=
  derivation_single D 0 a

/-- Leibniz in multiplication notation for the actual Laurent-series algebra. -/
theorem derivation_mul (D : Derivation k A A) (x y : LaurentSeries A) :
    derivation D (x * y) = x * derivation D y + y * derivation D x :=
  (derivation D).leibniz x y

section Augmentation

local instance selfAlgebra : Algebra (LaurentSeries k) (LaurentSeries k) := Algebra.id _

/-- The coefficient augmentation with the canonical self-algebra on its target.
This specialization avoids a scalar-instance ambiguity in nested series maps. -/
def augmentation (ε : A →ₐ[k] k) :
    LaurentSeries A →ₐ[LaurentSeries k] LaurentSeries k where
  __ := mapRingHom ε.toRingHom
  commutes' a := by
    ext n
    change ε (algebraMap k A (a.coeff n)) = a.coeff n
    exact ε.commutes _

@[simp] theorem coeff_augmentation (ε : A →ₐ[k] k) (x : LaurentSeries A) (n : ℤ) :
    (augmentation ε x).coeff n = ε (x.coeff n) := rfl

@[simp] theorem augmentation_C (ε : A →ₐ[k] k) (a : A) :
    augmentation ε (HahnSeries.C a) = HahnSeries.C (ε a) := by
  ext n
  by_cases h : n = 0 <;> simp [HahnSeries.C_apply, h]

end Augmentation

end EnvelopingIsomorphism.FormalSeries.LaurentAlgebra
