import EnvelopingIsomorphism.FormalSeries.Module
import Mathlib.LinearAlgebra.Prod

/-!
# Actual Laurent modules commute with finite products

The inverse of the product equivalence is the sum of the two coefficientwise
inclusions. Inputs may have different lower bounds: their minimum bounds the
result. No assertion about infinite products or algebraic tensor products is
used.
-/

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

noncomputable section

universe u v w

/-- Laurent series of pairs are canonically pairs of actual Laurent series. -/
def prodEquiv (k : Type u) [CommRing k] (U : Type v) (V : Type w)
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] :
    LaurentModule k (U × V) ≃ₗ[LaurentSeries k] LaurentModule k U × LaurentModule k V :=
  { (map (LinearMap.fst k U V)).prod (map (LinearMap.snd k U V)) with
    invFun p := map (LinearMap.inl k U V) p.1 + map (LinearMap.inr k U V) p.2
    left_inv x := by
      apply LaurentModule.ext
      intro d
      simp
    right_inv p := by
      apply Prod.ext
      · apply LaurentModule.ext
        intro d
        simp
      · apply LaurentModule.ext
        intro d
        simp }

variable {k : Type u} [CommRing k]
variable {U : Type v} {V : Type w} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]

@[simp] theorem prodEquiv_apply (x : LaurentModule k (U × V)) :
    prodEquiv k U V x = (map (LinearMap.fst k U V) x, map (LinearMap.snd k U V) x) := rfl

@[simp] theorem prodEquiv_symm_apply (x : LaurentModule k U) (y : LaurentModule k V) :
    (prodEquiv k U V).symm (x, y) =
      map (LinearMap.inl k U V) x + map (LinearMap.inr k U V) y := rfl

@[simp] theorem coeff_prodEquiv_fst (x : LaurentModule k (U × V)) (d : ℤ) :
    coeff (prodEquiv k U V x).1 d = (coeff x d).1 := rfl

@[simp] theorem coeff_prodEquiv_snd (x : LaurentModule k (U × V)) (d : ℤ) :
    coeff (prodEquiv k U V x).2 d = (coeff x d).2 := rfl

@[simp] theorem coeff_prodEquiv_symm (x : LaurentModule k U) (y : LaurentModule k V) (d : ℤ) :
    coeff ((prodEquiv k U V).symm (x, y)) d = (coeff x d, coeff y d) := by
  simp

@[simp] theorem prodEquiv_single (d : ℤ) (u : U) (v : V) :
    prodEquiv k U V (single d (u, v)) = (single d u, single d v) := by
  rw [prodEquiv_apply, map_single, map_single]
  rfl

@[simp] theorem prodEquiv_symm_single (d : ℤ) (u : U) (v : V) :
    (prodEquiv k U V).symm (single d u, single d v) = single d (u, v) := by
  apply (prodEquiv k U V).injective
  rw [LinearEquiv.apply_symm_apply, prodEquiv_single]

theorem boundedBelow_prodEquiv_iff (b : ℤ) (x : LaurentModule k (U × V)) :
    BoundedBelow b x ↔ BoundedBelow b (prodEquiv k U V x).1 ∧
      BoundedBelow b (prodEquiv k U V x).2 := by
  constructor
  · intro hx
    exact ⟨boundedBelow_map (LinearMap.fst k U V) hx,
      boundedBelow_map (LinearMap.snd k U V) hx⟩
  · rintro ⟨hU, hV⟩ d hd
    exact Prod.ext (hU d hd) (hV d hd)

/-- Independent lower bounds of the two inputs combine by taking their minimum. -/
theorem boundedBelow_prodEquiv_symm {b c : ℤ} {x : LaurentModule k U} {y : LaurentModule k V}
    (hx : BoundedBelow b x) (hy : BoundedBelow c y) :
    BoundedBelow (min b c) ((prodEquiv k U V).symm (x, y)) := by
  intro d hd
  rw [coeff_prodEquiv_symm, hx d (lt_of_lt_of_le hd (min_le_left b c)),
    hy d (lt_of_lt_of_le hd (min_le_right b c))]
  rfl

section LinearMaps

variable {X Y Z : Type*} [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]

theorem prodEquiv_map_prod (f : X →ₗ[k] U) (g : X →ₗ[k] V) (x : LaurentModule k X) :
    prodEquiv k U V (map (f.prod g) x) = (map f x, map g x) := by
  apply Prod.ext
  · apply LaurentModule.ext
    intro d
    rfl
  · apply LaurentModule.ext
    intro d
    rfl

theorem map_coprod_prodEquiv_symm (f : U →ₗ[k] X) (g : V →ₗ[k] X)
    (x : LaurentModule k U) (y : LaurentModule k V) :
    map (f.coprod g) ((prodEquiv k U V).symm (x, y)) = map f x + map g y := by
  apply LaurentModule.ext
  intro d
  rw [coeff_map, coeff_prodEquiv_symm]
  rfl

theorem prodEquiv_map_prodMap (f : U →ₗ[k] X) (g : V →ₗ[k] Y)
    (x : LaurentModule k U) (y : LaurentModule k V) :
    prodEquiv k X Y (map (f.prodMap g) ((prodEquiv k U V).symm (x, y))) =
      (map f x, map g y) := by
  apply Prod.ext
  · apply LaurentModule.ext
    intro d
    simp
  · apply LaurentModule.ext
    intro d
    simp

/-- The actual Laurent extension of a general 2-by-2 block linear map. -/
theorem prodEquiv_map_block (f₁₁ : U →ₗ[k] X) (f₁₂ : V →ₗ[k] X)
    (f₂₁ : U →ₗ[k] Y) (f₂₂ : V →ₗ[k] Y)
    (x : LaurentModule k U) (y : LaurentModule k V) :
    prodEquiv k X Y
      (map ((f₁₁.coprod f₁₂).prod (f₂₁.coprod f₂₂)) ((prodEquiv k U V).symm (x, y))) =
      (map f₁₁ x + map f₁₂ y, map f₂₁ x + map f₂₂ y) := by
  rw [prodEquiv_map_prod, map_coprod_prodEquiv_symm, map_coprod_prodEquiv_symm]

end LinearMaps

end

end EnvelopingIsomorphism.FormalSeries.LaurentModule
