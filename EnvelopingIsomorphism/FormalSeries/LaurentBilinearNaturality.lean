import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition

/-! Naturality and coefficient linearity of the actual Laurent bilinear convolution. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

set_option backward.isDefEq.respectTransparency false

universe u v
variable {k : Type u} [CommRing k]
  {V W X Y : Type v} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y]

theorem extendBilinear_precomp_right (f : V →ₗ[k] W →ₗ[k] X) (g : Y →ₗ[k] W)
    (x : LaurentModule k V) (y : LaurentModule k Y) :
    extendBilinear f x (map g y) = extendBilinear (f.compl₂ g) x y := by
  apply LaurentModule.ext
  intro d
  rfl

theorem extendBilinear_coeff_add (f g : V →ₗ[k] W →ₗ[k] X)
    (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBilinear (f + g) x y = extendBilinear f x y + extendBilinear g x y := by
  have h : bilinearMultilinear (f + g) = bilinearMultilinear f + bilinearMultilinear g := by
    ext a
    rfl
  change extendScalars (bilinearMultilinear (f + g)) _ = _
  rw [h, extendScalars_add]
  rfl

theorem extendBilinear_coeff_neg (f : V →ₗ[k] W →ₗ[k] X)
    (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBilinear (-f) x y = -extendBilinear f x y := by
  have h := extendBilinear_postcomp f (-LinearMap.id) x y
  have hf : f.compr₂ (-LinearMap.id) = -f := by ext a b; rfl
  rw [hf] at h
  rw [← h]
  apply LaurentModule.ext
  intro d
  rfl

theorem extendBilinear_coeff_sub (f g : V →ₗ[k] W →ₗ[k] X)
    (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBilinear (f - g) x y = extendBilinear f x y - extendBilinear g x y := by
  simp only [sub_eq_add_neg, extendBilinear_coeff_add, extendBilinear_coeff_neg]

theorem extendBilinear_coeff_flip (f : V →ₗ[k] W →ₗ[k] X)
    (x : LaurentModule k W) (y : LaurentModule k V) :
    extendBilinear f.flip x y = extendBilinear f y x := by
  have h : restrictBilinear (extendBilinear f.flip) =
      (restrictBilinear (extendBilinear f)).flip := by
    apply bilinear_ext_of_bounded _ _ 0
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0) (extendBilinear f.flip x y)
      simpa only [add_zero] using boundedBelow_extendBilinear f.flip x y hx hy
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0) (extendBilinear f y x)
      simpa only [add_zero, add_comm b c] using boundedBelow_extendBilinear f y x hy hx
    · intro e d x y
      change extendBilinear f.flip (single e x) (single d y) =
        extendBilinear f (single d y) (single e x)
      rw [extendBilinear_single, extendBilinear_single, add_comm e d]
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end EnvelopingIsomorphism.FormalSeries.LaurentModule
