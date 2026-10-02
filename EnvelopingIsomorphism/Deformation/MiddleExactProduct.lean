import EnvelopingIsomorphism.Deformation.MiddleExactPerturbation
import EnvelopingIsomorphism.FormalSeries.LaurentProduct

/-!
# Middle exactness on products of actual Laurent modules

This adapter conjugates the proved Laurent middle-exactness theorem by the
canonical finite-product equivalences. It also identifies the resulting maps
with their four heterogeneous block actions. No additional complex or
perturbation theorem is constructed here.
-/

namespace EnvelopingIsomorphism.Deformation.MiddleExactProduct

noncomputable section

open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation

universe u v
variable {k : Type u} [Field k]
variable {U₁ U₂ V₁ V₂ W₁ W₂ : Type v}
  [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

/-- A formal pair-to-pair operator acting on the product of its actual Laurent modules. -/
def productAct (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂)) :
    (LaurentModule k U₁ × LaurentModule k U₂) →ₗ[LaurentSeries k]
      (LaurentModule k V₁ × LaurentModule k V₂) :=
  (LaurentModule.prodEquiv k V₁ V₂).toLinearMap.comp
    ((act A).comp (LaurentModule.prodEquiv k U₁ U₂).symm.toLinearMap)

@[simp] theorem productAct_apply (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    productAct A (x, y) = LaurentModule.prodEquiv k V₁ V₂
      (act A ((LaurentModule.prodEquiv k U₁ U₂).symm (x, y))) := rfl

theorem productAct_on_pair_series (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (x : LaurentModule k (U₁ × U₂)) :
    productAct A (LaurentModule.prodEquiv k U₁ U₂ x) =
      LaurentModule.prodEquiv k V₁ V₂ (act A x) := by
  change LaurentModule.prodEquiv k V₁ V₂
    (act A ((LaurentModule.prodEquiv k U₁ U₂).symm (LaurentModule.prodEquiv k U₁ U₂ x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Extract an operator block by constant projection and inclusion series. -/
def extractBlock {U V X Y : Type v} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y]
    (π : V →ₗ[k] Y) (A : OperatorSeries (k := k) U V) (ι : X →ₗ[k] U) :
    OperatorSeries (k := k) X Y :=
  PowerSeriesModule.linearCompose (PowerSeriesModule.single 0 π)
    (PowerSeriesModule.linearCompose A (PowerSeriesModule.single 0 ι))

theorem act_extractBlock {U V X Y : Type v} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y]
    (π : V →ₗ[k] Y) (A : OperatorSeries (k := k) U V) (ι : X →ₗ[k] U) :
    act (extractBlock π A ι) = (LaurentModule.map π).comp ((act A).comp (LaurentModule.map ι)) := by
  rw [extractBlock, ← act_comp, act_single, ← act_comp, act_single]

/-- Exact evaluation of all four blocks of an arbitrary formal pair operator. -/
theorem productAct_blocks (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    productAct A (x, y) =
      (act (extractBlock (LinearMap.fst k V₁ V₂) A (LinearMap.inl k U₁ U₂)) x +
        act (extractBlock (LinearMap.fst k V₁ V₂) A (LinearMap.inr k U₁ U₂)) y,
       act (extractBlock (LinearMap.snd k V₁ V₂) A (LinearMap.inl k U₁ U₂)) x +
        act (extractBlock (LinearMap.snd k V₁ V₂) A (LinearMap.inr k U₁ U₂)) y) := by
  simp only [productAct_apply, LaurentModule.prodEquiv_symm_apply, LaurentModule.prodEquiv_apply,
    map_add, act_extractBlock, LinearMap.comp_apply]
  rfl

/-- Constant block matrices extend to the corresponding literal block maps of Laurent modules. -/
theorem productAct_constant_blocks (f₁₁ : U₁ →ₗ[k] V₁) (f₁₂ : U₂ →ₗ[k] V₁)
    (f₂₁ : U₁ →ₗ[k] V₂) (f₂₂ : U₂ →ₗ[k] V₂)
    (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    productAct (PowerSeriesModule.single 0 ((f₁₁.coprod f₁₂).prod (f₂₁.coprod f₂₂))) (x, y) =
      (LaurentModule.map f₁₁ x + LaurentModule.map f₁₂ y,
        LaurentModule.map f₂₁ x + LaurentModule.map f₂₂ y) := by
  rw [productAct_apply, act_single, LaurentModule.prodEquiv_map_block]

section ExactnessTransport

variable {R : Type*} [Ring R]
variable {U V W U' V' W' : Type*}
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup U'] [Module R U'] [AddCommGroup V'] [Module R V']
  [AddCommGroup W'] [Module R W']

/-- Exactness transports through three proved linear equivalences and commuting squares. -/
theorem range_eq_ker_transport (eU : U ≃ₗ[R] U') (eV : V ≃ₗ[R] V') (eW : W ≃ₗ[R] W')
    (A : U →ₗ[R] V) (B : V →ₗ[R] W) (F : U' →ₗ[R] V') (G : V' →ₗ[R] W')
    (hF : ∀ u, F (eU u) = eV (A u)) (hG : ∀ v, G (eV v) = eW (B v))
    (h : LinearMap.range A = LinearMap.ker B) : LinearMap.range F = LinearMap.ker G := by
  apply le_antisymm
  · rintro _ ⟨u', rfl⟩
    have hz : B (A (eU.symm u')) = 0 := h.le ⟨eU.symm u', rfl⟩
    have hf := hF (eU.symm u')
    rw [LinearEquiv.apply_symm_apply] at hf
    change G (F u') = 0
    rw [hf, hG, hz, map_zero]
  · intro v' hv'
    have hz : B (eV.symm v') = 0 := by
      apply eW.injective
      rw [← hG, LinearEquiv.apply_symm_apply, map_zero]
      exact hv'
    obtain ⟨u, hu⟩ := h.ge hz
    refine ⟨eU u, ?_⟩
    rw [hF, hu, LinearEquiv.apply_symm_apply]

end ExactnessTransport

/-- The proved perturbation theorem on the literal products of Laurent modules. -/
theorem laurent_middle_exact_product
    (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂))
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B)) :
    LinearMap.range (productAct A) = LinearMap.ker (productAct B) :=
  range_eq_ker_transport (LaurentModule.prodEquiv k U₁ U₂)
    (LaurentModule.prodEquiv k V₁ V₂) (LaurentModule.prodEquiv k W₁ W₂)
    (act A) (act B) (productAct A) (productAct B)
    (productAct_on_pair_series A) (productAct_on_pair_series B)
    (laurent_middle_exact A B hBA h0)

/-- The explicit middle preimage operator expressed on products of Laurent modules. -/
def productLift (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂)) :
    (LaurentModule k V₁ × LaurentModule k V₂) →ₗ[LaurentSeries k]
      (LaurentModule k U₁ × LaurentModule k U₂) :=
  (LaurentModule.prodEquiv k U₁ U₂).toLinearMap.comp
    ((MiddleExactPerturbation.lift A B).comp (LaurentModule.prodEquiv k V₁ V₂).symm.toLinearMap)

theorem productLift_spec (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂))
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B))
    (z : LaurentModule k V₁ × LaurentModule k V₂) (hz : productAct B z = 0) :
    productAct A (productLift A B z) = z := by
  have hc : act B ((LaurentModule.prodEquiv k V₁ V₂).symm z) = 0 := by
    apply (LaurentModule.prodEquiv k W₁ W₂).injective
    have he := productAct_on_pair_series B ((LaurentModule.prodEquiv k V₁ V₂).symm z)
    rw [LinearEquiv.apply_symm_apply] at he
    rw [← he, hz, map_zero]
  change productAct A (LaurentModule.prodEquiv k U₁ U₂
    (MiddleExactPerturbation.lift A B ((LaurentModule.prodEquiv k V₁ V₂).symm z))) = z
  rw [productAct_on_pair_series, lift_spec A B hBA h0 _ hc, LinearEquiv.apply_symm_apply]

/-- The product preimage retains the minimum of the two independent input bounds. -/
theorem productLift_boundedBelow (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂))
    {b c : ℤ} {x : LaurentModule k V₁} {y : LaurentModule k V₂}
    (hx : LaurentModule.BoundedBelow b x) (hy : LaurentModule.BoundedBelow c y) :
    LaurentModule.BoundedBelow (min b c) (productLift A B (x, y)).1 ∧
      LaurentModule.BoundedBelow (min b c) (productLift A B (x, y)).2 :=
  (LaurentModule.boundedBelow_prodEquiv_iff _ _).mp
    (lift_boundedBelow A B (LaurentModule.boundedBelow_prodEquiv_symm hx hy))

/-- Consumer form for explicitly supplied product-block maps: only their actual
commuting-square identities with the convolution actions remain to be checked. -/
theorem laurent_middle_exact_of_block_maps
    (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂))
    (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂))
    (hBA : PowerSeriesModule.linearCompose B A = 0)
    (h0 : LinearMap.range (PowerSeriesModule.coeffV 0 A) =
      LinearMap.ker (PowerSeriesModule.coeffV 0 B))
    (F : (LaurentModule k U₁ × LaurentModule k U₂) →ₗ[LaurentSeries k]
      (LaurentModule k V₁ × LaurentModule k V₂))
    (G : (LaurentModule k V₁ × LaurentModule k V₂) →ₗ[LaurentSeries k]
      (LaurentModule k W₁ × LaurentModule k W₂))
    (hF : ∀ z, F (LaurentModule.prodEquiv k U₁ U₂ z) = LaurentModule.prodEquiv k V₁ V₂ (act A z))
    (hG : ∀ z, G (LaurentModule.prodEquiv k V₁ V₂ z) = LaurentModule.prodEquiv k W₁ W₂ (act B z)) :
    LinearMap.range F = LinearMap.ker G :=
  range_eq_ker_transport (LaurentModule.prodEquiv k U₁ U₂)
    (LaurentModule.prodEquiv k V₁ V₂) (LaurentModule.prodEquiv k W₁ W₂)
    (act A) (act B) F G hF hG (laurent_middle_exact A B hBA h0)

end

end EnvelopingIsomorphism.Deformation.MiddleExactProduct
