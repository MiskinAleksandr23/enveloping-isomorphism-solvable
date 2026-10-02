import EnvelopingIsomorphism.Deformation.MiddleExactProduct
import EnvelopingIsomorphism.Deformation.Gauge.PositiveSourceOperators
import EnvelopingIsomorphism.FormalSeries.PositiveLaurentMultilinear

/-! Block matrices of positive operator series act on the original Laurent products. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Gauge.PositiveBlockOperators
open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation MiddleExactProduct
universe u v
variable {k : Type u} [Field k]
variable {U₁ U₂ V₁ V₂ W₁ W₂ : Type v}
  [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂] [Module k U₂]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

@[simp] theorem act_zero {U V : Type v} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] :
    act (0 : OperatorSeries (k := k) U V) = 0 := by
  simp only [act, toLaurent_zero, map_zero]

@[simp] theorem act_add {U V : Type v} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (A B : OperatorSeries (k := k) U V) : act (A + B) = act A + act B := by
  change LaurentModule.linearApply (PositiveLaurent.toLaurentLinear (A+B)) = _
  rw [map_add, map_add]
  rfl

@[simp] theorem act_neg {U V : Type v} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (A : OperatorSeries (k := k) U V) : act (-A) = -act A := by
  change LaurentModule.linearApply (PositiveLaurent.toLaurentLinear (-A)) = _
  rw [map_neg, map_neg]
  rfl

/-- Packing uses genuine constant projection and inclusion convolutions. -/
def blockSeries (A : OperatorSeries (k := k) U₁ V₁) (B : OperatorSeries (k := k) U₂ V₁)
    (C : OperatorSeries (k := k) U₁ V₂) (D : OperatorSeries (k := k) U₂ V₂) :
    OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂) :=
  extractBlock (LinearMap.inl k V₁ V₂) A (LinearMap.fst k U₁ U₂) +
  extractBlock (LinearMap.inl k V₁ V₂) B (LinearMap.snd k U₁ U₂) +
  extractBlock (LinearMap.inr k V₁ V₂) C (LinearMap.fst k U₁ U₂) +
  extractBlock (LinearMap.inr k V₁ V₂) D (LinearMap.snd k U₁ U₂)

theorem coeff0_blockSeries (A : OperatorSeries (k := k) U₁ V₁) (B : OperatorSeries (k := k) U₂ V₁)
    (C : OperatorSeries (k := k) U₁ V₂) (D : OperatorSeries (k := k) U₂ V₂) :
    PowerSeriesModule.coeffV 0 (blockSeries A B C D) =
      ((PowerSeriesModule.coeffV 0 A).coprod (PowerSeriesModule.coeffV 0 B)).prod
        ((PowerSeriesModule.coeffV 0 C).coprod (PowerSeriesModule.coeffV 0 D)) := by
  apply LinearMap.ext
  intro x
  simp [blockSeries, extractBlock, coeff0_series_compose, LinearMap.comp_apply]

private theorem map_fst_symm (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    LaurentModule.map (LinearMap.fst k U₁ U₂) ((LaurentModule.prodEquiv k U₁ U₂).symm (x,y)) = x :=
  congrArg Prod.fst ((LaurentModule.prodEquiv k U₁ U₂).apply_symm_apply (x,y))

private theorem map_snd_symm (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    LaurentModule.map (LinearMap.snd k U₁ U₂) ((LaurentModule.prodEquiv k U₁ U₂).symm (x,y)) = y :=
  congrArg Prod.snd ((LaurentModule.prodEquiv k U₁ U₂).apply_symm_apply (x,y))

private theorem prodEquiv_inl (x : LaurentModule k V₁) :
    LaurentModule.prodEquiv k V₁ V₂ (LaurentModule.map (LinearMap.inl k V₁ V₂) x) = (x,0) := by
  apply Prod.ext <;> apply LaurentModule.ext <;> intro n <;> simp

private theorem prodEquiv_inr (y : LaurentModule k V₂) :
    LaurentModule.prodEquiv k V₁ V₂ (LaurentModule.map (LinearMap.inr k V₁ V₂) y) = (0,y) := by
  apply Prod.ext <;> apply LaurentModule.ext <;> intro n <;> simp

theorem productAct_blockSeries (A : OperatorSeries (k := k) U₁ V₁) (B : OperatorSeries (k := k) U₂ V₁)
    (C : OperatorSeries (k := k) U₁ V₂) (D : OperatorSeries (k := k) U₂ V₂)
    (x : LaurentModule k U₁) (y : LaurentModule k U₂) :
    productAct (blockSeries A B C D) (x,y) = (act A x + act B y, act C x + act D y) := by
  rw [productAct_apply, blockSeries]
  simp only [act_add, LinearMap.add_apply, act_extractBlock, LinearMap.comp_apply,
    map_fst_symm, map_snd_symm, map_add, prodEquiv_inl, prodEquiv_inr]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem productAct_injective : Function.Injective
    (productAct (k := k) (U₁ := U₁) (U₂ := U₂) (V₁ := V₁) (V₂ := V₂)) := by
  intro A B h
  apply PositiveSourceOperators.act_injective
  apply LinearMap.ext
  intro x
  apply (LaurentModule.prodEquiv k V₁ V₂).injective
  rw [← productAct_on_pair_series, ← productAct_on_pair_series, h]

@[simp] theorem productAct_zero :
    productAct (0 : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂)) = 0 := by
  apply LinearMap.ext
  intro x
  change LaurentModule.prodEquiv k V₁ V₂
    (act 0 ((LaurentModule.prodEquiv k U₁ U₂).symm x)) = 0
  rw [act_zero, LinearMap.zero_apply, map_zero]

theorem productAct_comp (B : OperatorSeries (k := k) (V₁ × V₂) (W₁ × W₂))
    (A : OperatorSeries (k := k) (U₁ × U₂) (V₁ × V₂)) :
    productAct (PowerSeriesModule.linearCompose B A) = (productAct B).comp (productAct A) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (LaurentModule.prodEquiv k U₁ U₂).surjective x
  rw [productAct_on_pair_series]
  change _ = productAct B (productAct A (LaurentModule.prodEquiv k U₁ U₂ x))
  rw [productAct_on_pair_series, productAct_on_pair_series, ← act_comp]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.PositiveBlockOperators
