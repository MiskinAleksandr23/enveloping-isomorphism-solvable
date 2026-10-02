import EnvelopingIsomorphism.Enveloping.BaseChange
import EnvelopingIsomorphism.PBW.Basis
import EnvelopingIsomorphism.FieldTheory.CoefficientField
import Mathlib.RingTheory.Flat.Basic

/-!
# Enveloping algebras of coefficient-field models

The scalar-extension isomorphism of Lie algebras induces an injective evaluation
of the smaller enveloping algebra into the original one. PBW coefficients then
give actual preimages whenever they lie in the coefficient field.
-/

noncomputable section

namespace EnvelopingIsomorphism.FieldTheory

open UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace EnvelopingModel

variable {K k L₀ L : Type*} [Field K] [Field k] [Algebra K k]
  [LieRing L₀] [LieAlgebra K L₀] [LieRing L] [LieAlgebra k L]

/-- Scalar extension of a Lie model identifies its extended UEA with the original UEA. -/
def scalarExtensionEquiv (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) :
    k ⊗[K] UniversalEnvelopingAlgebra K L₀ ≃ₐ[k] UniversalEnvelopingAlgebra k L :=
  (Enveloping.baseChangeEquiv K k L₀).symm.trans (Enveloping.congr e)

/-- Evaluation of the smaller enveloping algebra in the original one. -/
def evaluate (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) :
    UniversalEnvelopingAlgebra K L₀ →+* UniversalEnvelopingAlgebra k L :=
  (scalarExtensionEquiv e).toRingHom.comp
    (Algebra.TensorProduct.includeRight : UniversalEnvelopingAlgebra K L₀ →ₐ[K]
      k ⊗[K] UniversalEnvelopingAlgebra K L₀).toRingHom

@[simp]
theorem evaluate_ι (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (x : L₀) :
    evaluate e (ι K x) = ι k (e (1 ⊗ₜ[K] x)) := by
  change Enveloping.congr e ((Enveloping.baseChangeEquiv K k L₀).symm (1 ⊗ₜ[K] ι K x)) = _
  rw [Enveloping.baseChangeEquiv_symm_tmul_ι, Enveloping.congr_ι]

/-- Evaluation is injective because scalar extension of modules over a field is faithful. -/
theorem evaluate_injective (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) : Function.Injective (evaluate e) :=
  (scalarExtensionEquiv e).injective.comp
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap K k)))

/-- Evaluation is semilinear with respect to the coefficient-field embedding. -/
theorem evaluate_smul (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (a : K)
    (u : UniversalEnvelopingAlgebra K L₀) :
    evaluate e (a • u) = algebraMap K k a • evaluate e u := by
  change scalarExtensionEquiv e (1 ⊗ₜ[K] (a • u)) =
    algebraMap K k a • scalarExtensionEquiv e (1 ⊗ₜ[K] u)
  rw [← TensorProduct.smul_tmul]
  rw [Algebra.smul_def, mul_one]
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]

@[simp]
theorem evaluate_algebraMap (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (a : K) :
    evaluate e (algebraMap K (UniversalEnvelopingAlgebra K L₀) a) =
      algebraMap k (UniversalEnvelopingAlgebra k L) (algebraMap K k a) := by
  simpa only [map_one, ← Algebra.algebraMap_eq_smul_one] using
    evaluate_smul e a (1 : UniversalEnvelopingAlgebra K L₀)

/-- Evaluation preserves the PBW basis when the underlying Lie bases match. -/
theorem evaluate_pbwBasis {α : Type*} [LinearOrder α]
    (b₀ : Module.Basis α K L₀) (b : Module.Basis α k L)
    (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (he : ∀ i, e (1 ⊗ₜ[K] b₀ i) = b i)
    (m : α →₀ ℕ) : evaluate e (PBW.pbwBasis b₀ m) = PBW.pbwBasis b m := by
  rw [PBW.pbwBasis_apply, PBW.pbwBasis_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (evaluate_ι e (b₀ i)).trans (congrArg (ι k) (he i))

/-- The finitely many nonzero PBW coefficients of an original enveloping element. -/
def pbwCoefficientSet {α : Type*} [LinearOrder α] (b : Module.Basis α k L)
    (u : UniversalEnvelopingAlgebra k L) : Finset k := by
  classical
  exact ((PBW.pbwBasis b).repr u).support.image ((PBW.pbwBasis b).repr u)

theorem mem_pbwCoefficientSet {α : Type*} [LinearOrder α] (b : Module.Basis α k L)
    (u : UniversalEnvelopingAlgebra k L) {m : α →₀ ℕ}
    (hm : m ∈ ((PBW.pbwBasis b).repr u).support) :
    (PBW.pbwBasis b).repr u m ∈ pbwCoefficientSet b u := by
  classical
  exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

/-- PBW coefficients in the smaller field give an actual preimage under evaluation. -/
theorem exists_preimage_of_pbw_coefficients {α : Type*} [LinearOrder α]
    (b₀ : Module.Basis α K L₀) (b : Module.Basis α k L)
    (e : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (he : ∀ i, e (1 ⊗ₜ[K] b₀ i) = b i)
    (u : UniversalEnvelopingAlgebra k L)
    (hc : ∀ a ∈ pbwCoefficientSet b u, a ∈ Set.range (algebraMap K k)) :
    ∃ u₀ : UniversalEnvelopingAlgebra K L₀, evaluate e u₀ = u := by
  classical
  have hu : u ∈ (evaluate e).range := by
    rw [← (PBW.pbwBasis b).linearCombination_repr u, Finsupp.linearCombination_apply,
      Finsupp.sum]
    apply Subring.sum_mem
    intro m hm
    obtain ⟨a, ha⟩ := hc _ (mem_pbwCoefficientSet b u hm)
    refine ⟨a • PBW.pbwBasis b₀ m, ?_⟩
    rw [evaluate_smul, evaluate_pbwBasis b₀ b e he, ha]
  exact hu

section DescendMap

variable {M₀ M : Type*} [LieRing M₀] [LieAlgebra K M₀] [LieRing M] [LieAlgebra k M]
  {α : Type*}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A linear map determined by proposed images of the model's basis generators. -/
def generatorLift (b₀ : Module.Basis α K L₀)
    (images : α → UniversalEnvelopingAlgebra K M₀) :
    L₀ →ₗ[K] UniversalEnvelopingAlgebra K M₀ :=
  b₀.constr K images

/-- Correct evaluation on the basis gives correct evaluation on every Lie generator. -/
theorem evaluate_generatorLift (b₀ : Module.Basis α K L₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i)))) (x : L₀) :
    evaluate eM (generatorLift b₀ images x) = φ (evaluate eL (ι K x)) := by
  have hx : x ∈ Submodule.span K (Set.range b₀) := by rw [b₀.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa only [generatorLift, Module.Basis.constr_basis] using himages i
  | zero => simp
  | add x y hx hy hxi hyi => simp only [map_add, hxi, hyi]
  | smul a x hx hxi => simp only [map_smul, evaluate_smul, hxi]

/-- The Lie relations of proposed generator images are reflected through injective evaluation. -/
def generatorLieHom (b₀ : Module.Basis α K L₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i)))) :
    L₀ →ₗ⁅K⁆ UniversalEnvelopingAlgebra K M₀ where
  toLinearMap := generatorLift b₀ images
  map_lie' := by
    intro x y
    apply evaluate_injective eM
    change evaluate eM (generatorLift b₀ images ⁅x, y⁆) =
      evaluate eM ⁅generatorLift b₀ images x, generatorLift b₀ images y⁆
    simp only [evaluate_generatorLift b₀ eL eM φ images himages,
      LieHom.map_lie, Ring.lie_def, map_sub, map_mul]

/-- The actual map of model UEAs built from descended generator coefficients. -/
def descendHom (b₀ : Module.Basis α K L₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i)))) :
    UniversalEnvelopingAlgebra K L₀ →ₐ[K] UniversalEnvelopingAlgebra K M₀ :=
  UniversalEnvelopingAlgebra.lift K (generatorLieHom b₀ eL eM φ images himages)

/-- The constructed smaller algebra map evaluates to the given original algebra map. -/
theorem evaluate_descendHom (b₀ : Module.Basis α K L₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i))))
    (u : UniversalEnvelopingAlgebra K L₀) :
    evaluate eM (descendHom b₀ eL eM φ images himages u) = φ (evaluate eL u) := by
  induction u using Enveloping.induction with
  | scalar a => simp only [AlgHom.commutes, evaluate_algebraMap]
  | generator x =>
    rw [descendHom, lift_ι_apply]
    exact evaluate_generatorLift b₀ eL eM φ images himages x
  | mul u v hu hv => simp only [map_mul, hu, hv]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- Descended generator formulas for an equivalence and its inverse give an actual equivalence.
The inverse laws are reflected through the injective evaluations, not assumed. -/
def descendEquiv {β : Type*} (b₀ : Module.Basis α K L₀) (c₀ : Module.Basis β K M₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (inverseImages : β → UniversalEnvelopingAlgebra K L₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i))))
    (hinverse : ∀ j, evaluate eL (inverseImages j) = φ.symm (evaluate eM (ι K (c₀ j)))) :
    UniversalEnvelopingAlgebra K L₀ ≃ₐ[K] UniversalEnvelopingAlgebra K M₀ :=
  AlgEquiv.ofAlgHom (descendHom b₀ eL eM φ.toAlgHom images himages)
    (descendHom c₀ eM eL φ.symm.toAlgHom inverseImages hinverse)
    (by
      apply Enveloping.hom_ext_ι
      intro x
      apply evaluate_injective eM
      change evaluate eM (descendHom b₀ eL eM φ.toAlgHom images himages
        (descendHom c₀ eM eL φ.symm.toAlgHom inverseImages hinverse (ι K x))) = _
      rw [evaluate_descendHom, evaluate_descendHom]
      exact φ.apply_symm_apply _)
    (by
      apply Enveloping.hom_ext_ι
      intro x
      apply evaluate_injective eL
      change evaluate eL (descendHom c₀ eM eL φ.symm.toAlgHom inverseImages hinverse
        (descendHom b₀ eL eM φ.toAlgHom images himages (ι K x))) = _
      rw [evaluate_descendHom, evaluate_descendHom]
      exact φ.symm_apply_apply _)

/-- The constructed equivalence evaluates to the original equivalence on every element. -/
theorem evaluate_descendEquiv {β : Type*} (b₀ : Module.Basis α K L₀)
    (c₀ : Module.Basis β K M₀)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (images : α → UniversalEnvelopingAlgebra K M₀)
    (inverseImages : β → UniversalEnvelopingAlgebra K L₀)
    (himages : ∀ i, evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i))))
    (hinverse : ∀ j, evaluate eL (inverseImages j) = φ.symm (evaluate eM (ι K (c₀ j))))
    (u : UniversalEnvelopingAlgebra K L₀) :
    evaluate eM (descendEquiv b₀ c₀ eL eM φ images inverseImages himages hinverse u) =
      φ (evaluate eL u) :=
  evaluate_descendHom b₀ eL eM φ.toAlgHom images himages u

/-- Finite generator coefficients of an equivalence and its inverse construct a descended equivalence. -/
theorem exists_descendedEquiv_of_coefficients {β : Type*} [LinearOrder α] [LinearOrder β]
    (b₀ : Module.Basis α K L₀) (b : Module.Basis α k L)
    (c₀ : Module.Basis β K M₀) (c : Module.Basis β k M)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (heL : ∀ i, eL (1 ⊗ₜ[K] b₀ i) = b i) (heM : ∀ j, eM (1 ⊗ₜ[K] c₀ j) = c j)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hφ : ∀ i a, a ∈ pbwCoefficientSet c (φ (ι k (b i))) → a ∈ Set.range (algebraMap K k))
    (hφinv : ∀ j a, a ∈ pbwCoefficientSet b (φ.symm (ι k (c j))) →
      a ∈ Set.range (algebraMap K k)) :
    ∃ ψ : UniversalEnvelopingAlgebra K L₀ ≃ₐ[K] UniversalEnvelopingAlgebra K M₀,
      (∀ u, evaluate eM (ψ u) = φ (evaluate eL u)) ∧
      (∀ v, evaluate eL (ψ.symm v) = φ.symm (evaluate eM v)) := by
  choose images himages using fun i =>
    exists_preimage_of_pbw_coefficients c₀ c eM heM (φ (ι k (b i))) (hφ i)
  choose inverseImages hinverse using fun j =>
    exists_preimage_of_pbw_coefficients b₀ b eL heL (φ.symm (ι k (c j))) (hφinv j)
  have himages' (i : α) : evaluate eM (images i) = φ (evaluate eL (ι K (b₀ i))) := by
    rw [evaluate_ι, heL]
    exact himages i
  have hinverse' (j : β) : evaluate eL (inverseImages j) = φ.symm (evaluate eM (ι K (c₀ j))) := by
    rw [evaluate_ι, heM]
    exact hinverse j
  let ψ := descendEquiv b₀ c₀ eL eM φ images inverseImages himages' hinverse'
  have hψ (u) : evaluate eM (ψ u) = φ (evaluate eL u) :=
    evaluate_descendEquiv b₀ c₀ eL eM φ images inverseImages himages' hinverse' u
  refine ⟨ψ, hψ, ?_⟩
  intro v
  apply φ.injective
  rw [φ.apply_symm_apply]
  simpa only [ψ.apply_symm_apply] using (hψ (ψ.symm v)).symm

/-- Extend a model equivalence and transport it through the two scalar-extension identifications. -/
def extendEquiv (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (ψ : UniversalEnvelopingAlgebra K L₀ ≃ₐ[K] UniversalEnvelopingAlgebra K M₀) :
    UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M :=
  (scalarExtensionEquiv eL).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) ψ).trans (scalarExtensionEquiv eM))

@[simp]
theorem extendEquiv_evaluate (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (ψ : UniversalEnvelopingAlgebra K L₀ ≃ₐ[K] UniversalEnvelopingAlgebra K M₀)
    (u : UniversalEnvelopingAlgebra K L₀) :
    extendEquiv eL eM ψ (evaluate eL u) = evaluate eM (ψ u) := by
  change scalarExtensionEquiv eM
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) ψ)
      ((scalarExtensionEquiv eL).symm (scalarExtensionEquiv eL (1 ⊗ₜ[K] u)))) =
    scalarExtensionEquiv eM (1 ⊗ₜ[K] ψ u)
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Evaluation compatibility proves exact equality with the scalar-extended equivalence. -/
theorem extendEquiv_eq_of_evaluate (b₀ : Module.Basis α K L₀) (b : Module.Basis α k L)
    (eL : k ⊗[K] L₀ ≃ₗ⁅k⁆ L) (eM : k ⊗[K] M₀ ≃ₗ⁅k⁆ M)
    (heL : ∀ i, eL (1 ⊗ₜ[K] b₀ i) = b i)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (ψ : UniversalEnvelopingAlgebra K L₀ ≃ₐ[K] UniversalEnvelopingAlgebra K M₀)
    (hψ : ∀ u, evaluate eM (ψ u) = φ (evaluate eL u)) :
    extendEquiv eL eM ψ = φ := by
  have hlinear : (extendEquiv eL eM ψ).toLinearMap.comp (ι k).toLinearMap =
      φ.toLinearMap.comp (ι k).toLinearMap := by
    apply b.ext
    intro i
    change extendEquiv eL eM ψ (ι k (b i)) = φ (ι k (b i))
    have hi : evaluate eL (ι K (b₀ i)) = ι k (b i) := by rw [evaluate_ι, heL]
    rw [← hi, extendEquiv_evaluate, hψ]
  have hhom : (extendEquiv eL eM ψ).toAlgHom = φ.toAlgHom :=
    Enveloping.hom_ext_ι (fun x => LinearMap.congr_fun hlinear x)
  exact AlgEquiv.ext (fun u => DFunLike.congr_fun hhom u)

end DescendMap

end EnvelopingModel

end EnvelopingIsomorphism.FieldTheory
