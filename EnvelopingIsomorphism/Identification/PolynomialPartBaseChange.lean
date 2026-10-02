import EnvelopingIsomorphism.Identification.MetabelianBasic
import EnvelopingIsomorphism.Identification.LocalScalarExtension
import EnvelopingIsomorphism.Enveloping.BaseChange

/-!
The intrinsic polynomial and linear-polynomial parts commute with scalar
extension under the actual universal-enveloping base-change equivalence.
Membership is reflected by faithful scalar extension.  PBW coordinates are
not needed for these statements.
-/

namespace EnvelopingIsomorphism.Identification

open scoped TensorProduct

universe u v w z
variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]

section Submodules

variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Faithful extension reflects membership in an arbitrary subspace. -/
theorem one_tmul_mem_baseChange_iff (P : Submodule k V) (x : V) :
    (1 : K) ⊗ₜ[k] x ∈ P.baseChange K ↔ x ∈ P := by
  simpa only [Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply,
    Submodule.span_singleton_le_iff_mem] using
    (Submodule.baseChange_le_iff (A := K) (p := Submodule.span k {x}) (q := P))

/-- Extending scalars preserves the sum of two subspaces. -/
theorem submodule_baseChange_sup (P Q : Submodule k V) :
    (P ⊔ Q).baseChange K = P.baseChange K ⊔ Q.baseChange K := by
  have hspan : P ⊔ Q = Submodule.span k ((P : Set V) ∪ Q) := by
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq]
  rw [hspan, Submodule.baseChange_span, Set.image_union, Submodule.span_union]
  congr 1 <;> rw [← Submodule.baseChange_span, Submodule.span_eq]

/-- Taking the image of a linear map commutes with scalar extension. -/
theorem range_baseChange_eq {W : Type z} [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) : (f.baseChange K).range = f.range.baseChange K := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        rw [LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a ⟨x, rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨v, rfl⟩, rfl⟩
    exact ⟨(1 : K) ⊗ₜ[k] v, rfl⟩

end Submodules

section Subalgebras

variable {A : Type w} [Ring A] [Algebra k A]

/-- Algebraic and linear scalar extension have the same underlying subspace. -/
theorem subalgebra_baseChange_toSubmodule (C : Subalgebra k A) :
    (C.baseChange K).toSubmodule = C.toSubmodule.baseChange K := rfl

/-- Adjoining a set of algebra generators commutes with scalar extension. -/
theorem adjoin_baseChange (s : Set A) :
    (Algebra.adjoin k s).baseChange K =
      Algebra.adjoin K (((1 : K) ⊗ₜ[k] ·) '' s) := by
  apply Subalgebra.toSubmodule_injective
  rw [subalgebra_baseChange_toSubmodule, Algebra.adjoin_eq_span,
    Submodule.baseChange_span, Algebra.adjoin_eq_span]
  congr 1
  exact congrArg (fun S : Submonoid (K ⊗[k] A) => (S : Set (K ⊗[k] A)))
    (MonoidHom.map_mclosure
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) s)

end Subalgebras

section Lie

variable {L : Type w} [LieRing L] [LieAlgebra k L]
attribute [local instance 100] LieRing.ofAssociativeRing
open UniversalEnvelopingAlgebra

/-- The actual base-change equivalence takes the polynomial part of the extended
ideal to the scalar extension of the original polynomial part. -/
theorem idealPolynomialPart_map_baseChange (H : LieIdeal k L) :
    (idealPolynomialPart (H.baseChange K)).map (Enveloping.baseChangeEquiv k K L).toAlgHom =
      (idealPolynomialPart H).baseChange K := by
  apply le_antisymm
  · rw [Subalgebra.map_le]
    apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    rcases x with ⟨x, hx⟩
    change Enveloping.baseChangeEquiv k K L (ι K (x : K ⊗[k] L)) ∈
      (idealPolynomialPart H).baseChange K
    rw [LieSubmodule.mem_baseChange_iff] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨h, hh, rfl⟩ := hy
        rw [TensorProduct.mk_apply, Enveloping.baseChangeEquiv_ι_tmul]
        exact Subalgebra.tmul_mem_baseChange (ι_mem_idealPolynomialPart H hh) 1
    | zero => simp
    | add y z _ _ hy hz => simpa only [map_add] using add_mem hy hz
    | smul a y _ hy => simpa only [map_smul] using Subalgebra.smul_mem _ hy a
  · rw [idealPolynomialPart, adjoin_baseChange]
    apply Algebra.adjoin_le
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨ι K ((1 : K) ⊗ₜ[k] (h : L)), ?_, ?_⟩
    · exact ι_mem_idealPolynomialPart _ (LieSubmodule.tmul_mem_baseChange_of_mem 1 h.property)
    · exact Enveloping.baseChangeEquiv_ι_tmul k K L 1 h

/-- The submodule form of polynomial-part compatibility. -/
theorem idealPolynomialPart_submodule_map_baseChange (H : LieIdeal k L) :
    (idealPolynomialPart (H.baseChange K)).toSubmodule.map
        (Enveloping.baseChangeEquiv k K L).toLinearMap =
      (idealPolynomialPart H).toSubmodule.baseChange K := by
  change (idealPolynomialPart (H.baseChange K)).toSubmodule.map
    (Enveloping.baseChangeEquiv k K L).toAlgHom.toLinearMap = _
  rw [← Subalgebra.map_toSubmodule, idealPolynomialPart_map_baseChange,
    subalgebra_baseChange_toSubmodule]

/-- Linear generators commute with the actual enveloping base-change equivalence. -/
theorem generator_range_map_baseChange :
    (ι K (L := K ⊗[k] L)).toLinearMap.range.map
        (Enveloping.baseChangeEquiv k K L).toLinearMap =
      (ι k (L := L)).toLinearMap.range.baseChange K := by
  rw [← LinearMap.range_comp]
  have h : (Enveloping.baseChangeEquiv k K L).toLinearMap.comp
      (ι K (L := K ⊗[k] L)).toLinearMap = (ι k (L := L)).toLinearMap.baseChange K := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    exact Enveloping.baseChangeEquiv_ι_tmul k K L a x
  rw [h, range_baseChange_eq]

/-- The concrete LF target submodule commutes with scalar extension. -/
theorem linearPolynomialPart_map_baseChange (H : LieIdeal k L) :
    (linearPolynomialPart (H.baseChange K)).map
        (Enveloping.baseChangeEquiv k K L).toLinearMap =
      (linearPolynomialPart H).baseChange K := by
  unfold linearPolynomialPart
  rw [Submodule.map_sup, submodule_baseChange_sup, generator_range_map_baseChange,
    idealPolynomialPart_submodule_map_baseChange]

/-- Polynomial-part membership is preserved and reflected under actual scalar extension. -/
theorem mem_idealPolynomialPart_baseChange_iff (H : LieIdeal k L)
    (a : UniversalEnvelopingAlgebra k L) :
    (Enveloping.baseChangeEquiv k K L).symm ((1 : K) ⊗ₜ[k] a) ∈
        idealPolynomialPart (H.baseChange K) ↔ a ∈ idealPolynomialPart H := by
  change (Enveloping.baseChangeEquiv k K L).toLinearEquiv.symm
      ((1 : K) ⊗ₜ[k] a) ∈ (idealPolynomialPart (H.baseChange K)).toSubmodule ↔ _
  rw [← Submodule.mem_map_equiv, idealPolynomialPart_submodule_map_baseChange]
  exact one_tmul_mem_baseChange_iff _ a

/-- The linear-plus-polynomial LF target is preserved and reflected under scalar extension. -/
theorem mem_linearPolynomialPart_baseChange_iff (H : LieIdeal k L)
    (a : UniversalEnvelopingAlgebra k L) :
    (Enveloping.baseChangeEquiv k K L).symm ((1 : K) ⊗ₜ[k] a) ∈
        linearPolynomialPart (H.baseChange K) ↔ a ∈ linearPolynomialPart H := by
  change (Enveloping.baseChangeEquiv k K L).toLinearEquiv.symm
      ((1 : K) ⊗ₜ[k] a) ∈ linearPolynomialPart (H.baseChange K) ↔ _
  rw [← Submodule.mem_map_equiv, linearPolynomialPart_map_baseChange]
  exact one_tmul_mem_baseChange_iff _ a

end Lie

end EnvelopingIsomorphism.Identification
