import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Algebra.Equiv

/-! Functoriality and generation for Mathlib's universal enveloping algebra.
All results use only its universal property; no PBW theorem is required. -/

namespace EnvelopingIsomorphism.Enveloping

open UniversalEnvelopingAlgebra

universe u v w z a
variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {M : Type w} [LieRing M] [LieAlgebra R M]
variable {N : Type z} [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Equality of algebra maps from the UEA can be checked on Lie generators. -/
theorem hom_ext_ι {A : Type a} [Ring A] [Algebra R A]
    {f g : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h : ∀ x : L, f (ι R x) = g (ι R x)) : f = g := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  exact h x

/-- The enveloping algebra map induced by a Lie algebra map. -/
def map (f : L →ₗ⁅R⁆ M) :
    UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R M :=
  lift R ((ι R).comp f)

@[simp] theorem map_ι (f : L →ₗ⁅R⁆ M) (x : L) :
    map f (ι R x) = ι R (f x) := by
  rw [map, lift_ι_apply]
  rfl

@[simp] theorem map_id : map (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R _ := by
  apply hom_ext_ι
  intro x
  rw [map_ι]
  rfl

@[simp] theorem map_comp (g : M →ₗ⁅R⁆ N) (f : L →ₗ⁅R⁆ M) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext_ι
  intro x
  simp only [map_ι, AlgHom.comp_apply, LieHom.comp_apply]

/-- Functorial transport of an isomorphism of Lie algebras. -/
def congr (e : L ≃ₗ⁅R⁆ M) :
    UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M :=
  AlgEquiv.ofAlgHom (map e.toLieHom) (map e.symm.toLieHom)
    (by
      apply hom_ext_ι
      intro x
      simp only [AlgHom.comp_apply, map_ι, AlgHom.id_apply, LieEquiv.coe_toLieHom,
        LieEquiv.apply_symm_apply])
    (by
      apply hom_ext_ι
      intro x
      simp only [AlgHom.comp_apply, map_ι, AlgHom.id_apply, LieEquiv.coe_toLieHom,
        LieEquiv.symm_apply_apply])

@[simp] theorem congr_ι (e : L ≃ₗ⁅R⁆ M) (x : L) :
    congr e (ι R x) = ι R (e x) := map_ι e.toLieHom x

@[simp] theorem congr_symm_ι (e : L ≃ₗ⁅R⁆ M) (x : M) :
    (congr e).symm (ι R x) = ι R (e.symm x) := map_ι e.symm.toLieHom x

/-- An induction principle using scalars, Lie generators, addition, and multiplication. -/
@[elab_as_elim] theorem induction {C : UniversalEnvelopingAlgebra R L → Prop}
    (scalar : ∀ r, C (algebraMap R (UniversalEnvelopingAlgebra R L) r))
    (generator : ∀ x : L, C (ι R x))
    (mul : ∀ x y, C x → C y → C (x * y))
    (add : ∀ x y, C x → C y → C (x + y))
    (x : UniversalEnvelopingAlgebra R L) : C x := by
  let S : Subalgebra R (UniversalEnvelopingAlgebra R L) :=
    { carrier := {x | C x}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := scalar }
  let j : L →ₗ⁅R⁆ S :=
    { toLinearMap := (ι R).toLinearMap.codRestrict S.toSubmodule generator
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact (ι R).map_lie x y }
  have h : S.val.comp (lift R j) = AlgHom.id R _ := by
    apply hom_ext_ι
    intro y
    change (lift R j (ι R y)).val = ι R y
    rw [lift_ι_apply]
    rfl
  have hx := (lift R j x).property
  change C (S.val (lift R j x)) at hx
  rw [← AlgHom.comp_apply, h, AlgHom.id_apply] at hx
  exact hx

@[simp] theorem adjoin_range_ι :
    Algebra.adjoin R (Set.range (ι R (L := L))) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using induction with
  | scalar r => exact Subalgebra.algebraMap_mem _ r
  | generator x => exact Algebra.subset_adjoin (Set.mem_range_self x)
  | mul x y hx hy => exact mul_mem hx hy
  | add x y hx hy => exact add_mem hx hy

/-- Products of Lie generators span the enveloping algebra. -/
theorem span_monoidClosure_range_ι :
    Submodule.span R (Submonoid.closure (Set.range (ι R (L := L))) :
      Set (UniversalEnvelopingAlgebra R L)) = ⊤ := by
  rw [← Algebra.adjoin_eq_span, adjoin_range_ι]
  rfl

@[simp] theorem range_lift {A : Type a} [Ring A] [Algebra R A]
    (f : L →ₗ⁅R⁆ A) :
    (lift R f).range = Algebra.adjoin R (Set.range f) := by
  rw [← Algebra.map_top, ← adjoin_range_ι (R := R) (L := L), AlgHom.map_adjoin,
    ← Set.range_comp, ι_comp_lift]

theorem map_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  rw [← AlgHom.range_eq_top, map, range_lift]
  have h : Set.range ((ι R).comp f) = Set.range (ι R (L := M)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := hf x
      exact ⟨z, rfl⟩
  rw [h, adjoin_range_ι]

end EnvelopingIsomorphism.Enveloping
