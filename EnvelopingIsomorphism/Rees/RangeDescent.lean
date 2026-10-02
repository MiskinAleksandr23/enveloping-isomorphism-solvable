import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Restrict an actual ambient algebra equivalence through injective algebra maps.
All range conditions are explicit and must be proved by the Rees construction. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees

variable {R A B C D : Type*} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- Pull an algebra map back through an injective algebra map whose range contains its image. -/
def liftThroughRange (f : B →ₐ[R] D) (hf : Function.Injective f)
    (g : A →ₐ[R] D) (hg : ∀ x, g x ∈ f.range) : A →ₐ[R] B :=
  (AlgEquiv.ofInjective f hf).symm.toAlgHom.comp (g.codRestrict f.range hg)

@[simp] theorem apply_liftThroughRange (f : B →ₐ[R] D) (hf : Function.Injective f)
    (g : A →ₐ[R] D) (hg : ∀ x, g x ∈ f.range) (x : A) :
    f (liftThroughRange f hf g hg x) = g x := by
  change ((AlgEquiv.ofInjective f hf)
    ((AlgEquiv.ofInjective f hf).symm ⟨g x, hg x⟩)).val = g x
  rw [AlgEquiv.apply_symm_apply]

/-- An ambient equivalence preserving the two ranges restricts to an actual equivalence. -/
def descendAlongEmbeddings (fA : A →ₐ[R] C) (fB : B →ₐ[R] D)
    (hfA : Function.Injective fA) (hfB : Function.Injective fB) (e : C ≃ₐ[R] D)
    (he : ∀ x, e (fA x) ∈ fB.range)
    (he' : ∀ y, e.symm (fB y) ∈ fA.range) : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom
    (liftThroughRange fB hfB (e.toAlgHom.comp fA) he)
    (liftThroughRange fA hfA (e.symm.toAlgHom.comp fB) he')
    (by
      ext y
      apply hfB
      simp only [AlgHom.comp_apply, apply_liftThroughRange, AlgEquiv.coe_toAlgHom,
        AlgEquiv.apply_symm_apply, AlgHom.id_apply])
    (by
      ext x
      apply hfA
      simp only [AlgHom.comp_apply, apply_liftThroughRange, AlgEquiv.coe_toAlgHom,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply])

/-- The descended equivalence is characterized by its exact commuting diagram. -/
theorem descendAlongEmbeddings_commutes (fA : A →ₐ[R] C) (fB : B →ₐ[R] D)
    (hfA : Function.Injective fA) (hfB : Function.Injective fB) (e : C ≃ₐ[R] D)
    (he : ∀ x, e (fA x) ∈ fB.range)
    (he' : ∀ y, e.symm (fB y) ∈ fA.range) (x : A) :
    fB (descendAlongEmbeddings fA fB hfA hfB e he he' x) = e (fA x) :=
  apply_liftThroughRange fB hfB (e.toAlgHom.comp fA) he x

end EnvelopingIsomorphism.Rees
