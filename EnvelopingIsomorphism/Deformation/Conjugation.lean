import EnvelopingIsomorphism.Deformation.LowArity

/-!
The genuine action of linear coordinate changes on arbitrary bilinear products.
No associativity is built into the type of a product.  The action and its
intertwining criterion are therefore available before imposing Maurer-Cartan.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Transport a bilinear product by an invertible linear map. -/
def conjugate (g : A ≃ₗ[R] A) (μ : Binary R A) : Binary R A :=
  ((μ.comp g.symm.toLinearMap).compl₂ g.symm.toLinearMap).compr₂ g.toLinearMap

@[simp] theorem conjugate_apply (g : A ≃ₗ[R] A) (μ : Binary R A) (a b : A) :
    conjugate g μ a b = g (μ (g.symm a) (g.symm b)) := rfl

@[simp] theorem conjugate_refl (μ : Binary R A) :
    conjugate (LinearEquiv.refl R A) μ = μ := by ext a b; rfl

theorem conjugate_trans (g h : A ≃ₗ[R] A) (μ : Binary R A) :
    conjugate h (conjugate g μ) = conjugate (g.trans h) μ := by ext a b; rfl

@[simp] theorem conjugate_symm (g : A ≃ₗ[R] A) (μ : Binary R A) :
    conjugate g.symm (conjugate g μ) = μ := by
  ext a b
  simp

@[simp] theorem conjugate_add (g : A ≃ₗ[R] A) (μ ν : Binary R A) :
    conjugate g (μ + ν) = conjugate g μ + conjugate g ν := by ext a b; simp

@[simp] theorem conjugate_smul (g : A ≃ₗ[R] A) (r : R) (μ : Binary R A) :
    conjugate g (r • μ) = r • conjugate g μ := by ext a b; simp

/-- Equality under transport is equivalent to the algebraic intertwining equation. -/
theorem conjugate_eq_iff (g : A ≃ₗ[R] A) (μ ν : Binary R A) :
    conjugate g μ = ν ↔ ∀ a b, g (μ a b) = ν (g a) (g b) := by
  constructor
  · intro h a b
    have := LinearMap.congr_fun (LinearMap.congr_fun h (g a)) (g b)
    simpa using this
  · intro h
    ext a b
    simpa using h (g.symm a) (g.symm b)

/-- A coordinate change preserves associativity. -/
theorem conjugate_associative (g : A ≃ₗ[R] A) (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    ∀ a b c, conjugate g μ (conjugate g μ a b) c =
      conjugate g μ a (conjugate g μ b c) := by
  intro a b c
  simp only [conjugate_apply, LinearEquiv.symm_apply_apply]
  rw [hμ]

/-- Associativity is invariant, with no restriction on the linear coordinate change. -/
theorem conjugate_associative_iff (g : A ≃ₗ[R] A) (μ : Binary R A) :
    (∀ a b c, conjugate g μ (conjugate g μ a b) c =
      conjugate g μ a (conjugate g μ b c)) ↔
        ∀ a b c, μ (μ a b) c = μ a (μ b c) := by
  constructor
  · intro h
    simpa only [conjugate_symm] using conjugate_associative g.symm (conjugate g μ) h
  · exact conjugate_associative g μ

end EnvelopingIsomorphism.Deformation
