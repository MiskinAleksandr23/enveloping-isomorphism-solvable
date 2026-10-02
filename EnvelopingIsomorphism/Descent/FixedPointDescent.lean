import Mathlib.Algebra.Lie.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! Descent of fixed Lie isomorphisms along injective maps, and the coordinate
fixed-point calculation for a finite Galois extension. -/

namespace EnvelopingIsomorphism.Descent

universe u v w v' w' z
variable {k : Type u} [Field k]
variable {L : Type v} {M : Type w} {A : Type v'} {B : Type w'}
variable [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
variable [LieRing A] [LieAlgebra k A] [LieRing B] [LieAlgebra k B]

/-- Restriction of scalars preserves a Lie equivalence. -/
def restrictLieEquiv (R : Type z) [Field R] [Algebra R k]
    [LieAlgebra R L] [LieAlgebra R M]
    [IsScalarTower R k L] [IsScalarTower R k M]
    (f : L ≃ₗ⁅k⁆ M) : L ≃ₗ⁅R⁆ M where
  __ := f.toLinearEquiv.restrictScalars R
  map_lie' := by intro x y; exact f.map_lie x y

@[simp] theorem restrictLieEquiv_apply (R : Type z) [Field R] [Algebra R k]
    [LieAlgebra R L] [LieAlgebra R M]
    [IsScalarTower R k L] [IsScalarTower R k M]
    (f : L ≃ₗ⁅k⁆ M) (x : L) : restrictLieEquiv R f x = f x := rfl

/-- Restrict a Lie morphism to embedded base algebras when its values lie in the target range. -/
noncomputable def descendLieHom
    (jL : L →ₗ⁅k⁆ A) (jM : M →ₗ⁅k⁆ B) (hjM : Function.Injective jM)
    (f : A →ₗ⁅k⁆ B) (hf : ∀ x, ∃ y, jM y = f (jL x)) : L →ₗ⁅k⁆ M where
  toFun x := Classical.choose (hf x)
  map_add' x y := by
    apply hjM
    change jM (Classical.choose (hf (x + y))) =
      jM (Classical.choose (hf x) + Classical.choose (hf y))
    rw [Classical.choose_spec (hf (x + y))]
    simp only [map_add]
    rw [Classical.choose_spec (hf x), Classical.choose_spec (hf y)]
  map_smul' a x := by
    apply hjM
    change jM (Classical.choose (hf (a • x))) = jM (a • Classical.choose (hf x))
    rw [Classical.choose_spec (hf (a • x))]
    simp only [map_smul]
    rw [Classical.choose_spec (hf x)]
  map_lie' {x y} := by
    apply hjM
    rw [Classical.choose_spec (hf ⁅x, y⁆), jL.map_lie, f.map_lie,
      jM.map_lie, Classical.choose_spec (hf x), Classical.choose_spec (hf y)]

@[simp] theorem descendLieHom_commutes
    (jL : L →ₗ⁅k⁆ A) (jM : M →ₗ⁅k⁆ B) (hjM : Function.Injective jM)
    (f : A →ₗ⁅k⁆ B) (hf : ∀ x, ∃ y, jM y = f (jL x)) (x : L) :
    jM (descendLieHom jL jM hjM f hf x) = f (jL x) :=
  Classical.choose_spec (hf x)

/-- Descend an equivalence whose forward and inverse maps preserve the embedded base spaces. -/
noncomputable def descendLieEquiv
    (jL : L →ₗ⁅k⁆ A) (jM : M →ₗ⁅k⁆ B)
    (hjL : Function.Injective jL) (hjM : Function.Injective jM)
    (f : A ≃ₗ⁅k⁆ B)
    (hf : ∀ x, ∃ y, jM y = f (jL x))
    (hf' : ∀ y, ∃ x, jL x = f.symm (jM y)) : L ≃ₗ⁅k⁆ M where
  toLieHom := descendLieHom jL jM hjM f.toLieHom hf
  invFun := descendLieHom jM jL hjL f.symm.toLieHom hf'
  left_inv x := by
    apply hjL
    change jL (descendLieHom jM jL hjL f.symm.toLieHom hf'
      (descendLieHom jL jM hjM f.toLieHom hf x)) = jL x
    simp only [descendLieHom_commutes, LieEquiv.coe_coe, LieEquiv.symm_apply_apply]
  right_inv y := by
    apply hjM
    change jM (descendLieHom jL jM hjM f.toLieHom hf
      (descendLieHom jM jL hjL f.symm.toLieHom hf' y)) = jM y
    simp only [descendLieHom_commutes, LieEquiv.coe_coe, LieEquiv.apply_symm_apply]

@[simp] theorem descendLieEquiv_commutes
    (jL : L →ₗ⁅k⁆ A) (jM : M →ₗ⁅k⁆ B)
    (hjL : Function.Injective jL) (hjM : Function.Injective jM)
    (f : A ≃ₗ⁅k⁆ B)
    (hf : ∀ x, ∃ y, jM y = f (jL x))
    (hf' : ∀ y, ∃ x, jL x = f.symm (jM y)) (x : L) :
    jM (descendLieEquiv jL jM hjL hjM f hf hf' x) = f (jL x) :=
  Classical.choose_spec (hf x)

/-- A fixed Lie equivalence descends once fixed vectors are known to be exactly the base vectors. -/
theorem exists_descended_lieEquiv_of_fixed
    {Γ : Type z} (jL : L →ₗ⁅k⁆ A) (jM : M →ₗ⁅k⁆ B)
    (hjL : Function.Injective jL) (hjM : Function.Injective jM)
    (aL : Γ → A → A) (aM : Γ → B → B)
    (hL : ∀ x, x ∈ Set.range jL ↔ ∀ σ, aL σ x = x)
    (hM : ∀ y, y ∈ Set.range jM ↔ ∀ σ, aM σ y = y)
    (f : A ≃ₗ⁅k⁆ B) (hfixed : ∀ σ x, aM σ (f x) = f (aL σ x)) :
    ∃ g : L ≃ₗ⁅k⁆ M, ∀ x, jM (g x) = f (jL x) := by
  have hf : ∀ x, ∃ y, jM y = f (jL x) := by
    intro x
    apply (hM _).mpr
    intro σ
    rw [hfixed, (hL _).mp ⟨x, rfl⟩ σ]
  have hf' : ∀ y, ∃ x, jL x = f.symm (jM y) := by
    intro y
    apply (hL _).mpr
    intro σ
    apply f.injective
    change f (aL σ (f.symm (jM y))) = f (f.symm (jM y))
    rw [← hfixed, f.apply_symm_apply, (hM _).mp ⟨y, rfl⟩ σ]
  exact ⟨descendLieEquiv jL jM hjL hjM f hf hf',
    descendLieEquiv_commutes jL jM hjL hjM f hf hf'⟩

section Coordinates

variable (k) (K : Type v) [Field K] [Algebra k K]
variable (ι : Type w)

/-- Scalar extension of coordinate vectors, regarded as a map over the base field. -/
def coordinateExtension : (ι → k) →ₗ[k] (ι → K) where
  toFun x i := algebraMap k K (x i)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [Algebra.smul_def]

@[simp] theorem coordinateExtension_apply (x : ι → k) (i : ι) :
    coordinateExtension k K ι x i = algebraMap k K (x i) := rfl

theorem coordinateExtension_injective : Function.Injective (coordinateExtension k K ι) := by
  intro x y h
  funext i
  exact (FaithfulSMul.algebraMap_injective k K) (congrFun h i)

/-- Fixed coordinate vectors over a finite Galois extension are precisely base vectors.
The coordinate index type itself need not be finite. -/
theorem coordinateExtension_range_iff_fixed
    [FiniteDimensional k K] [IsGalois k K] (x : ι → K) :
    x ∈ Set.range (coordinateExtension k K ι) ↔
      ∀ σ : K ≃ₐ[k] K, (fun i => σ (x i)) = x := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    ext i
    exact σ.commutes (y i)
  · intro hx
    have hi : ∀ i, ∃ a : k, algebraMap k K a = x i := by
      intro i
      apply (IsGalois.mem_range_algebraMap_iff_fixed (x i)).mpr
      intro σ
      exact congrFun (hx σ) i
    refine ⟨fun i => Classical.choose (hi i), ?_⟩
    funext i
    exact Classical.choose_spec (hi i)

end Coordinates

end EnvelopingIsomorphism.Descent
