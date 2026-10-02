import EnvelopingIsomorphism.Descent.SemilinearLieAction
import EnvelopingIsomorphism.Descent.FixedPointDescent
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
The native semilinear Galois action on a scalar-extended Lie algebra, its
coordinates in a scalar-extended basis, and descent of its fixed vectors.
-/

noncomputable section

namespace EnvelopingIsomorphism.Descent.GaloisLieAction

open scoped TensorProduct

universe u v w z
variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
variable (L : Type w) [LieRing L] [LieAlgebra k L]

local instance (κ : K ≃+* K) : RingHomInvPair κ.toRingHom κ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv κ

/-- The tensor action of a field automorphism, semilinear over the extended field. -/
def tensorEquiv (σ : K ≃ₐ[k] K) :
    (K ⊗[k] L) ≃ₛₗ[σ.toRingEquiv.toRingHom] (K ⊗[k] L) where
  __ := (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl k L)).toAddEquiv
  map_smul' a x := by
    change (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl k L)) (a • x) =
      σ a • (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl k L)) x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
        simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.congr_tmul,
          AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp] theorem tensorEquiv_tmul (σ : K ≃ₐ[k] K) (a : K) (x : L) :
    tensorEquiv k K L σ (a ⊗ₜ[k] x) = σ a ⊗ₜ[k] x := rfl

/-- The native tensor action preserves the extended Lie bracket. -/
theorem tensorEquiv_map_lie (σ : K ≃ₐ[k] K) (x y : K ⊗[k] L) :
    tensorEquiv k K L σ ⁅x, y⁆ =
      ⁅tensorEquiv k K L σ x, tensorEquiv k K L σ y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul, tensorEquiv_tmul, map_mul]
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_lie, map_add, hx, hz]

/-- The actual action needed by the filtered-cocycle descent theorem. -/
def action : SemilinearLieAction (K ≃ₐ[k] K) K (K ⊗[k] L) where
  scalar σ := σ.toRingEquiv
  equiv := tensorEquiv k K L
  map_lie := tensorEquiv_map_lie k K L
  one_apply x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  mul_apply σ τ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem action_equiv_tmul (σ : K ≃ₐ[k] K) (a : K) (x : L) :
    (action k K L).equiv σ (a ⊗ₜ[k] x) = σ a ⊗ₜ[k] x := rfl

/-- The native Lie embedding of the original algebra in its scalar extension. -/
def embedding : L →ₗ⁅k⁆ (K ⊗[k] L) where
  toLinearMap := TensorProduct.mk k K L 1
  map_lie' := by
    intro x y
    change (1 : K) ⊗ₜ[k] ⁅x, y⁆ = ⁅(1 : K) ⊗ₜ[k] x, (1 : K) ⊗ₜ[k] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

@[simp] theorem embedding_apply (x : L) : embedding k K L x = (1 : K) ⊗ₜ[k] x := rfl

/-- The original Lie algebra embeds faithfully after field extension. -/
theorem embedding_injective : Function.Injective (embedding k K L) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff k L (A := K) (x - y)).mp
  simpa only [TensorProduct.tmul_sub, sub_eq_zero, embedding_apply] using hxy

@[simp] theorem embedding_fixed (σ : K ≃ₐ[k] K) (x : L) :
    (action k K L).equiv σ (embedding k K L x) = embedding k K L x := by
  change σ 1 ⊗ₜ[k] x = (1 : K) ⊗ₜ[k] x
  rw [map_one]

variable {k K L}

/-- Galois acts on every extended-basis coordinate by its field automorphism. -/
theorem basis_repr_action {ι : Type z} (b : Module.Basis ι k L)
    (σ : K ≃ₐ[k] K) (x : K ⊗[k] L) (i : ι) :
    (b.baseChange K).repr ((action k K L).equiv σ x) i =
      σ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      simp only [action_equiv_tmul, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, map_mul, AlgEquiv.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

@[simp] theorem basis_fixed {ι : Type z} (b : Module.Basis ι k L)
    (σ : K ≃ₐ[k] K) (i : ι) :
    (action k K L).equiv σ (b.baseChange K i) = b.baseChange K i := by
  rw [Module.Basis.baseChange_apply]
  change σ 1 ⊗ₜ[k] b i = (1 : K) ⊗ₜ[k] b i
  rw [map_one]

/-- Coordinates of the embedding are the images of the original coordinates. -/
@[simp] theorem basis_repr_embedding {ι : Type z} (b : Module.Basis ι k L)
    (x : L) (i : ι) :
    (b.baseChange K).repr (embedding k K L x) i = algebraMap k K (b.repr x i) := by
  simp [Algebra.smul_def]

/-- Fixed vectors in a scalar-extended finite basis are exactly the original
vectors.  The field extension is finite Galois. -/
theorem embedding_range_iff_fixed [FiniteDimensional k K] [IsGalois k K]
    {ι : Type z} [Fintype ι] (b : Module.Basis ι k L) (x : K ⊗[k] L) :
    x ∈ Set.range (embedding k K L) ↔
      ∀ σ : K ≃ₐ[k] K, (action k K L).equiv σ x = x := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact embedding_fixed k K L σ y
  · intro hx
    have hcoord : (b.baseChange K).equivFun x ∈
        Set.range (coordinateExtension k K ι) := by
      apply (coordinateExtension_range_iff_fixed k K ι _).mpr
      intro σ
      funext i
      have h := basis_repr_action b σ x i
      rw [hx σ] at h
      exact h.symm
    obtain ⟨c, hc⟩ := hcoord
    refine ⟨b.equivFun.symm c, ?_⟩
    apply (b.baseChange K).equivFun.injective
    funext i
    change (b.baseChange K).repr (embedding k K L (b.equivFun.symm c)) i = _
    rw [basis_repr_embedding]
    change algebraMap k K ((b.equivFun (b.equivFun.symm c)) i) =
      (b.baseChange K).equivFun x i
    rw [b.equivFun.apply_symm_apply]
    exact congrFun hc i

/-- Basis-free fixed-vector descent for a finite-dimensional Lie algebra. -/
theorem embedding_range_iff_fixed_of_finiteDimensional
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    (x : K ⊗[k] L) :
    x ∈ Set.range (embedding k K L) ↔
      ∀ σ : K ≃ₐ[k] K, (action k K L).equiv σ x = x :=
  embedding_range_iff_fixed (Module.finBasis k L) x

/-- Canonical restriction to rational scalars, for the exp/log APIs. -/
abbrev rationalLieAlgebra (R : Type*) [Field R] [CharZero R]
    (V : Type*) [LieRing V] [LieAlgebra R V] : LieAlgebra ℚ V where
  toModule := Module.compHom V (algebraMap ℚ R)
  lie_smul q x y := by
    change ⁅x, algebraMap ℚ R q • y⁆ = algebraMap ℚ R q • ⁅x, y⁆
    exact lie_smul _ _ _

end EnvelopingIsomorphism.Descent.GaloisLieAction
