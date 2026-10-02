import EnvelopingIsomorphism.Enveloping.UniversalProperties
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic

/-! Scalar extension of universal enveloping algebras, proved by universal properties. -/

namespace EnvelopingIsomorphism.Enveloping

open UniversalEnvelopingAlgebra
open scoped TensorProduct

universe u v w z
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (L : Type w) [LieRing L] [LieAlgebra R L]

attribute [local instance 2000] LieRing.ofAssociativeRing

section LieLift

variable {R L} {A : Type z} [LieRing A] [LieAlgebra R A] [LieAlgebra S A]
    [IsScalarTower R S A]

/-- Extension of a Lie homomorphism into an algebra over the extended scalar ring. -/
def lieLiftBaseChange (f : L →ₗ⁅R⁆ A) : S ⊗[R] L →ₗ⁅S⁆ A where
  toLinearMap := f.toLinearMap.liftBaseChange S
  map_lie' {x y} := by
    change f.toLinearMap.liftBaseChange S ⁅x, y⁆ =
      ⁅f.toLinearMap.liftBaseChange S x, f.toLinearMap.liftBaseChange S y⁆
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.liftBaseChange_tmul,
          LieHom.coe_toLinearMap, LieHom.map_lie, smul_lie, lie_smul, smul_smul]
        rw [mul_comm]
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_lie, map_add, hx, hz]

@[simp] theorem lieLiftBaseChange_tmul (f : L →ₗ⁅R⁆ A) (s : S) (x : L) :
    lieLiftBaseChange S f (s ⊗ₜ[R] x) = s • f x := rfl

end LieLift

local instance : Algebra R (UniversalEnvelopingAlgebra S (S ⊗[R] L)) :=
  Algebra.restrictScalars R S _

local instance : IsScalarTower R S (UniversalEnvelopingAlgebra S (S ⊗[R] L)) :=
  IsScalarTower.of_compHom R S _

/-- Original Lie generators inside the enveloping algebra after scalar extension. -/
def scalarExtensionι : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra S (S ⊗[R] L) where
  toLinearMap := ((ι S).toLinearMap.restrictScalars R).comp (TensorProduct.mk R S L 1)
  map_lie' {x y} := by
    change ι S (1 ⊗ₜ[R] ⁅x, y⁆) = ⁅ι S (1 ⊗ₜ[R] x), ι S (1 ⊗ₜ[R] y)⁆
    rw [← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

@[simp] theorem scalarExtensionι_apply (x : L) :
    scalarExtensionι R S L x = ι S (1 ⊗ₜ[R] x) := rfl

/-- The canonical map from the enveloping algebra of the extended Lie algebra. -/
def baseChangeForward : UniversalEnvelopingAlgebra S (S ⊗[R] L) →ₐ[S]
    S ⊗[R] UniversalEnvelopingAlgebra R L :=
  lift S (lieLiftBaseChange S
    ((Algebra.TensorProduct.includeRight : UniversalEnvelopingAlgebra R L →ₐ[R]
      S ⊗[R] UniversalEnvelopingAlgebra R L).toLieHom.comp (ι R)))

@[simp] theorem baseChangeForward_ι_tmul (s : S) (x : L) :
    baseChangeForward R S L (ι S (s ⊗ₜ[R] x)) = s ⊗ₜ[R] ι R x := by
  rw [baseChangeForward, lift_ι_apply, lieLiftBaseChange_tmul]
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The canonical map in the reverse direction. -/
def baseChangeBackward : S ⊗[R] UniversalEnvelopingAlgebra R L →ₐ[S]
    UniversalEnvelopingAlgebra S (S ⊗[R] L) :=
  AlgHom.liftEquiv R S _ _ (lift R (scalarExtensionι R S L))

@[simp] theorem baseChangeBackward_tmul (s : S) (a : UniversalEnvelopingAlgebra R L) :
    baseChangeBackward R S L (s ⊗ₜ[R] a) =
      s • lift R (scalarExtensionι R S L) a := rfl

@[simp] theorem baseChangeBackward_tmul_ι (s : S) (x : L) :
    baseChangeBackward R S L (s ⊗ₜ[R] ι R x) = ι S (s ⊗ₜ[R] x) := by
  rw [baseChangeBackward_tmul, lift_ι_apply, scalarExtensionι_apply,
    ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem baseChangeForward_comp_backward :
    (baseChangeForward R S L).comp (baseChangeBackward R S L) = AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext_ι
  intro x
  change baseChangeForward R S L (baseChangeBackward R S L (1 ⊗ₜ[R] ι R x)) =
    1 ⊗ₜ[R] ι R x
  rw [baseChangeBackward_tmul_ι, baseChangeForward_ι_tmul]

theorem baseChangeBackward_comp_forward :
    (baseChangeBackward R S L).comp (baseChangeForward R S L) = AlgHom.id S _ := by
  apply hom_ext_ι
  intro x
  change baseChangeBackward R S L (baseChangeForward R S L (ι S x)) = ι S x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rw [baseChangeForward_ι_tmul, baseChangeBackward_tmul_ι]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Universal enveloping algebras commute with arbitrary scalar extension.
This does not need flatness, finite dimensionality, or PBW. -/
def baseChangeEquiv : UniversalEnvelopingAlgebra S (S ⊗[R] L) ≃ₐ[S]
    S ⊗[R] UniversalEnvelopingAlgebra R L :=
  AlgEquiv.ofAlgHom (baseChangeForward R S L) (baseChangeBackward R S L)
    (baseChangeForward_comp_backward R S L) (baseChangeBackward_comp_forward R S L)

@[simp] theorem baseChangeEquiv_ι_tmul (s : S) (x : L) :
    baseChangeEquiv R S L (ι S (s ⊗ₜ[R] x)) = s ⊗ₜ[R] ι R x :=
  baseChangeForward_ι_tmul R S L s x

@[simp] theorem baseChangeEquiv_symm_tmul_ι (s : S) (x : L) :
    (baseChangeEquiv R S L).symm (s ⊗ₜ[R] ι R x) = ι S (s ⊗ₜ[R] x) :=
  baseChangeBackward_tmul_ι R S L s x

end EnvelopingIsomorphism.Enveloping
