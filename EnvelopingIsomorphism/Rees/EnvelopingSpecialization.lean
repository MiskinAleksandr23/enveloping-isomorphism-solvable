import EnvelopingIsomorphism.Rees.Family
import EnvelopingIsomorphism.Enveloping.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual specialization of Rees enveloping-algebra isomorphisms

Polynomial evaluation is implemented as scalar extension, using the proved
base-change equivalence for universal enveloping algebras. Every statement
uses the native Lie structures on `Family.Fiber`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Rees.EnvelopingSpecialization

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

variable {k ι L M : Type*} [Field k] [Fintype ι]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  {bL : Basis ι k L} {bM : Basis ι k M}

variable (a : k)

/-- Polynomial coefficients act on the enveloping algebra of the fiber by evaluation. -/
scoped instance fiberAlgebra (d : WeightData bL) :
    Algebra (Polynomial k) (UniversalEnvelopingAlgebra k (Family.Fiber d a)) := by
  letI := Family.evaluationAlgebra a
  exact Algebra.restrictScalars (Polynomial k) k _

@[simp] theorem fiber_algebraMap (d : WeightData bL) (p : Polynomial k) :
    algebraMap (Polynomial k) (UniversalEnvelopingAlgebra k (Family.Fiber d a)) p =
      algebraMap k _ (Polynomial.eval a p) := rfl

@[simp] theorem algebraMap_X (d : WeightData bL) :
    algebraMap (Polynomial k) (UniversalEnvelopingAlgebra k (Family.Fiber d a)) Polynomial.X =
      algebraMap k _ a := by
  rw [fiber_algebraMap, Polynomial.eval_X]

/-- The actual evaluation map into the enveloping algebra of the native fiber. -/
def evalMap (d : WeightData bL) :
    UniversalEnvelopingAlgebra (Polynomial k) (Family d) →ₐ[Polynomial k]
      UniversalEnvelopingAlgebra k (Family.Fiber d a) :=
  by
    letI := Family.evaluationAlgebra a
    exact UniversalEnvelopingAlgebra.lift (Polynomial k)
      (EnvelopingIsomorphism.Enveloping.scalarExtensionι (Polynomial k) k (Family d))

@[simp] theorem evalMap_ι_basis (d : WeightData bL) (i : ι) :
    evalMap a d (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis d i)) =
      UniversalEnvelopingAlgebra.ι k (Family.fiberBasis d a i) := by
  letI := Family.evaluationAlgebra a
  rw [evalMap, lift_ι_apply]
  change UniversalEnvelopingAlgebra.ι k ((1 : k) ⊗ₜ[Polynomial k] Family.basis d i) =
    UniversalEnvelopingAlgebra.ι k ((Family.basis d).baseChange k i)
  rw [Basis.baseChange_apply]

@[simp] theorem evalMap_algebraMap_X (d : WeightData bL) :
    evalMap a d (algebraMap (Polynomial k)
      (UniversalEnvelopingAlgebra (Polynomial k) (Family d)) Polynomial.X) = algebraMap k _ a := by
  rw [AlgHom.commutes, algebraMap_X]

theorem evalMap_eq_baseChange (d : WeightData bL)
    (x : UniversalEnvelopingAlgebra (Polynomial k) (Family d)) :
    letI := Family.evaluationAlgebra a
    evalMap a d x =
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) k (Family d)).symm
        (1 ⊗ₜ[Polynomial k] x) := by
  letI := Family.evaluationAlgebra a
  change evalMap a d x = EnvelopingIsomorphism.Enveloping.baseChangeBackward (Polynomial k) k
    (Family d) (1 ⊗ₜ[Polynomial k] x)
  rw [EnvelopingIsomorphism.Enveloping.baseChangeBackward_tmul, one_smul]
  rfl

/-- Specialize an actual polynomial enveloping equivalence at the chosen scalar. -/
def specialize (dL : WeightData bL) (dM : WeightData bM)
    (Ψ : UniversalEnvelopingAlgebra (Polynomial k) (Family dL) ≃ₐ[Polynomial k]
      UniversalEnvelopingAlgebra (Polynomial k) (Family dM)) :
    UniversalEnvelopingAlgebra k (Family.Fiber dL a) ≃ₐ[k]
      UniversalEnvelopingAlgebra k (Family.Fiber dM a) :=
  by
    letI := Family.evaluationAlgebra a
    exact (EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) k (Family dL)).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) Ψ).trans
        (EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) k (Family dM)).symm)

/-- Specialization commutes with evaluation on every element, not just generators. -/
theorem specialize_evalMap (dL : WeightData bL) (dM : WeightData bM)
    (Ψ : UniversalEnvelopingAlgebra (Polynomial k) (Family dL) ≃ₐ[Polynomial k]
      UniversalEnvelopingAlgebra (Polynomial k) (Family dM))
    (x : UniversalEnvelopingAlgebra (Polynomial k) (Family dL)) :
    specialize a dL dM Ψ (evalMap a dL x) = evalMap a dM (Ψ x) := by
  letI := Family.evaluationAlgebra a
  rw [evalMap_eq_baseChange, evalMap_eq_baseChange]
  let eL := EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) k (Family dL)
  let eM := EnvelopingIsomorphism.Enveloping.baseChangeEquiv (Polynomial k) k (Family dM)
  change eM.symm (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) Ψ
    (eL (eL.symm (1 ⊗ₜ[Polynomial k] x)))) = eM.symm (1 ⊗ₜ[Polynomial k] Ψ x)
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The specialized equivalence acts on the actual fiber basis generators by evaluating `Ψ`. -/
theorem specialize_ι_basis (dL : WeightData bL) (dM : WeightData bM)
    (Ψ : UniversalEnvelopingAlgebra (Polynomial k) (Family dL) ≃ₐ[Polynomial k]
      UniversalEnvelopingAlgebra (Polynomial k) (Family dM)) (i : ι) :
    specialize a dL dM Ψ (UniversalEnvelopingAlgebra.ι k (Family.fiberBasis dL a i)) =
      evalMap a dM (Ψ (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i))) := by
  rw [← evalMap_ι_basis, specialize_evalMap]

/-- The coefficient hypothesis needed to apply zero-parameter marking. -/
@[simp] theorem zero_algebraMap_X (d : WeightData bL) :
    algebraMap (Polynomial k) (UniversalEnvelopingAlgebra k (Family.Fiber d 0)) Polynomial.X = 0 := by
  rw [algebraMap_X, map_zero]

end EnvelopingIsomorphism.Rees.EnvelopingSpecialization
