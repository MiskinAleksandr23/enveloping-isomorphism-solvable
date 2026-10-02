import EnvelopingIsomorphism.Deformation.TwoVertexSchoutenContraction
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSubstitution

/-! Exact raw tensor identities for the local graphs which replace an internal
Schouten vertex. The coefficients are retained before geometric normalization. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.SchoutenGraphContraction

open MvPolynomial
open scoped BigOperators
open KontsevichGraph.General
open KontsevichGraph.General.TwoVertexContraction

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
theorem rawTensor_three (F : Multiderivation K (PolynomialFunctions K d) 3)
    (i : Fin 3 → Fin d) :
    rawTensor F i = trivectorComponent F (i 0) (i 1) (i 2) := by
  rw [trivectorComponent_apply]
  apply congrArg F
  funext j
  fin_cases j <;> rfl

/-- The entire raw trivector tensor is the six-term sum of actual local templates. -/
theorem rawTensor_bivector_bracket
    (F G : Multiderivation K (PolynomialFunctions K d) 2) :
    rawTensor (show Multiderivation K (PolynomialFunctions K d) 3 from
        schoutenBracket K d 1 1 F G) =
      ∑ c : Fin 3,
        ((bivectorForward (cyclicPermutation c)).templateTensor (bivectorPairTensors F G) +
          (bivectorReverse (cyclicPermutation c)).templateTensor (bivectorPairTensors F G)) := by
  funext i
  simp only [rawTensor_three, Finset.sum_apply, Pi.add_apply, Graph.templateTensor]
  exact bivector_bracket_graphs F G i

/-- The entire vector action tensor is the canonical plus/minus/plus template sum. -/
theorem rawTensor_vector_bivector
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) :
    rawTensor (schoutenVectorAction 1 X F) =
      vectorBivectorForward.templateTensor (vectorBivectorPairTensors X F) -
        (vectorBivectorBackward 1).templateTensor (vectorBivectorPairTensors X F) +
        (vectorBivectorBackward (Equiv.swap 0 1)).templateTensor (vectorBivectorPairTensors X F) := by
  funext i
  simp only [rawTensor_two, Pi.add_apply, Pi.sub_apply, Graph.templateTensor]
  exact vector_bivector_graphs X F i

section OuterGraph

variable {n m : ℕ} {q : Fin n → ℕ}

/-- Arity equality transports only the ordered tensor domain. -/
def tensorCast {p p' : ℕ} (h : p = p') : Tensor p d K →ₗ[K] Tensor p' d K := by
  subst p'
  exact LinearMap.id

omit [CharZero K] in
@[simp] theorem tensorCast_rfl {p : ℕ} (T : Tensor p d K) : tensorCast rfl T = T := rfl

/-- A trivector source vertex in any graph expands into six genuine local
template tensors, with its outgoing slots and all other tensors fixed. -/
theorem cochainOperator_bivector_bracket_templates (Γ : Graph q m) (r : Fin n)
    (hq : 3 = q r) (T : (v : Fin n) → Tensor (q v) d K)
    (F G : Multiderivation K (PolynomialFunctions K d) 2)
    (f : Fin m → Polynomial d K) :
    Γ.cochainOperator (Function.update T r
        (tensorCast hq (rawTensor (show Multiderivation K (PolynomialFunctions K d) 3 from
          schoutenBracket K d 1 1 F G)))) f =
      ∑ c : Fin 3,
        (Γ.cochainOperator (Function.update T r
          (tensorCast hq ((bivectorForward (cyclicPermutation c)).templateTensor
            (bivectorPairTensors F G)))) f +
        Γ.cochainOperator (Function.update T r
          (tensorCast hq ((bivectorReverse (cyclicPermutation c)).templateTensor
            (bivectorPairTensors F G)))) f) := by
  classical
  rw [rawTensor_bivector_bracket, map_sum]
  rw [MultilinearMap.map_update_sum]
  simp only [map_add, MultilinearMap.map_update_add, sum_apply, add_apply]

/-- The raw vector action in an arbitrary graph has the same three signs as
the actual local Schouten action, before any geometric coefficients. -/
theorem cochainOperator_vector_bivector_templates (Γ : Graph q m) (r : Fin n)
    (hq : 2 = q r) (T : (v : Fin n) → Tensor (q v) d K)
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2)
    (f : Fin m → Polynomial d K) :
    Γ.cochainOperator (Function.update T r
        (tensorCast hq (rawTensor (schoutenVectorAction 1 X F)))) f =
      Γ.cochainOperator (Function.update T r
        (tensorCast hq (vectorBivectorForward.templateTensor (vectorBivectorPairTensors X F)))) f -
      Γ.cochainOperator (Function.update T r
        (tensorCast hq ((vectorBivectorBackward 1).templateTensor (vectorBivectorPairTensors X F)))) f +
      Γ.cochainOperator (Function.update T r
        (tensorCast hq ((vectorBivectorBackward (Equiv.swap 0 1)).templateTensor
          (vectorBivectorPairTensors X F)))) f := by
  classical
  rw [rawTensor_vector_bivector]
  simp only [map_add, map_sub, MultilinearMap.map_update_add,
    MultilinearMap.map_update_sub, add_apply, sub_apply]

end OuterGraph

end EnvelopingIsomorphism.Deformation.SchoutenGraphContraction
