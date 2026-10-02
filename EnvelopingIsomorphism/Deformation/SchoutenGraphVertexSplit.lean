import EnvelopingIsomorphism.Deformation.SchoutenVertexTemplates
import EnvelopingIsomorphism.Deformation.GeneralGraphInternalSubstitution

/-! Actual source-side graph contraction identities in the two low arities.
These are raw operator identities; every incoming arrow assignment and each
coefficient in the six-term or three-term expansion remains explicit. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.SchoutenGraphContraction

open scoped BigOperators
open KontsevichGraph.General
open KontsevichGraph.General.TwoVertexContraction

variable {K : Type*} [Field K] [CharZero K] {n m d p : ℕ}
  {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}

omit [CharZero K] in
theorem tensorCast_eq_transport {p p' : ℕ} (h : p = p') (T : Tensor p d K) :
    tensorCast h T = h ▸ T := by
  subst p'
  rfl

omit [CharZero K] in
theorem cochainOperator_template_vertexSplit (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal p) (hq : p = q r) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d K)
    (U : (c : Fin 2) → Tensor (qLocal c) d K) (f : Fin m → Polynomial d K) :
    Γ.cochainOperator (Function.update T r (tensorCast hq (Θ.templateTensor U))) f =
      ∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit Θ r hq.symm χ).cochainOperator (vertexSplitTensors q qLocal r T U) f := by
  rw [tensorCast_eq_transport]
  exact Graph.cochainOperator_vertexSplit_arity Γ r Θ hq.symm legEdge hleg T U f

def bivectorForwardLeg (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) : Edge bivectorArity :=
  ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩] (ρ.symm j)

def bivectorReverseLeg (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) : Edge bivectorArity :=
  ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩] (ρ.symm j)

def vectorBivectorForwardLeg (j : Fin 2) : Edge vectorBivectorArity := ⟨1, j⟩

def vectorBivectorBackwardLeg (ρ : Equiv.Perm (Fin 2)) (j : Fin 2) : Edge vectorBivectorArity :=
  ![⟨0, 0⟩, ⟨1, 1⟩] (ρ.symm j)

theorem bivectorForward_incoming_leg (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (bivectorForward ρ).incoming (Sum.inr j) = {bivectorForwardLeg ρ j} := by
  simpa only [Equiv.apply_symm_apply, bivectorForwardLeg] using
    bivectorForward_incoming_external ρ (ρ.symm j)

theorem bivectorReverse_incoming_leg (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (bivectorReverse ρ).incoming (Sum.inr j) = {bivectorReverseLeg ρ j} := by
  simpa only [Equiv.apply_symm_apply, bivectorReverseLeg] using
    bivectorReverse_incoming_external ρ (ρ.symm j)

theorem vectorBivectorForward_incoming_leg (j : Fin 2) :
    vectorBivectorForward.incoming (Sum.inr j) = {vectorBivectorForwardLeg j} :=
  vectorBivectorForward_incoming_external j

theorem vectorBivectorBackward_incoming_leg (ρ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (vectorBivectorBackward ρ).incoming (Sum.inr j) = {vectorBivectorBackwardLeg ρ j} := by
  simpa only [Equiv.apply_symm_apply, vectorBivectorBackwardLeg] using
    vectorBivectorBackward_incoming_external ρ (ρ.symm j)

/-- Replacing a raw Schouten trivector vertex is the sum of six actual joined
graph families, each further summed over every incoming-arrow assignment. -/
theorem cochainOperator_bivector_bracket_vertexSplit (Γ : Graph q m) (r : Fin (n + 1))
    (hq : 3 = q r) (T : (v : Fin (n + 1)) → Tensor (q v) d K)
    (F G : Multiderivation K (PolynomialFunctions K d) 2)
    (f : Fin m → Polynomial d K) :
    Γ.cochainOperator (Function.update T r
        (tensorCast hq (rawTensor (show Multiderivation K (PolynomialFunctions K d) 3 from
          schoutenBracket K d 1 1 F G)))) f =
      ∑ c : Fin 3,
        ((∑ χ : Γ.VertexSplitChoices r,
          (Γ.vertexSplit (bivectorForward (cyclicPermutation c)) r hq.symm χ).cochainOperator
            (vertexSplitTensors q bivectorArity r T (bivectorPairTensors F G)) f) +
        ∑ χ : Γ.VertexSplitChoices r,
          (Γ.vertexSplit (bivectorReverse (cyclicPermutation c)) r hq.symm χ).cochainOperator
            (vertexSplitTensors q bivectorArity r T (bivectorPairTensors F G)) f) := by
  classical
  rw [cochainOperator_bivector_bracket_templates]
  apply Finset.sum_congr rfl
  intro c hc
  rw [cochainOperator_template_vertexSplit Γ r _ hq (bivectorForwardLeg _)
      (bivectorForward_incoming_leg _),
    cochainOperator_template_vertexSplit Γ r _ hq (bivectorReverseLeg _)
      (bivectorReverse_incoming_leg _)]

/-- Replacing the actual vector/bivector action vertex gives the three
admissible split graph families with raw signs plus, minus, plus. -/
theorem cochainOperator_vector_bivector_vertexSplit (Γ : Graph q m) (r : Fin (n + 1))
    (hq : 2 = q r) (T : (v : Fin (n + 1)) → Tensor (q v) d K)
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2)
    (f : Fin m → Polynomial d K) :
    Γ.cochainOperator (Function.update T r
        (tensorCast hq (rawTensor (schoutenVectorAction 1 X F)))) f =
      (∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit vectorBivectorForward r hq.symm χ).cochainOperator
          (vertexSplitTensors q vectorBivectorArity r T (vectorBivectorPairTensors X F)) f) -
      (∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit (vectorBivectorBackward 1) r hq.symm χ).cochainOperator
          (vertexSplitTensors q vectorBivectorArity r T (vectorBivectorPairTensors X F)) f) +
      ∑ χ : Γ.VertexSplitChoices r,
        (Γ.vertexSplit (vectorBivectorBackward (Equiv.swap 0 1)) r hq.symm χ).cochainOperator
          (vertexSplitTensors q vectorBivectorArity r T (vectorBivectorPairTensors X F)) f := by
  classical
  rw [cochainOperator_vector_bivector_templates,
    cochainOperator_template_vertexSplit Γ r _ hq vectorBivectorForwardLeg
      vectorBivectorForward_incoming_leg,
    cochainOperator_template_vertexSplit Γ r _ hq (vectorBivectorBackwardLeg _)
      (vectorBivectorBackward_incoming_leg _),
    cochainOperator_template_vertexSplit Γ r _ hq (vectorBivectorBackwardLeg _)
      (vectorBivectorBackward_incoming_leg _)]

end EnvelopingIsomorphism.Deformation.SchoutenGraphContraction
