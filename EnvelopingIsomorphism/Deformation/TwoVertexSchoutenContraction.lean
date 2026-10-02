import EnvelopingIsomorphism.Deformation.SchoutenGraphContraction
import EnvelopingIsomorphism.Deformation.TwoVertexContractionGraphs

/-! The raw low Schouten coordinate contractions are actual two-vertex graph
operators. Only canonical first-slot internal arrows occur here; their raw
numerical multiplicities are not folded into any geometric normalization. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.SchoutenGraphContraction

open MvPolynomial
open scoped BigOperators
open KontsevichGraph.General
open KontsevichGraph.General.TwoVertexContraction

universe u
variable {K : Type u} [Field K] [CharZero K] {d : ℕ}

/-- Actual raw coordinate tensor of a polynomial multiderivation. -/
def rawTensor {r : ℕ} (F : Multiderivation K (PolynomialFunctions K d) r) : Tensor r d K :=
  fun lab ↦ F (fun j ↦ MvPolynomial.X (lab j))

omit [CharZero K] in
theorem rawTensor_one (X : Multiderivation K (PolynomialFunctions K d) 1) (lab : Fin 1 → Fin d) :
    rawTensor X lab = vectorComponent X (lab 0) := by
  rw [vectorComponent_apply]
  apply congrArg X
  funext j
  fin_cases j
  rfl

omit [CharZero K] in
theorem rawTensor_two (F : Multiderivation K (PolynomialFunctions K d) 2) (lab : Fin 2 → Fin d) :
    rawTensor F lab = bivectorComponent F (lab 0) (lab 1) := by
  rw [bivectorComponent_apply]
  apply congrArg F
  funext j
  fin_cases j <;> rfl

def bivectorPairTensors (F G : Multiderivation K (PolynomialFunctions K d) 2) : Fin 2 → Tensor 2 d K :=
  ![rawTensor F, rawTensor G]

def vectorBivectorPairTensors (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) :
    (v : Fin 2) → Tensor (vectorBivectorArity v) d K :=
  Fin.cons (α := fun v ↦ Tensor (vectorBivectorArity v) d K) (rawTensor X) (fun _ : Fin 1 ↦ rawTensor F)

omit [CharZero K] in
theorem bivectorForward_join (ρ : Equiv.Perm (Fin 3))
    (F G : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 3 → Fin d) :
    (bivectorForward ρ).cochainOperator (bivectorPairTensors F G) (fun j ↦ MvPolynomial.X (i j)) =
      bivectorJoin F G (i (ρ 0)) (i (ρ 1)) (i (ρ 2)) := by
  rw [bivectorForward_cochainOperator_X]
  simp only [bivectorPairTensors, Matrix.cons_val_zero, Matrix.cons_val_one, rawTensor_two]
  rfl

omit [CharZero K] in
theorem bivectorReverse_join (ρ : Equiv.Perm (Fin 3))
    (F G : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 3 → Fin d) :
    (bivectorReverse ρ).cochainOperator (bivectorPairTensors F G) (fun j ↦ MvPolynomial.X (i j)) =
      bivectorJoin G F (i (ρ 0)) (i (ρ 1)) (i (ρ 2)) := by
  rw [bivectorReverse_cochainOperator_X]
  simp only [bivectorPairTensors, Matrix.cons_val_zero, Matrix.cons_val_one, rawTensor_two]
  rfl

omit [CharZero K] in
theorem vectorBivectorForward_join
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 2 → Fin d) :
    vectorBivectorForward.cochainOperator (vectorBivectorPairTensors X F) (fun j ↦ MvPolynomial.X (i j)) =
      vectorToBivector X F (i 0) (i 1) := by
  rw [vectorBivectorForward_cochainOperator_X]
  change (∑ s : Fin d, rawTensor X ![s] * pderiv s (rawTensor F ![i 0, i 1])) = _
  simp only [rawTensor_one, rawTensor_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

omit [CharZero K] in
theorem vectorBivectorBackward_join (ρ : Equiv.Perm (Fin 2))
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 2 → Fin d) :
    (vectorBivectorBackward ρ).cochainOperator (vectorBivectorPairTensors X F) (fun j ↦ MvPolynomial.X (i j)) =
      bivectorToVectorLeft F X (i (ρ 0)) (i (ρ 1)) := by
  rw [vectorBivectorBackward_cochainOperator_X]
  change (∑ s : Fin d, rawTensor F ![s, i (ρ 1)] * pderiv s (rawTensor X ![i (ρ 0)])) = _
  simp only [rawTensor_one, rawTensor_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

def cyclicPermutation : Fin 3 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1]

/-- Six genuine joined graph operators, each with raw coefficient one. -/
theorem bivector_bracket_graphs
    (F G : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 3 → Fin d) :
    trivectorComponent
        (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F G)
        (i 0) (i 1) (i 2) =
      ∑ c : Fin 3,
        ((bivectorForward (cyclicPermutation c)).cochainOperator (bivectorPairTensors F G)
            (fun j ↦ MvPolynomial.X (i j)) +
          (bivectorReverse (cyclicPermutation c)).cochainOperator (bivectorPairTensors F G)
            (fun j ↦ MvPolynomial.X (i j))) := by
  rw [bivector_bracket_coordinates]
  simp only [bivectorForward_join, bivectorReverse_join, Fin.sum_univ_three]
  simp [cyclicPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  abel

/-- The actual vector/bivector bracket gives the three canonical graphs with
signs plus, minus, plus; no outgoing factorial ratio is assumed. -/
theorem vector_bivector_graphs
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i : Fin 2 → Fin d) :
    bivectorComponent (schoutenVectorAction 1 X F) (i 0) (i 1) =
      vectorBivectorForward.cochainOperator (vectorBivectorPairTensors X F) (fun j ↦ MvPolynomial.X (i j)) -
        (vectorBivectorBackward 1).cochainOperator (vectorBivectorPairTensors X F) (fun j ↦ MvPolynomial.X (i j)) +
        (vectorBivectorBackward (Equiv.swap 0 1)).cochainOperator (vectorBivectorPairTensors X F)
          (fun j ↦ MvPolynomial.X (i j)) := by
  rw [vector_bivector_coordinates_canonical, vectorBivectorForward_join,
    vectorBivectorBackward_join, vectorBivectorBackward_join]
  simp

end EnvelopingIsomorphism.Deformation.SchoutenGraphContraction
