import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual two-vertex contraction graphs and their values on coordinate inputs. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.TwoVertexContraction

open MvPolynomial
open scoped BigOperators

abbrev bivectorArity : Fin 2 → ℕ := fun _ ↦ 2

def bivectorLabels {α : Type*} (x : (α × α) × (α × α)) : Edge bivectorArity → α :=
  fun e ↦ ![![x.1.1, x.1.2], ![x.2.1, x.2.2]] e.1 e.2

def bivectorLabelEquiv (α : Type*) :
    (Edge bivectorArity → α) ≃ (α × α) × (α × α) where
  toFun lab := ((lab ⟨0, 0⟩, lab ⟨0, 1⟩), (lab ⟨1, 0⟩, lab ⟨1, 1⟩))
  invFun := bivectorLabels
  left_inv lab := by
    funext e
    rcases e with ⟨v, j⟩
    fin_cases v <;> fin_cases j <;> rfl
  right_inv x := rfl

theorem sum_bivectorLabels {α M : Type*} [Fintype α] [AddCommMonoid M]
    (F : (Edge bivectorArity → α) → M) :
    ∑ lab, F lab = ∑ x, ∑ y, ∑ z, ∑ w, F (bivectorLabels ((x, y), (z, w))) := by
  rw [← (bivectorLabelEquiv α).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The distinguished internal arrow is outgoing slot zero at internal vertex zero. -/
def bivectorForward (ρ : Equiv.Perm (Fin 3)) : Graph bivectorArity 3 where
  target e := ![![Sum.inl 1, Sum.inr (ρ 2)], ![Sum.inr (ρ 0), Sum.inr (ρ 1)]] e.1 e.2
  noLoops v j := by fin_cases v <;> fin_cases j <;> simp
  distinctTargets v j k h := by
    fin_cases v <;> fin_cases j <;> fin_cases k <;> simp_all

@[simp] theorem bivectorForward_target00 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).target ⟨0, 0⟩ = Sum.inl 1 := rfl

@[simp] theorem bivectorForward_target01 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).target ⟨0, 1⟩ = Sum.inr (ρ 2) := rfl

@[simp] theorem bivectorForward_target10 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).target ⟨1, 0⟩ = Sum.inr (ρ 0) := rfl

@[simp] theorem bivectorForward_target11 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).target ⟨1, 1⟩ = Sum.inr (ρ 1) := rfl

@[simp] theorem bivectorForward_incoming0 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).incoming (Sum.inl 0) = ∅ := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming]

@[simp] theorem bivectorForward_incoming1 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward ρ).incoming (Sum.inl 1) = {⟨0, 0⟩} := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming]

@[simp] theorem bivectorForward_incoming_external (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (bivectorForward ρ).incoming (Sum.inr (ρ j)) =
      {![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩] j} := by
  ext ⟨v, k⟩
  fin_cases j <;> fin_cases v <;> fin_cases k <;> simp [Graph.incoming]

variable {R : Type*} [CommRing R] {d : ℕ}

theorem bivectorForward_labelled_X (ρ : Equiv.Perm (Fin 3))
    (T : Fin 2 → Tensor 2 d R) (i : Fin 3 → Fin d)
    (x y z w : Fin d) :
    (bivectorForward ρ).labelledOperator (bivectorLabels ((x, y), (z, w)))
      (Sum.rec T (fun j ↦ X (i j))) =
      T 0 ![x, y] * pderiv x (T 1 ![z, w]) *
        (pderiv z (X (i (ρ 0))) * pderiv w (X (i (ρ 1))) *
          pderiv y (X (i (ρ 2)))) := by
  rw [Graph.labelledOperator_apply, Fintype.prod_sum_type]
  rw [← Equiv.prod_comp ρ (fun j ↦ (bivectorForward ρ).vertexDerivative
    (bivectorLabels ((x, y), (z, w))) (Sum.inr j)
      (Graph.vertexEvaluation (bivectorLabels ((x, y), (z, w))) (Sum.inr j) (X (i j))))]
  simp [Fin.prod_univ_two, Fin.prod_univ_three, Graph.vertexDerivative, Graph.vertexEvaluation,
    bivectorLabels, EnvelopingIsomorphism.Deformation.iteratedPDeriv, mul_assoc]

/-- The forward bivector graph evaluates to the actual coefficient contraction. -/
theorem bivectorForward_cochainOperator_X (ρ : Equiv.Perm (Fin 3))
    (T : Fin 2 → Tensor 2 d R) (i : Fin 3 → Fin d) :
    (bivectorForward ρ).cochainOperator T (fun j ↦ X (i j)) =
      ∑ s, T 0 ![s, i (ρ 2)] * pderiv s (T 1 ![i (ρ 0), i (ρ 1)]) := by
  change (bivectorForward ρ).operator (Sum.rec T (fun j ↦ X (i j))) = _
  simp only [Graph.operator, sum_apply]
  rw [sum_bivectorLabels]
  simp only [bivectorForward_labelled_X]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]

/-- The reversed contraction has outgoing slot zero at vertex one as its internal arrow. -/
def bivectorReverse (ρ : Equiv.Perm (Fin 3)) : Graph bivectorArity 3 where
  target e := ![![Sum.inr (ρ 0), Sum.inr (ρ 1)], ![Sum.inl 0, Sum.inr (ρ 2)]] e.1 e.2
  noLoops v j := by fin_cases v <;> fin_cases j <;> simp
  distinctTargets v j k h := by
    fin_cases v <;> fin_cases j <;> fin_cases k <;> simp_all

@[simp] theorem bivectorReverse_incoming0 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorReverse ρ).incoming (Sum.inl 0) = {⟨1, 0⟩} := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, bivectorReverse]

@[simp] theorem bivectorReverse_incoming1 (ρ : Equiv.Perm (Fin 3)) :
    (bivectorReverse ρ).incoming (Sum.inl 1) = ∅ := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, bivectorReverse]

@[simp] theorem bivectorReverse_incoming_external (ρ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (bivectorReverse ρ).incoming (Sum.inr (ρ j)) =
      {![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩] j} := by
  ext ⟨v, k⟩
  fin_cases j <;> fin_cases v <;> fin_cases k <;> simp [Graph.incoming, bivectorReverse]

theorem bivectorReverse_labelled_X (ρ : Equiv.Perm (Fin 3))
    (T : Fin 2 → Tensor 2 d R) (i : Fin 3 → Fin d)
    (x y z w : Fin d) :
    (bivectorReverse ρ).labelledOperator (bivectorLabels ((x, y), (z, w)))
      (Sum.rec T (fun j ↦ X (i j))) =
      T 1 ![z, w] * pderiv z (T 0 ![x, y]) *
        (pderiv x (X (i (ρ 0))) * pderiv y (X (i (ρ 1))) *
          pderiv w (X (i (ρ 2)))) := by
  rw [Graph.labelledOperator_apply, Fintype.prod_sum_type]
  rw [← Equiv.prod_comp ρ (fun j ↦ (bivectorReverse ρ).vertexDerivative
    (bivectorLabels ((x, y), (z, w))) (Sum.inr j)
      (Graph.vertexEvaluation (bivectorLabels ((x, y), (z, w))) (Sum.inr j) (X (i j))))]
  simp [Fin.prod_univ_two, Fin.prod_univ_three, Graph.vertexDerivative, Graph.vertexEvaluation,
    bivectorLabels, EnvelopingIsomorphism.Deformation.iteratedPDeriv, mul_assoc, mul_comm]

/-- The reverse bivector graph differentiates the tensor at vertex zero. -/
theorem bivectorReverse_cochainOperator_X (ρ : Equiv.Perm (Fin 3))
    (T : Fin 2 → Tensor 2 d R) (i : Fin 3 → Fin d) :
    (bivectorReverse ρ).cochainOperator T (fun j ↦ X (i j)) =
      ∑ s, T 1 ![s, i (ρ 2)] * pderiv s (T 0 ![i (ρ 0), i (ρ 1)]) := by
  change (bivectorReverse ρ).operator (Sum.rec T (fun j ↦ X (i j))) = _
  simp only [Graph.operator, sum_apply]
  rw [sum_bivectorLabels]
  simp only [bivectorReverse_labelled_X]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]

/-- A vector vertex followed by a bivector vertex. -/
abbrev vectorBivectorArity : Fin 2 → ℕ := fun v ↦ if v.val = 0 then 1 else 2

theorem vectorBivectorArity_eq_cons :
    vectorBivectorArity = Fin.cons 1 (fun _ : Fin 1 ↦ 2) := by
  funext v
  fin_cases v <;> rfl

instance : NeZero (vectorBivectorArity 0) := ⟨by simp [vectorBivectorArity]⟩
instance : NeZero (vectorBivectorArity 1) := ⟨by simp [vectorBivectorArity]⟩

private theorem fin_one_const {α : Type*} (x : α) : (fun _ : Fin 1 ↦ x) = ![x] := by
  funext i
  fin_cases i
  rfl

def vectorBivectorLabels {α : Type*} (x : α × (α × α)) : Edge vectorBivectorArity → α :=
  fun e ↦ Fin.cons (α := fun v ↦ Fin (vectorBivectorArity v) → α) (fun _ : Fin 1 ↦ x.1)
    (fun _ : Fin 1 ↦ fun j : Fin 2 ↦ ![x.2.1, x.2.2] j) e.1 e.2

def vectorBivectorLabelEquiv (α : Type*) :
    (Edge vectorBivectorArity → α) ≃ α × (α × α) where
  toFun lab := (lab ⟨0, 0⟩, (lab ⟨1, 0⟩, lab ⟨1, 1⟩))
  invFun := vectorBivectorLabels
  left_inv lab := by
    funext e
    rcases e with ⟨v, j⟩
    fin_cases v <;> fin_cases j <;> rfl
  right_inv x := rfl

theorem sum_vectorBivectorLabels {α M : Type*} [Fintype α] [AddCommMonoid M]
    (F : (Edge vectorBivectorArity → α) → M) :
    ∑ lab, F lab = ∑ x, ∑ y, ∑ z, F (vectorBivectorLabels (x, (y, z))) := by
  rw [← (vectorBivectorLabelEquiv α).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The vector's sole arrow differentiates the bivector coefficient. -/
def vectorBivectorForward : Graph vectorBivectorArity 2 where
  target e := Fin.cons (α := fun v ↦ Fin (vectorBivectorArity v) → Vertex 2 2)
    (fun _ : Fin 1 ↦ Sum.inl 1)
    (fun _ : Fin 1 ↦ fun j : Fin 2 ↦ Sum.inr j) e.1 e.2
  noLoops v j := by fin_cases v <;> fin_cases j <;> simp
  distinctTargets v j k h := by
    fin_cases v <;> fin_cases j <;> fin_cases k <;> simp_all

@[simp] theorem vectorBivectorForward_incoming0 :
    vectorBivectorForward.incoming (Sum.inl 0) = ∅ := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, vectorBivectorForward]

@[simp] theorem vectorBivectorForward_incoming1 :
    vectorBivectorForward.incoming (Sum.inl 1) = {⟨0, 0⟩} := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, vectorBivectorForward]

@[simp] theorem vectorBivectorForward_incoming_external (j : Fin 2) :
    vectorBivectorForward.incoming (Sum.inr j) = {⟨1, j⟩} := by
  ext ⟨v, k⟩
  fin_cases j <;> fin_cases v <;> fin_cases k <;>
    simp [Graph.incoming, vectorBivectorForward]
  all_goals norm_num [vectorBivectorArity, Fin.ext_iff]
  · decide
  · rfl

theorem vectorBivectorForward_labelled_X
    (T : (v : Fin 2) → Tensor (vectorBivectorArity v) d R) (i : Fin 2 → Fin d)
    (x y z : Fin d) :
    vectorBivectorForward.labelledOperator (vectorBivectorLabels (x, (y, z)))
      (Sum.rec T (fun j ↦ X (i j))) =
      T 0 ![x] * pderiv x (T 1 ![y, z]) *
        (pderiv y (X (i 0)) * pderiv z (X (i 1))) := by
  rw [Graph.labelledOperator_apply, Fintype.prod_sum_type]
  simp [Fin.prod_univ_two, Graph.vertexDerivative, Graph.vertexEvaluation,
    vectorBivectorLabels, vectorBivectorArity,
    EnvelopingIsomorphism.Deformation.iteratedPDeriv, mul_assoc, fin_one_const]

/-- Actual vector-on-bivector coefficient contraction, without a degree restriction. -/
theorem vectorBivectorForward_cochainOperator_X
    (T : (v : Fin 2) → Tensor (vectorBivectorArity v) d R) (i : Fin 2 → Fin d) :
    vectorBivectorForward.cochainOperator T (fun j ↦ X (i j)) =
      ∑ s, T 0 ![s] * pderiv s (T 1 ![i 0, i 1]) := by
  change vectorBivectorForward.operator (Sum.rec T (fun j ↦ X (i j))) = _
  simp only [Graph.operator, sum_apply]
  rw [sum_vectorBivectorLabels]
  simp only [vectorBivectorForward_labelled_X]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]

/-- The bivector's first arrow differentiates the vector coefficient. -/
def vectorBivectorBackward (ρ : Equiv.Perm (Fin 2)) : Graph vectorBivectorArity 2 where
  target e := Fin.cons (α := fun v ↦ Fin (vectorBivectorArity v) → Vertex 2 2)
    (fun _ : Fin 1 ↦ Sum.inr (ρ 0))
    (fun _ : Fin 1 ↦ fun j : Fin 2 ↦ ![Sum.inl 0, Sum.inr (ρ 1)] j) e.1 e.2
  noLoops v j := by fin_cases v <;> fin_cases j <;> simp [vectorBivectorArity]
  distinctTargets v j k h := by
    fin_cases v <;> fin_cases j <;> fin_cases k <;> simp_all [vectorBivectorArity]

@[simp] theorem vectorBivectorBackward_incoming0 (ρ : Equiv.Perm (Fin 2)) :
    (vectorBivectorBackward ρ).incoming (Sum.inl 0) = {⟨1, 0⟩} := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, vectorBivectorBackward, vectorBivectorArity]

@[simp] theorem vectorBivectorBackward_incoming1 (ρ : Equiv.Perm (Fin 2)) :
    (vectorBivectorBackward ρ).incoming (Sum.inl 1) = ∅ := by
  ext ⟨v, j⟩
  fin_cases v <;> fin_cases j <;> simp [Graph.incoming, vectorBivectorBackward, vectorBivectorArity]

@[simp] theorem vectorBivectorBackward_incoming_external (ρ : Equiv.Perm (Fin 2))
    (j : Fin 2) :
    (vectorBivectorBackward ρ).incoming (Sum.inr (ρ j)) = {![⟨0, 0⟩, ⟨1, 1⟩] j} := by
  ext ⟨v, k⟩
  fin_cases j <;> fin_cases v <;> fin_cases k <;>
    simp [Graph.incoming, vectorBivectorBackward]
  all_goals norm_num [vectorBivectorArity, Fin.ext_iff]
  · change Sum.inr (ρ 1) ≠ (Sum.inr (ρ 0) : Vertex 2 2)
    simp
  · rfl

theorem vectorBivectorBackward_labelled_X (ρ : Equiv.Perm (Fin 2))
    (T : (v : Fin 2) → Tensor (vectorBivectorArity v) d R) (i : Fin 2 → Fin d)
    (x y z : Fin d) :
    (vectorBivectorBackward ρ).labelledOperator (vectorBivectorLabels (x, (y, z)))
      (Sum.rec T (fun j ↦ X (i j))) =
      T 1 ![y, z] * pderiv y (T 0 ![x]) *
        (pderiv x (X (i (ρ 0))) * pderiv z (X (i (ρ 1)))) := by
  rw [Graph.labelledOperator_apply, Fintype.prod_sum_type]
  rw [← Equiv.prod_comp ρ (fun j ↦ (vectorBivectorBackward ρ).vertexDerivative
    (vectorBivectorLabels (x, (y, z))) (Sum.inr j)
      (Graph.vertexEvaluation (vectorBivectorLabels (x, (y, z))) (Sum.inr j) (X (i j))))]
  simp [Fin.prod_univ_two, Graph.vertexDerivative, Graph.vertexEvaluation,
    vectorBivectorLabels, vectorBivectorArity, EnvelopingIsomorphism.Deformation.iteratedPDeriv,
    mul_assoc, mul_comm, fin_one_const]

/-- Actual bivector-on-vector coefficient contraction. The source-internal arrow remains
outgoing slot zero; no outgoing permutation sign or factorial is absorbed. -/
theorem vectorBivectorBackward_cochainOperator_X (ρ : Equiv.Perm (Fin 2))
    (T : (v : Fin 2) → Tensor (vectorBivectorArity v) d R) (i : Fin 2 → Fin d) :
    (vectorBivectorBackward ρ).cochainOperator T (fun j ↦ X (i j)) =
      ∑ s, T 1 ![s, i (ρ 1)] * pderiv s (T 0 ![i (ρ 0)]) := by
  change (vectorBivectorBackward ρ).operator (Sum.rec T (fun j ↦ X (i j))) = _
  simp only [Graph.operator, sum_apply]
  rw [sum_vectorBivectorLabels]
  simp only [vectorBivectorBackward_labelled_X]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.TwoVertexContraction
