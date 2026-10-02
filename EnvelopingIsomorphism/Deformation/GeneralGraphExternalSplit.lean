import EnvelopingIsomorphism.Deformation.GeneralGraphSplitConstruction
import EnvelopingIsomorphism.Deformation.GraphLeibnizFinset
import Mathlib.Algebra.BigOperators.Fin

/-! Actual external-vertex splitting for graph operators. Incoming arrows are
assigned to the two consecutive factors using the position-sensitive Leibniz
formula; all edge labels and internal polynomial tensors are retained. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open MvPolynomial
open scoped BigOperators

namespace Graph

variable {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin n → ℕ}

def incomingSubtypeEquiv (Γ : Graph q m) (r : Fin m) :
    Γ.incoming (Sum.inr r) ≃ {e : Edge q // Γ.target e = Sum.inr r} where
  toFun e := ⟨e.val, by simpa only [incoming, Finset.mem_filter, Finset.mem_univ, true_and] using e.property⟩
  invFun e := ⟨e.val, by simpa only [incoming, Finset.mem_filter, Finset.mem_univ, true_and] using e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def splitChoicesEquiv (Γ : Graph q m) (r : Fin m) :
    Γ.SplitExternalChoices r ≃ (Γ.incoming (Sum.inr r) → Fin 2) :=
  Equiv.arrowCongr (Γ.incomingSubtypeEquiv r).symm (Equiv.refl _)

theorem splitChoicesEquiv_apply (Γ : Graph q m) (r : Fin m) (χ : Γ.SplitExternalChoices r)
    (e : Γ.incoming (Sum.inr r)) :
    Γ.splitChoicesEquiv r χ e = Γ.splitExternalChoice r χ e.val := by
  have he : Γ.target e.val = Sum.inr r := (Γ.incomingSubtypeEquiv r e).property
  rw [splitExternalChoice_of_hit Γ r χ e.val he]
  rfl

theorem assignedEdges_splitChoicesEquiv (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (j : Fin 2) :
    assignedEdges (Γ.incoming (Sum.inr r)) (Γ.splitChoicesEquiv r χ) j =
      (Γ.incoming (Sum.inr r)).filter (fun e ↦ Γ.splitExternalChoice r χ e = j) := by
  classical
  ext e
  rw [mem_assignedEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, hχ⟩
    exact ⟨he, (Γ.splitChoicesEquiv_apply r χ ⟨e, he⟩).symm.trans hχ⟩
  · rintro ⟨he, hχ⟩
    exact ⟨he, (Γ.splitChoicesEquiv_apply r χ ⟨e, he⟩).trans hχ⟩

@[simp] theorem vertexDerivative_split_internal (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (lab : Edge q → Fin d) (v : Fin n) :
    (Γ.splitExternal r χ).vertexDerivative (R := R) lab (Sum.inl v) =
      Γ.vertexDerivative lab (Sum.inl v) := by
  rw [vertexDerivative, incoming_splitExternal_internal]
  rfl

theorem vertexDerivative_split_unaffected (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (lab : Edge q → Fin d) (j : Fin m) (hj : j ≠ r) :
    (Γ.splitExternal r χ).vertexDerivative (R := R) lab (Sum.inr (splitExternalEmbedding r j)) =
      Γ.vertexDerivative lab (Sum.inr j) := by
  rw [vertexDerivative, incoming_splitExternal_unaffected Γ r χ j hj]
  rfl

/-- The literal sum over split admissible graphs is the derivative of a product. -/
theorem vertexDerivative_product_split (Γ : Graph q m) (r : Fin m) (lab : Edge q → Fin d)
    (f g : Polynomial d R) :
    Γ.vertexDerivative lab (Sum.inr r) (f * g) =
      ∑ χ : Γ.SplitExternalChoices r,
        (Γ.splitExternal r χ).vertexDerivative lab (Sum.inr r.castSucc) f *
          (Γ.splitExternal r χ).vertexDerivative lab (Sum.inr r.succ) g := by
  classical
  have h := iteratedPDeriv_edge_prod (Γ.incoming (Sum.inr r)) lab (![f, g] : Fin 2 → Polynomial d R)
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change iteratedPDeriv _ (f * g) = _
  refine h.trans ?_
  symm
  apply Fintype.sum_equiv (Γ.splitChoicesEquiv r)
  intro χ
  rw [vertexDerivative, vertexDerivative, incoming_splitExternal_left, incoming_splitExternal_right,
    assignedEdges_splitChoicesEquiv, assignedEdges_splitChoicesEquiv]

/-- Merge consecutive exterior inputs by multiplication; all other positions keep their order. -/
def mergeExternalInputs (r : Fin m) (f : Fin (m + 1) → Polynomial d R) : Fin m → Polynomial d R :=
  Function.update (fun j ↦ f (splitExternalEmbedding r j)) r (f r.castSucc * f r.succ)

def externalRemainder (Γ : Graph q m) (r : Fin m) (lab : Edge q → Fin d)
    (f : Fin (m + 1) → Polynomial d R) : Polynomial d R :=
  ∏ j ∈ Finset.univ.erase r, Γ.vertexDerivative lab (Sum.inr j) (f (splitExternalEmbedding r j))

theorem externalProduct_merge (Γ : Graph q m) (r : Fin m) (lab : Edge q → Fin d)
    (f : Fin (m + 1) → Polynomial d R) :
    (∏ j, Γ.vertexDerivative lab (Sum.inr j) (mergeExternalInputs r f j)) =
      Γ.vertexDerivative lab (Sum.inr r) (f r.castSucc * f r.succ) * Γ.externalRemainder r lab f := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  simp only [mergeExternalInputs, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem externalProduct_split (Γ : Graph q m) (r : Fin m) (χ : Γ.SplitExternalChoices r)
    (lab : Edge q → Fin d) (f : Fin (m + 1) → Polynomial d R) :
    (∏ j, (Γ.splitExternal r χ).vertexDerivative lab (Sum.inr j) (f j)) =
      ((Γ.splitExternal r χ).vertexDerivative lab (Sum.inr r.castSucc) (f r.castSucc) *
        (Γ.splitExternal r χ).vertexDerivative lab (Sum.inr r.succ) (f r.succ)) *
          Γ.externalRemainder r lab f := by
  classical
  rw [Fin.prod_univ_succAbove _ r.castSucc]
  change _ * (∏ j : Fin m, (Γ.splitExternal r χ).vertexDerivative lab
    (Sum.inr (splitExternalEmbedding r j)) (f (splitExternalEmbedding r j))) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), splitExternalEmbedding_self, ← mul_assoc]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [vertexDerivative_split_unaffected Γ r χ lab j (Finset.mem_erase.mp hj).1]

/-- Inserting ordinary multiplication into a graph cochain is exactly the finite
sum of admissible graphs obtained by distributing all incoming edges between
the two consecutive new exterior vertices. No weight or formality identity is
assumed, and empty incoming sets contribute their unique empty assignment. -/
theorem cochainOperator_mergeExternal (Γ : Graph q m) (r : Fin m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin (m + 1) → Polynomial d R) :
    Γ.cochainOperator T (mergeExternalInputs r f) =
      ∑ χ : Γ.SplitExternalChoices r, (Γ.splitExternal r χ).cochainOperator T f := by
  classical
  simp only [cochainOperator_apply, vertexDerivative_split_internal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lab hlab
  rw [externalProduct_merge, vertexDerivative_product_split]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [externalProduct_split]

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
