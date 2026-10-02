import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitConstruction
import EnvelopingIsomorphism.Deformation.GeneralGraphInsertion
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLabels

/-! Substitution of a two-vertex graph template into an internal tensor slot.
External template legs are evaluated on coordinate functions; their actual
Kronecker factors identify the labels of the original outgoing edges. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {a p d : ℕ} {qLocal : Fin a → ℕ}

def internalProduct (Θ : Graph qLocal p) (U : (v : Fin a) → Tensor (qLocal v) d R)
    (lab : Edge qLocal → Fin d) : Polynomial d R :=
  ∏ v : Fin a, Θ.vertexDerivative lab (Sum.inl v) (U v (fun j ↦ lab ⟨v, j⟩))

def externalLabels (legEdge : Fin p → Edge qLocal) (lab : Edge qLocal → Fin d) : Fin p → Fin d :=
  fun j ↦ lab (legEdge j)

theorem single_leg_derivative_X (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (lab : Edge qLocal → Fin d) (j : Fin p) (i : Fin d) :
    Θ.vertexDerivative (R := R) lab (Sum.inr j) (MvPolynomial.X i) =
      if lab (legEdge j) = i then 1 else 0 := by
  classical
  rw [vertexDerivative, hleg]
  simp [iteratedPDeriv, pderiv_X, Pi.single_apply, eq_comm]

theorem product_leg_deltas (legEdge : Fin p → Edge qLocal) (lab : Edge qLocal → Fin d)
    (i : Fin p → Fin d) :
    (∏ j : Fin p, if lab (legEdge j) = i j then (1 : Polynomial d R) else 0) =
      if externalLabels legEdge lab = i then 1 else 0 := by
  classical
  by_cases h : externalLabels legEdge lab = i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    have hj' : lab (legEdge j) = i j := congrFun h j
    rw [if_pos hj']
  · rw [if_neg h]
    have hn : ¬ ∀ j, lab (legEdge j) = i j := fun he ↦ h (funext he)
    obtain ⟨j, hj⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- Coordinate inputs force every exterior edge label, with no factorial or
symmetry convention inserted. -/
theorem cochainOperator_X_delta (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (U : (v : Fin a) → Tensor (qLocal v) d R) (i : Fin p → Fin d) :
    Θ.cochainOperator U (fun j ↦ MvPolynomial.X (i j)) =
      ∑ lab : Edge qLocal → Fin d,
        if externalLabels legEdge lab = i then Θ.internalProduct U lab else 0 := by
  classical
  rw [cochainOperator_apply]
  apply Finset.sum_congr rfl
  intro lab hlab
  simp only [single_leg_derivative_X Θ legEdge hleg, product_leg_deltas]
  split_ifs <;> simp [internalProduct]

theorem leg_target_of_singleton (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j}) (j : Fin p) :
    Θ.target (legEdge j) = Sum.inr j := by
  have h : legEdge j ∈ Θ.incoming (Sum.inr j) := by rw [hleg]; simp
  simpa only [incoming, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem leg_complete_of_singleton (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (e : Edge qLocal) (j : Fin p) (he : Θ.target e = Sum.inr j) : e = legEdge j := by
  have h : e ∈ Θ.incoming (Sum.inr j) := by simp [incoming, he]
  rw [hleg, Finset.mem_singleton] at h
  exact h

/-- The exact polynomial tensor represented by a graph on its external coordinate legs. -/
def templateTensor (Θ : Graph qLocal p) (U : (v : Fin a) → Tensor (qLocal v) d R) : Tensor p d R :=
  fun i ↦ Θ.cochainOperator U (fun j ↦ MvPolynomial.X (i j))

theorem templateTensor_delta (Θ : Graph qLocal p) (legEdge : Fin p → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (U : (v : Fin a) → Tensor (qLocal v) d R) (i : Fin p → Fin d) :
    templateTensor Θ U i = ∑ lab : Edge qLocal → Fin d,
      if externalLabels legEdge lab = i then Θ.internalProduct U lab else 0 :=
  cochainOperator_X_delta Θ legEdge hleg U i

section RootFactor

variable {n m : ℕ} {q : Fin (n + 1) → ℕ}

/-- All factors away from the internal source which is being replaced. -/
def vertexOuterFactor (Γ : Graph q m) (r : Fin (n + 1)) (lab : Edge q → Fin d)
    (T : (v : Fin (n + 1)) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    Polynomial d R :=
  (∏ v : {v : Fin (n + 1) // v ≠ r},
    Γ.vertexDerivative lab (Sum.inl v.val) (T v.val (fun j ↦ lab ⟨v.val, j⟩))) *
      ∏ j : Fin m, Γ.vertexDerivative lab (Sum.inr j) (f j)

theorem cochainOperator_update_tensor_factor (Γ : Graph q m) (r : Fin (n + 1))
    (T : (v : Fin (n + 1)) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (S : Tensor (q r) d R) :
    Γ.cochainOperator (Function.update T r S) f = ∑ lab : Edge q → Fin d,
      Γ.vertexOuterFactor r lab T f *
        Γ.vertexDerivative lab (Sum.inl r) (S (fun j ↦ lab ⟨r, j⟩)) := by
  classical
  rw [cochainOperator_apply]
  apply Finset.sum_congr rfl
  intro lab hlab
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), Function.update_self]
  have hrest :
      (∏ v ∈ Finset.univ.erase r, Γ.vertexDerivative lab (Sum.inl v)
        (Function.update T r S v (fun j ↦ lab ⟨v, j⟩))) =
      ∏ v : {v : Fin (n + 1) // v ≠ r}, Γ.vertexDerivative lab (Sum.inl v.val)
        (T v.val (fun j ↦ lab ⟨v.val, j⟩)) := by
    rw [← Finset.prod_subtype (p := fun v : Fin (n + 1) ↦ v ≠ r)
      (Finset.univ.erase r) (by simp)
      (fun v ↦ Γ.vertexDerivative lab (Sum.inl v) (T v (fun j ↦ lab ⟨v, j⟩)))]
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
  rw [hrest]
  simp only [vertexOuterFactor]
  ring

/-- Actual coordinate delta expansion before any graph labels are reindexed. -/
theorem cochainOperator_template_delta (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal (q r)) (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (v : Fin a) → Tensor (qLocal v) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator (Function.update T r (Θ.templateTensor U)) f =
      ∑ oldLab : Edge q → Fin d, ∑ localLab : Edge qLocal → Fin d,
        if externalLabels legEdge localLab = (fun j ↦ oldLab ⟨r, j⟩) then
          Γ.vertexOuterFactor r oldLab T f *
            Γ.vertexDerivative oldLab (Sum.inl r) (Θ.internalProduct U localLab)
        else 0 := by
  classical
  rw [cochainOperator_update_tensor_factor]
  apply Finset.sum_congr rfl
  intro oldLab hLab
  rw [templateTensor_delta Θ legEdge hleg, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro localLab hLocal
  split_ifs <;> simp

/-- Summing the old outgoing labels eliminates exactly the coordinate deltas. -/
theorem sum_old_labels_delta {W : Type*} [AddCommMonoid W]
    (r : Fin (n + 1)) (legEdge : Fin (q r) → Edge qLocal)
    (F : (Edge q → Fin d) → (Edge qLocal → Fin d) → W) :
    (∑ oldLab : Edge q → Fin d, ∑ localLab : Edge qLocal → Fin d,
      if externalLabels legEdge localLab = (fun j ↦ oldLab ⟨r, j⟩)
      then F oldLab localLab else 0) =
      ∑ outsideLab : VertexSplitOutsideEdge q r → Fin d,
        ∑ localLab : Edge qLocal → Fin d,
          F ((vertexSplitOldLabelEquiv q r rfl d).symm
            (outsideLab, externalLabels legEdge localLab)) localLab := by
  classical
  let e := vertexSplitOldLabelEquiv q r rfl d
  calc
    _ = ∑ labels : (VertexSplitOutsideEdge q r → Fin d) × (Fin (q r) → Fin d),
        ∑ localLab : Edge qLocal → Fin d,
          if externalLabels legEdge localLab = labels.2
          then F (e.symm labels) localLab else 0 := by
      apply Fintype.sum_equiv e
      intro lab
      have hroot : (e lab).2 = (fun j ↦ lab ⟨r, j⟩) := rfl
      simp only [Equiv.symm_apply_apply, hroot]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro outsideLab hOutside
      rw [Finset.sum_comm]
      simp [e]

theorem cochainOperator_template_labels (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal (q r)) (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (v : Fin a) → Tensor (qLocal v) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator (Function.update T r (Θ.templateTensor U)) f =
      ∑ outsideLab : VertexSplitOutsideEdge q r → Fin d,
        ∑ localLab : Edge qLocal → Fin d,
          let oldLab := (vertexSplitOldLabelEquiv q r rfl d).symm
            (outsideLab, externalLabels legEdge localLab)
          Γ.vertexOuterFactor r oldLab T f *
            Γ.vertexDerivative oldLab (Sum.inl r) (Θ.internalProduct U localLab) := by
  rw [cochainOperator_template_delta Γ r Θ legEdge hleg, sum_old_labels_delta]

/-- After the coordinate deltas are eliminated, each incoming edge is assigned
to one actual internal template factor. -/
theorem cochainOperator_template_expansion (Γ : Graph q m) (r : Fin (n + 1))
    (Θ : Graph qLocal (q r)) (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.incoming (Sum.inr j) = {legEdge j})
    (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (U : (v : Fin a) → Tensor (qLocal v) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator (Function.update T r (Θ.templateTensor U)) f =
      ∑ χ : Γ.incoming (Sum.inl r) → Fin a,
        ∑ outsideLab : VertexSplitOutsideEdge q r → Fin d,
          ∑ localLab : Edge qLocal → Fin d,
            let oldLab := (vertexSplitOldLabelEquiv q r rfl d).symm
              (outsideLab, externalLabels legEdge localLab)
            Γ.vertexOuterFactor r oldLab T f * ∏ v : Fin a,
              iteratedPDeriv ((assignedEdges (Γ.incoming (Sum.inl r)) χ v).toList.map oldLab)
                (Θ.vertexDerivative localLab (Sum.inl v) (U v (fun j ↦ localLab ⟨v, j⟩))) := by
  classical
  rw [cochainOperator_template_labels Γ r Θ legEdge hleg]
  simp only [vertexDerivative, internalProduct, iteratedPDeriv_edge_prod, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext outsideLab
    rw [Finset.sum_comm]

end RootFactor

section SplitLabels

variable {n : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}

/-- Pulling the new labels back to old edges is exactly reconstruction from
outside labels and the labels selected by the external template legs. -/
theorem vertexSplitOldEdge_labels (r : Fin (n + 1)) (Θ : Graph qLocal (q r))
    (legEdge : Fin (q r) → Edge qLocal)
    (hleg : ∀ j, Θ.target (legEdge j) = Sum.inr j)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) :
    (fun e ↦ lab (Θ.vertexSplitOldEdge legEdge hleg q r rfl e)) =
      (vertexSplitOldLabelEquiv q r rfl d).symm
        ((vertexSplitLabelEquiv q qLocal r d lab).1,
          externalLabels legEdge (vertexSplitLabelEquiv q qLocal r d lab).2) := by
  apply (vertexSplitOldLabelEquiv q r rfl d).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext e
    simp only [vertexSplitOldLabelEquiv_outside, vertexSplitOldEdge_outside]
    rfl
  · funext j
    simp only [vertexSplitOldLabelEquiv_root, vertexSplitOldEdge_root]
    rfl

end SplitLabels

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
