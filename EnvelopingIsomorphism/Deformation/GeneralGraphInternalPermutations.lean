import EnvelopingIsomorphism.Deformation.GeneralGraphOperators

/-! Internal-vertex relabelling of genuine graph operators with a uniform outgoing arity. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open scoped BigOperators

variable {n m d a : ℕ}

/-- Relabel internal sources while retaining the order of all outgoing slots. -/
def internalEdgePerm (a : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Edge (fun _ : Fin n ↦ a)) where
  toFun e := ⟨σ e.1, e.2⟩
  invFun e := ⟨σ.symm e.1, e.2⟩
  left_inv e := by rcases e with ⟨v, j⟩; simp
  right_inv e := by rcases e with ⟨v, j⟩; simp

@[simp] theorem internalEdgePerm_apply (σ : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin a) :
    internalEdgePerm a σ ⟨v, j⟩ = ⟨σ v, j⟩ := rfl

@[simp] theorem internalEdgePerm_symm_apply (σ : Equiv.Perm (Fin n)) (v : Fin n) (j : Fin a) :
    (internalEdgePerm a σ).symm ⟨v, j⟩ = ⟨σ.symm v, j⟩ := rfl

/-- External vertices are fixed by the relabelling. -/
def internalVertexPerm (m : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Vertex n m) :=
  Equiv.sumCongr σ (Equiv.refl _)

@[simp] theorem internalVertexPerm_inl (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    internalVertexPerm m σ (Sum.inl v) = Sum.inl (σ v) := rfl

@[simp] theorem internalVertexPerm_inr (σ : Equiv.Perm (Fin n)) (j : Fin m) :
    internalVertexPerm m σ (Sum.inr j) = Sum.inr j := rfl

/-- Pull the labels of the relabelled graph back to the original edges. -/
def internalLabelEquiv (a d : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Edge (fun _ : Fin n ↦ a) → Fin d) ≃ (Edge (fun _ : Fin n ↦ a) → Fin d) where
  toFun lab e := lab (internalEdgePerm a σ e)
  invFun lab e := lab ((internalEdgePerm a σ).symm e)
  left_inv lab := by funext e; simp
  right_inv lab := by funext e; simp

@[simp] theorem internalLabelEquiv_apply (σ : Equiv.Perm (Fin n))
    (lab : Edge (fun _ : Fin n ↦ a) → Fin d) (v : Fin n) (j : Fin a) :
    internalLabelEquiv a d σ lab ⟨v, j⟩ = lab ⟨σ v, j⟩ := rfl

namespace Graph

variable (Γ : Graph (fun _ : Fin n ↦ a) m) (σ : Equiv.Perm (Fin n))

/-- Push forward the internal vertices of an admissible graph. -/
def permuteInternal : Graph (fun _ : Fin n ↦ a) m where
  target e := internalVertexPerm m σ (Γ.target ((internalEdgePerm a σ).symm e))
  noLoops v j := by
    intro h
    apply Γ.noLoops (σ.symm v) j
    apply (internalVertexPerm m σ).injective
    simpa using h
  distinctTargets v i j h := Γ.distinctTargets (σ.symm v) ((internalVertexPerm m σ).injective h)

@[simp] theorem permuteInternal_target (e : Edge (fun _ : Fin n ↦ a)) :
    (Γ.permuteInternal σ).target (internalEdgePerm a σ e) =
      internalVertexPerm m σ (Γ.target e) := by
  simp [permuteInternal]

@[simp] theorem permuteInternal_refl : Γ.permuteInternal (Equiv.refl _) = Γ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v, j⟩
  change internalVertexPerm m (Equiv.refl _) (Γ.target ⟨v, j⟩) = Γ.target ⟨v, j⟩
  cases Γ.target ⟨v, j⟩ <;> rfl

theorem permuteInternal_trans (τ : Equiv.Perm (Fin n)) :
    (Γ.permuteInternal τ).permuteInternal σ = Γ.permuteInternal (τ.trans σ) := by
  apply Graph.ext
  funext e
  rcases e with ⟨v, j⟩
  change internalVertexPerm m σ
    (internalVertexPerm m τ (Γ.target ⟨τ.symm (σ.symm v), j⟩)) =
    internalVertexPerm m (τ.trans σ) (Γ.target ⟨τ.symm (σ.symm v), j⟩)
  cases Γ.target ⟨τ.symm (σ.symm v), j⟩ <;> rfl

/-- The pushforward is an actual permutation of admissible graphs. -/
def permuteInternalEquiv (a m : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Graph (fun _ : Fin n ↦ a) m) where
  toFun Γ := Γ.permuteInternal σ
  invFun Γ := Γ.permuteInternal σ.symm
  left_inv Γ := by
    change (Γ.permuteInternal σ).permuteInternal σ.symm = Γ
    rw [permuteInternal_trans]
    simp
  right_inv Γ := by
    change (Γ.permuteInternal σ.symm).permuteInternal σ = Γ
    rw [permuteInternal_trans]
    simp

theorem incoming_permuteInternal_perm (v : Vertex n m) :
    (((Γ.permuteInternal σ).incoming (internalVertexPerm m σ v)).toList.map
      (internalEdgePerm a σ).symm).Perm (Γ.incoming v).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map (internalEdgePerm a σ).symm.injective)
    (Finset.nodup_toList _)).mpr
  intro e
  simp only [List.mem_map, Finset.mem_toList, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, he⟩
    have ht := (internalVertexPerm m σ).injective hf
    change Γ.target ((internalEdgePerm a σ).symm f) = v at ht
    exact he ▸ ht
  · intro he
    refine ⟨internalEdgePerm a σ e, ?_, by simp⟩
    rw [permuteInternal_target, he]

variable {R : Type*} [CommRing R]

/-- Incoming derivatives are unchanged after pulling the actual edge labels back. -/
theorem vertexDerivative_permuteInternal
    (lab : Edge (fun _ : Fin n ↦ a) → Fin d) (v : Vertex n m) :
    (Γ.permuteInternal σ).vertexDerivative (R := R) lab (internalVertexPerm m σ v) =
      Γ.vertexDerivative (internalLabelEquiv a d σ lab) v := by
  apply iteratedPDeriv_perm
  have h := (incoming_permuteInternal_perm Γ σ v).map (internalLabelEquiv a d σ lab)
  rw [List.map_map] at h
  have hc : (internalLabelEquiv a d σ lab) ∘ (internalEdgePerm a σ).symm = lab := by
    funext e
    change lab (internalEdgePerm a σ ((internalEdgePerm a σ).symm e)) = lab e
    rw [Equiv.apply_symm_apply]
  rwa [hc] at h

/-- Exact labelled covariance, allowing different tensors at different vertices. -/
theorem labelledOperator_permuteInternal
    (lab : Edge (fun _ : Fin n ↦ a) → Fin d)
    (T : Fin n → Tensor a d R) (f : Fin m → Polynomial d R) :
    ((Γ.permuteInternal σ).labelledOperator lab).currySum T f =
      (Γ.labelledOperator (internalLabelEquiv a d σ lab)).currySum (fun v ↦ T (σ v)) f := by
  rw [MultilinearMap.currySum_apply, MultilinearMap.currySum_apply,
    labelledOperator_apply, labelledOperator_apply]
  let F : Vertex n m → Polynomial d R := fun v ↦
    (Γ.permuteInternal σ).vertexDerivative lab v
      (vertexEvaluation lab v (Sum.rec T f v))
  change (∏ v, F v) = _
  calc
    (∏ v, F v) = ∏ v, F (internalVertexPerm m σ v) :=
      (Equiv.prod_comp (internalVertexPerm m σ) F).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v hv
      dsimp only [F]
      rw [vertexDerivative_permuteInternal]
      cases v with
      | inl v => rfl
      | inr j => rfl

/-- The actual graph cochain is covariant under arbitrary internal relabelling. -/
theorem cochainOperator_permuteInternal_covariance (T : Fin n → Tensor a d R) :
    (Γ.permuteInternal σ).cochainOperator T = Γ.cochainOperator (fun v ↦ T (σ v)) := by
  apply MultilinearMap.ext
  intro f
  classical
  change ((∑ lab, (Γ.permuteInternal σ).labelledOperator lab).currySum T) f =
    ((∑ lab, Γ.labelledOperator lab).currySum (fun v ↦ T (σ v))) f
  simp only [MultilinearMap.currySum_apply, sum_apply]
  apply Fintype.sum_equiv (internalLabelEquiv a d σ)
  intro lab
  exact labelledOperator_permuteInternal Γ σ lab T f

/-- Identical vertex tensors remove the tensor permutation, with no sign or weight premise. -/
theorem cochainOperator_permuteInternal_identical (π : Tensor a d R) :
    (Γ.permuteInternal σ).cochainOperator (fun _ ↦ π) = Γ.cochainOperator (fun _ ↦ π) := by
  rw [cochainOperator_permuteInternal_covariance]

theorem cochainOperator_permuteInternal_identical_apply (π : Tensor a d R)
    (f : Fin m → Polynomial d R) :
    (Γ.permuteInternal σ).cochainOperator (fun _ ↦ π) f =
      Γ.cochainOperator (fun _ ↦ π) f := by
  rw [cochainOperator_permuteInternal_identical]

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
