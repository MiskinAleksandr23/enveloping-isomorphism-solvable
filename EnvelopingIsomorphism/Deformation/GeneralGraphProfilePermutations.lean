import EnvelopingIsomorphism.Deformation.GeneralGraphInternalPermutations
import EnvelopingIsomorphism.Deformation.GeneralGraphPermutations
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphEdgeOrder

/-! Internal relabelling with genuinely dependent outgoing arities and coefficient tensors. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open scoped BigOperators

variable {n m d : ℕ}

/-- Transport the entire arity profile along an internal-vertex permutation. -/
def profileArity (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (v : Fin n) : ℕ := q (σ.symm v)

theorem profileArity_sum (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    (∑ v, profileArity q σ v) = ∑ v, q v := Equiv.sum_comp σ.symm q

/-- The dependent edge transport uses the native sigma equivalence, retaining every slot. -/
def profileEdgeEquiv (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    Edge q ≃ Edge (profileArity q σ) :=
  (Equiv.sigmaCongrLeft (β := fun v ↦ Fin (q v)) σ.symm).symm

@[simp] theorem profileEdgeEquiv_symm_apply (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n) (j : Fin (profileArity q σ v)) :
    (profileEdgeEquiv q σ).symm ⟨v, j⟩ = ⟨σ.symm v, j⟩ := rfl

@[simp] theorem profileEdgeEquiv_source (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (e : Edge q) :
    (profileEdgeEquiv q σ e).1 = σ e.1 := rfl

@[simp] theorem profileEdgeEquiv_slot_val (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (e : Edge q) :
    (profileEdgeEquiv q σ e).2.val = e.2.val := by
  obtain ⟨e, rfl⟩ := (profileEdgeEquiv q σ).symm.surjective e
  rw [Equiv.apply_symm_apply]
  rfl

/-- Exact row permutation in the canonical vertex-major outgoing-edge order.
The final cardinality cast changes no underlying natural-number index. -/
def profileRowPerm (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (∑ v, q v)) :=
  (Kontsevich.vertexMajorEdgeEquiv q).trans ((profileEdgeEquiv q σ).trans
    ((Kontsevich.vertexMajorEdgeEquiv (profileArity q σ)).symm.trans
      (finCongr (profileArity_sum q σ))))

theorem profileRowPerm_edge_val (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (e : Edge q) :
    (profileRowPerm q σ ((Kontsevich.vertexMajorEdgeEquiv q).symm e)).val =
      Kontsevich.edgePrefix (profileArity q σ) (σ e.1) + e.2.val := by
  simp only [profileRowPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  change ((Kontsevich.vertexMajorEdgeEquiv (profileArity q σ)).symm (profileEdgeEquiv q σ e)).val = _
  have h := Kontsevich.vertexMajorEdgeEquiv_symm_val (profileArity q σ)
    (profileEdgeEquiv q σ e).1 (profileEdgeEquiv q σ e).2
  rw [Sigma.eta, profileEdgeEquiv_slot_val, profileEdgeEquiv_source] at h
  exact h

/-- Actual new labels read as labels on all original edges. -/
def profileLabelEquiv (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (d : ℕ) :
    (Edge (profileArity q σ) → Fin d) ≃ (Edge q → Fin d) where
  toFun lab e := lab (profileEdgeEquiv q σ e)
  invFun lab e := lab ((profileEdgeEquiv q σ).symm e)
  left_inv lab := by funext e; simp
  right_inv lab := by funext e; simp

@[simp] theorem profileLabelEquiv_symm_source (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (lab : Edge (profileArity q σ) → Fin d) (v : Fin n) (j : Fin (profileArity q σ v)) :
    profileLabelEquiv q σ d lab ⟨σ.symm v, j⟩ = lab ⟨v, j⟩ := by
  change lab (profileEdgeEquiv q σ ((profileEdgeEquiv q σ).symm ⟨v, j⟩)) = _
  rw [Equiv.apply_symm_apply]

/-- The transported tensor at a new vertex is the original tensor at its inverse image. -/
def profileTensors {R : Type*} [CommRing R] (q : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (T : (v : Fin n) → Tensor (q v) d R) :
    (v : Fin n) → Tensor (profileArity q σ v) d R := fun v ↦ T (σ.symm v)

namespace Graph

variable {q : Fin n → ℕ} (Γ : Graph q m) (σ : Equiv.Perm (Fin n))

/-- Genuine pushforward of a graph, with its dependent arity profile transported. -/
def permuteProfile : Graph (profileArity q σ) m where
  target e := internalVertexPerm m σ (Γ.target ((profileEdgeEquiv q σ).symm e))
  noLoops v j := by
    intro h
    apply Γ.noLoops (σ.symm v) j
    apply (internalVertexPerm m σ).injective
    simpa using h
  distinctTargets v i j h := Γ.distinctTargets (σ.symm v) ((internalVertexPerm m σ).injective h)

@[simp] theorem permuteProfile_target (e : Edge q) :
    (Γ.permuteProfile σ).target (profileEdgeEquiv q σ e) =
      internalVertexPerm m σ (Γ.target e) := by
  simp [permuteProfile]

/-- Pull a relabelled graph back along the actual dependent edge equivalence. -/
def unpermuteProfile (Δ : Graph (profileArity q σ) m) : Graph q m where
  target e := (internalVertexPerm m σ).symm (Δ.target (profileEdgeEquiv q σ e))
  noLoops v j := by
    intro h
    apply Δ.noLoops (profileEdgeEquiv q σ ⟨v, j⟩).1 (profileEdgeEquiv q σ ⟨v, j⟩).2
    rw [Sigma.eta]
    have ht := congrArg (internalVertexPerm m σ) h
    simpa only [Equiv.apply_symm_apply, internalVertexPerm_inl, profileEdgeEquiv_source] using ht
  distinctTargets v i j h := by
    have ht := congrArg (internalVertexPerm m σ) h
    simp only [Equiv.apply_symm_apply] at ht
    have hs := Δ.distinctTargets (σ v) ht
    apply Fin.ext
    calc
      i.val = (profileEdgeEquiv q σ ⟨v, i⟩).2.val :=
        (profileEdgeEquiv_slot_val q σ ⟨v, i⟩).symm
      _ = (profileEdgeEquiv q σ ⟨v, j⟩).2.val := congrArg Fin.val hs
      _ = j.val := profileEdgeEquiv_slot_val q σ ⟨v, j⟩

@[simp] theorem unpermuteProfile_permuteProfile :
    unpermuteProfile σ (Γ.permuteProfile σ) = Γ := by
  apply Graph.ext
  funext e
  simp [unpermuteProfile]

@[simp] theorem permuteProfile_unpermuteProfile (Δ : Graph (profileArity q σ) m) :
    (unpermuteProfile σ Δ).permuteProfile σ = Δ := by
  apply Graph.ext
  funext e
  simp [permuteProfile, unpermuteProfile]

/-- Dependent internal relabelling is a bijection of the actual admissible graph sets. -/
def profileGraphEquiv (q : Fin n → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin n)) :
    Graph q m ≃ Graph (profileArity q σ) m where
  toFun Γ := Γ.permuteProfile σ
  invFun := unpermuteProfile σ
  left_inv Γ := unpermuteProfile_permuteProfile Γ σ
  right_inv Δ := permuteProfile_unpermuteProfile σ Δ

@[simp] theorem profileGraphEquiv_apply (Γ : Graph q m) :
    profileGraphEquiv q m σ Γ = Γ.permuteProfile σ := rfl

theorem incoming_permuteProfile_perm (v : Vertex n m) :
    (((Γ.permuteProfile σ).incoming (internalVertexPerm m σ v)).toList.map
      (profileEdgeEquiv q σ).symm).Perm (Γ.incoming v).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map (profileEdgeEquiv q σ).symm.injective)
    (Finset.nodup_toList _)).mpr
  intro e
  simp only [List.mem_map, Finset.mem_toList, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, he⟩
    have ht := (internalVertexPerm m σ).injective hf
    change Γ.target ((profileEdgeEquiv q σ).symm f) = v at ht
    exact he ▸ ht
  · intro he
    refine ⟨profileEdgeEquiv q σ e, ?_, by simp⟩
    rw [permuteProfile_target, he]

variable {R : Type*} [CommRing R]

theorem vertexDerivative_permuteProfile
    (lab : Edge (profileArity q σ) → Fin d) (v : Vertex n m) :
    (Γ.permuteProfile σ).vertexDerivative (R := R) lab (internalVertexPerm m σ v) =
      Γ.vertexDerivative (profileLabelEquiv q σ d lab) v := by
  apply iteratedPDeriv_perm
  have h := (incoming_permuteProfile_perm Γ σ v).map (profileLabelEquiv q σ d lab)
  rw [List.map_map] at h
  have hc : (profileLabelEquiv q σ d lab) ∘ (profileEdgeEquiv q σ).symm = lab := by
    funext e
    change lab (profileEdgeEquiv q σ ((profileEdgeEquiv q σ).symm e)) = lab e
    rw [Equiv.apply_symm_apply]
  rwa [hc] at h

theorem vertexDerivative_permuteProfile_new
    (lab : Edge (profileArity q σ) → Fin d) (v : Vertex n m) :
    (Γ.permuteProfile σ).vertexDerivative (R := R) lab v =
      Γ.vertexDerivative (profileLabelEquiv q σ d lab) ((internalVertexPerm m σ).symm v) := by
  simpa using vertexDerivative_permuteProfile Γ σ lab ((internalVertexPerm m σ).symm v)

/-- Actual labelled covariance, including every dependent tensor argument. -/
theorem labelledOperator_permuteProfile (lab : Edge (profileArity q σ) → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    ((Γ.permuteProfile σ).labelledOperator lab).currySum (profileTensors q σ T) f =
      (Γ.labelledOperator (profileLabelEquiv q σ d lab)).currySum T f := by
  rw [MultilinearMap.currySum_apply, MultilinearMap.currySum_apply,
    labelledOperator_apply, labelledOperator_apply]
  apply Fintype.prod_equiv (internalVertexPerm m σ).symm
  intro v
  rw [vertexDerivative_permuteProfile_new]
  cases v with
  | inl v =>
      apply congrArg (Γ.vertexDerivative (profileLabelEquiv q σ d lab)
        (Sum.inl (σ.symm v)))
      change T (σ.symm v) (fun j ↦ lab ⟨v, j⟩) =
        T (σ.symm v) (fun j ↦ profileLabelEquiv q σ d lab ⟨σ.symm v, j⟩)
      simp only [profileLabelEquiv_symm_source]
  | inr j => rfl

/-- Relabelling the graph and its entire tensor profile preserves its genuine cochain. -/
theorem cochainOperator_permuteProfile (T : (v : Fin n) → Tensor (q v) d R) :
    (Γ.permuteProfile σ).cochainOperator (profileTensors q σ T) = Γ.cochainOperator T := by
  apply MultilinearMap.ext
  intro f
  classical
  change ((∑ lab, (Γ.permuteProfile σ).labelledOperator lab).currySum (profileTensors q σ T)) f =
    ((∑ lab, Γ.labelledOperator lab).currySum T) f
  simp only [MultilinearMap.currySum_apply, sum_apply]
  apply Fintype.sum_equiv (profileLabelEquiv q σ d)
  intro lab
  exact labelledOperator_permuteProfile Γ σ lab T f

theorem cochainOperator_permuteProfile_apply (T : (v : Fin n) → Tensor (q v) d R)
    (f : Fin m → Polynomial d R) :
    (Γ.permuteProfile σ).cochainOperator (profileTensors q σ T) f = Γ.cochainOperator T f := by
  rw [cochainOperator_permuteProfile]

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
