import EnvelopingIsomorphism.Deformation.GeneralGraphProfilePermutations

/-! Single exceptional arities and genuine outgoing graph permutations. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {n m d : ℕ} {R : Type*} [CommRing R]

/-- One distinguished arity, with bivectors at all remaining internal vertices. -/
def oneExceptionalArity (a : ℕ) (r : Fin n) (v : Fin n) : ℕ := if v = r then a else 2

@[simp] theorem oneExceptionalArity_root (a : ℕ) (r : Fin n) : oneExceptionalArity a r r = a := by
  simp [oneExceptionalArity]

theorem oneExceptionalArity_other (a : ℕ) (r v : Fin n) (hv : v ≠ r) :
    oneExceptionalArity a r v = 2 := by simp [oneExceptionalArity, hv]

/-- Arbitrary internal relabelling moves the unique exceptional vertex to its image. -/
theorem profileArity_oneExceptional (a : ℕ) (r : Fin n) (σ : Equiv.Perm (Fin n)) :
    profileArity (oneExceptionalArity a r) σ = oneExceptionalArity a (σ r) := by
  funext v
  simp only [profileArity, oneExceptionalArity, Equiv.symm_apply_eq]

/-- Actual dependent tensors: a vector or higher tensor at the distinguished vertex,
and the same bivector tensor at every other vertex. -/
def oneExceptionalTensors {a : ℕ} (r : Fin n) (π : Tensor 2 d R) (ξ : Tensor a d R)
    (v : Fin n) : Tensor (oneExceptionalArity a r v) d R :=
  if h : v = r then by simpa [oneExceptionalArity, h] using ξ
  else by simpa [oneExceptionalArity, h] using π

theorem oneExceptionalTensors_root_heq {a : ℕ} (r : Fin n) (π : Tensor 2 d R) (ξ : Tensor a d R) :
    HEq (oneExceptionalTensors r π ξ r) ξ := by
  simp [oneExceptionalTensors]

theorem oneExceptionalTensors_other_heq {a : ℕ} (r : Fin n) (π : Tensor 2 d R) (ξ : Tensor a d R)
    (v : Fin n) (hv : v ≠ r) : HEq (oneExceptionalTensors r π ξ v) π := by
  simp [oneExceptionalTensors, hv]

/-- The transported exceptional tensor is exactly the original tensor, at its new vertex. -/
theorem profileTensors_oneExceptional_root_heq {a : ℕ} (r : Fin n) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (ξ : Tensor a d R) :
    HEq (profileTensors (oneExceptionalArity a r) σ (oneExceptionalTensors r π ξ) (σ r)) ξ := by
  exact (congr_arg_heq (oneExceptionalTensors r π ξ) (σ.symm_apply_apply r)).trans
    (oneExceptionalTensors_root_heq r π ξ)

theorem profileTensors_oneExceptional_other_heq {a : ℕ} (r : Fin n) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (ξ : Tensor a d R) (v : Fin n) (hv : v ≠ r) :
    HEq (profileTensors (oneExceptionalArity a r) σ (oneExceptionalTensors r π ξ) (σ v)) π := by
  exact (congr_arg_heq (oneExceptionalTensors r π ξ) (σ.symm_apply_apply v)).trans
    (oneExceptionalTensors_other_heq r π ξ v hv)

private theorem transportTensors_apply_heq {q q' : Fin n → ℕ} (h : q = q')
    (T : (v : Fin n) → Tensor (q v) d R) (v : Fin n) :
    HEq ((h ▸ T : (w : Fin n) → Tensor (q' w) d R) v) (T v) := by
  subst q'
  rfl

/-- Transport identifies the entire tensor family with the canonical new placement. -/
theorem profileTensors_oneExceptional {a : ℕ} (r : Fin n) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (ξ : Tensor a d R) :
    (profileArity_oneExceptional a r σ ▸
      profileTensors (oneExceptionalArity a r) σ (oneExceptionalTensors r π ξ) :
        (v : Fin n) → Tensor (oneExceptionalArity a (σ r) v) d R) =
      oneExceptionalTensors (σ r) π ξ := by
  funext v
  apply eq_of_heq
  refine (transportTensors_apply_heq (profileArity_oneExceptional a r σ) _ v).trans ?_
  by_cases hv : v = σ r
  · subst v
    exact (profileTensors_oneExceptional_root_heq r σ π ξ).trans
      (oneExceptionalTensors_root_heq (σ r) π ξ).symm
  · have hv' : σ.symm v ≠ r := by
      intro he
      apply hv
      simpa using congrArg σ he
    exact (oneExceptionalTensors_other_heq r π ξ (σ.symm v) hv').trans
      (oneExceptionalTensors_other_heq (σ r) π ξ v hv).symm

namespace Graph

/-- Identify graph spaces along a proved equality of dependent arity profiles. -/
def castProfileEquiv {q q' : Fin n → ℕ} (h : q = q') (m : ℕ) : Graph q m ≃ Graph q' m :=
  Equiv.cast (congrArg (fun p ↦ Graph p m) h)

theorem cochainOperator_castProfile {q q' : Fin n → ℕ} (h : q = q')
    (Γ : Graph q m) (T : (v : Fin n) → Tensor (q v) d R) :
    (castProfileEquiv h m Γ).cochainOperator (h ▸ T) = Γ.cochainOperator T := by
  subst q'
  rfl

/-- Relabelling gives a bijection between the two canonical exceptional placements. -/
def oneExceptionalGraphEquiv (a : ℕ) (r : Fin n) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    Graph (oneExceptionalArity a r) m ≃ Graph (oneExceptionalArity a (σ r)) m :=
  (profileGraphEquiv (oneExceptionalArity a r) m σ).trans
    (castProfileEquiv (profileArity_oneExceptional a r σ) m)

/-- The canonical tensor families at the old and new placements give the same cochain. -/
theorem cochainOperator_oneExceptionalGraphEquiv {a : ℕ} (r : Fin n)
    (σ : Equiv.Perm (Fin n)) (Γ : Graph (oneExceptionalArity a r) m)
    (π : Tensor 2 d R) (ξ : Tensor a d R) :
    (oneExceptionalGraphEquiv a r σ m Γ).cochainOperator (oneExceptionalTensors (σ r) π ξ) =
      Γ.cochainOperator (oneExceptionalTensors r π ξ) := by
  rw [← profileTensors_oneExceptional r σ π ξ]
  exact (cochainOperator_castProfile (profileArity_oneExceptional a r σ)
    (Γ.permuteProfile σ) _).trans (cochainOperator_permuteProfile Γ σ _)


/-- The dependent relabelling agrees with the already established uniform construction. -/
theorem permuteProfile_uniform {a : ℕ} (Γ : Graph (fun _ : Fin n ↦ a) m)
    (σ : Equiv.Perm (Fin n)) : Γ.permuteProfile σ = Γ.permuteInternal σ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v, j⟩
  rfl

theorem cochainOperator_permuteProfile_oneExceptional {a : ℕ} (r : Fin n)
    (Γ : Graph (oneExceptionalArity a r) m) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (ξ : Tensor a d R) (f : Fin m → Polynomial d R) :
    (Γ.permuteProfile σ).cochainOperator
        (profileTensors (oneExceptionalArity a r) σ (oneExceptionalTensors r π ξ)) f =
      Γ.cochainOperator (oneExceptionalTensors r π ξ) f :=
  cochainOperator_permuteProfile_apply Γ σ _ f

/-- One arity-one vector vertex may be placed at any internal index. -/
theorem cochainOperator_permuteProfile_vector (r : Fin n)
    (Γ : Graph (oneExceptionalArity 1 r) m) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (X : Tensor 1 d R) (f : Fin m → Polynomial d R) :
    (Γ.permuteProfile σ).cochainOperator
        (profileTensors (oneExceptionalArity 1 r) σ (oneExceptionalTensors r π X)) f =
      Γ.cochainOperator (oneExceptionalTensors r π X) f :=
  cochainOperator_permuteProfile_oneExceptional r Γ σ π X f

/-- One arity-three curvature vertex obeys the same genuine covariance. -/
theorem cochainOperator_permuteProfile_curvature (r : Fin n)
    (Γ : Graph (oneExceptionalArity 3 r) m) (σ : Equiv.Perm (Fin n))
    (π : Tensor 2 d R) (C : Tensor 3 d R) (f : Fin m → Polynomial d R) :
    (Γ.permuteProfile σ).cochainOperator
        (profileTensors (oneExceptionalArity 3 r) σ (oneExceptionalTensors r π C)) f =
      Γ.cochainOperator (oneExceptionalTensors r π C) f :=
  cochainOperator_permuteProfile_oneExceptional r Γ σ π C f

/-- Reordering outgoing slots is an actual permutation of admissible graphs with any profile. -/
def outgoingGraphEquiv (q : Fin n → ℕ) (m : ℕ)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) : Equiv.Perm (Graph q m) where
  toFun Γ := Γ.permuteOutgoing τ
  invFun Γ := Γ.permuteOutgoing (fun v ↦ (τ v).symm)
  left_inv Γ := by
    apply Graph.ext
    funext e
    rcases e with ⟨v, j⟩
    change Γ.target ⟨v, τ v ((τ v).symm j)⟩ = Γ.target ⟨v, j⟩
    rw [Equiv.apply_symm_apply]
  right_inv Γ := by
    apply Graph.ext
    funext e
    rcases e with ⟨v, j⟩
    change Γ.target ⟨v, (τ v).symm (τ v j)⟩ = Γ.target ⟨v, j⟩
    rw [Equiv.symm_apply_apply]

@[simp] theorem outgoingGraphEquiv_apply (q : Fin n → ℕ) (m : ℕ)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (Γ : Graph q m) :
    outgoingGraphEquiv q m τ Γ = Γ.permuteOutgoing τ := rfl

@[simp] theorem outgoingGraphEquiv_symm_apply (q : Fin n → ℕ) (m : ℕ)
    (τ : (v : Fin n) → Equiv.Perm (Fin (q v))) (Γ : Graph q m) :
    (outgoingGraphEquiv q m τ).symm Γ = Γ.permuteOutgoing (fun v ↦ (τ v).symm) := rfl

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
