import EnvelopingIsomorphism.Deformation.GraphBinaryGraftFibres
import EnvelopingIsomorphism.Deformation.GeneralGraphInternalPermutations

/-! Independent relabelling of the two genuine binary factors of a graft. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryGraftRelabelling
open scoped Classical
open KontsevichGraph.General UniformBinaryGraphs GraphWeightedInsertion
variable {a b : ℕ}

def blockPerm (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) : Equiv.Perm (Fin (a+b)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ τ).trans finSumFinEquiv)

@[simp] theorem blockPerm_outer (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) (v : Fin a) :
    blockPerm σ τ (Fin.castAdd b v) = Fin.castAdd b (σ v) := by simp [blockPerm]

@[simp] theorem blockPerm_inner (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) (v : Fin b) :
    blockPerm σ τ (Fin.natAdd a v) = Fin.natAdd a (τ v) := by simp [blockPerm]

theorem uniformGraft_target_outer (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (r : Fin 2) (χ : GraftChoices Γ r) (v : Fin a) (j : Fin 2) :
    (uniformGraft Γ Δ r χ).target ⟨Fin.castAdd b v, j⟩ = Γ.graftOuterTarget r χ ⟨v,j⟩ := by
  rw [uniformGraft_target]
  have he : (⟨Fin.castAdd b v,
      Fin.cast (congrFun graftArity_two (Fin.castAdd b v)).symm j⟩ :
      Edge (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2))) =
      graftOuterEdge (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2) ⟨v,j⟩ := by
    rw [graftOuterEdge_mk]
  rw [he, Graph.graft_target_outer]

theorem uniformGraft_target_inner (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (r : Fin 2) (χ : GraftChoices Γ r) (v : Fin b) (j : Fin 2) :
    (uniformGraft Γ Δ r χ).target ⟨Fin.natAdd a v, j⟩ = graftInnerVertex r (Δ.target ⟨v,j⟩) := by
  rw [uniformGraft_target]
  have he : (⟨Fin.natAdd a v,
      Fin.cast (congrFun graftArity_two (Fin.natAdd a v)).symm j⟩ :
      Edge (graftArity (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2))) =
      graftInnerEdge (fun _ : Fin a ↦ 2) (fun _ : Fin b ↦ 2) ⟨v,j⟩ := by
    rw [graftInnerEdge_mk]
  rw [he, Graph.graft_target_inner]

def incomingEquiv (Γ : BinaryGraph a 2) (r : Fin 2) (σ : Equiv.Perm (Fin a)) :
    {e : Edge (fun _ : Fin a ↦ 2) // Γ.target e = Sum.inr r} ≃
      {e : Edge (fun _ : Fin a ↦ 2) // (Γ.permuteInternal σ).target e = Sum.inr r} :=
  Equiv.subtypeEquiv (internalEdgePerm 2 σ) (by
    intro e
    rw [Graph.permuteInternal_target]
    change Γ.target e = Sum.inr r ↔ Sum.map σ id (Γ.target e) = Sum.inr r
    cases Γ.target e <;> simp)

def relabelChoices (Γ : BinaryGraph a 2) (r : Fin 2)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) (χ : GraftChoices (b := b) Γ r) :
    GraftChoices (b := b) (Γ.permuteInternal σ) r :=
  fun e ↦ internalVertexPerm 2 τ (χ ((incomingEquiv Γ r σ).symm e))

@[simp] theorem blockPerm_innerVertex (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (r : Fin 2) (v : Vertex b 2) :
    internalVertexPerm 3 (blockPerm σ τ) (graftInnerVertex r v) =
      graftInnerVertex r (internalVertexPerm 2 τ v) := by
  cases v <;> simp [graftInnerVertex, internalVertexPerm]

@[simp] theorem blockPerm_outerVertex (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (r : Fin 2) (v : Vertex a 2) :
    internalVertexPerm 3 (blockPerm σ τ) (graftOuterVertex (b := b) (l := 1) r v) =
      graftOuterVertex (b := b) (l := 1) r (internalVertexPerm 2 σ v) := by
  cases v <;> simp [graftOuterVertex, internalVertexPerm]

/-- Every incoming-arrow assignment transforms with its original edge, and
all targets transform with the correct factor's internal permutation. -/
theorem uniformGraft_permuteInternal (Γ : BinaryGraph a 2) (Δ : BinaryGraph b 2)
    (r : Fin 2) (χ : GraftChoices Γ r)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    (uniformGraft Γ Δ r χ).permuteInternal (blockPerm σ τ) =
      uniformGraft (Γ.permuteInternal σ) (Δ.permuteInternal τ) r
        (relabelChoices Γ r σ τ χ) := by
  apply Graph.ext
  funext e
  obtain ⟨e, rfl⟩ := (internalEdgePerm 2 (blockPerm σ τ)).surjective e
  rcases e with ⟨v,j⟩
  rw [Graph.permuteInternal_target]
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v
  · simp only [internalEdgePerm_apply, blockPerm_outer, uniformGraft_target_outer]
    have ht : (Γ.permuteInternal σ).target ⟨σ v,j⟩ =
        internalVertexPerm 2 σ (Γ.target ⟨v,j⟩) := Graph.permuteInternal_target Γ σ ⟨v,j⟩
    have hh : internalVertexPerm 2 σ (Γ.target ⟨v,j⟩) = Sum.inr r ↔
        Γ.target ⟨v,j⟩ = Sum.inr r := by
      cases Γ.target ⟨v,j⟩ <;> simp [internalVertexPerm]
    have hh' : (Γ.permuteInternal σ).target ⟨σ v,j⟩ = Sum.inr r ↔
        Γ.target ⟨v,j⟩ = Sum.inr r := by rw [ht, hh]
    unfold Graph.graftOuterTarget
    by_cases h : Γ.target ⟨v,j⟩ = Sum.inr r
    · simp only [dif_pos h, dif_pos (hh'.mpr h), blockPerm_innerVertex]
      congr 1
      simp [relabelChoices, incomingEquiv]
    · rw [dif_neg h, dif_neg (mt hh'.mp h), ht, blockPerm_outerVertex]
  · simp only [internalEdgePerm_apply, blockPerm_inner, uniformGraft_target_inner,
      blockPerm_innerVertex]
    exact congrArg (graftInnerVertex r) (Graph.permuteInternal_target Δ τ ⟨v,j⟩).symm

@[simp] theorem blockPerm_symm (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    (blockPerm σ τ).symm = blockPerm σ.symm τ.symm := rfl

def relabelData (r : Fin 2) (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (D : GraftIndex a b r) : GraftIndex a b r :=
  ⟨D.1.permuteInternal σ, D.2.1.permuteInternal τ, relabelChoices D.1 r σ τ D.2.2⟩

theorem graftGraph_relabelData (r : Fin 2) (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (D : GraftIndex a b r) :
    graftGraph r (relabelData r σ τ D) = (graftGraph r D).permuteInternal (blockPerm σ τ) :=
  (uniformGraft_permuteInternal D.1 D.2.1 r D.2.2 σ τ).symm

/-- Independent relabelling is a bijection on actual graft data, proved using
injectivity of the reconstructed graph rather than dependent choice casts. -/
def relabelDataEquiv (r : Fin 2) (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm (GraftIndex a b r) where
  toFun := relabelData r σ τ
  invFun := relabelData r σ.symm τ.symm
  left_inv D := by
    apply GraphBinaryGraftFibres.graftGraph_injective r
    rw [graftGraph_relabelData, graftGraph_relabelData, Graph.permuteInternal_trans,
      ← blockPerm_symm, Equiv.self_trans_symm, Graph.permuteInternal_refl]
  right_inv D := by
    apply GraphBinaryGraftFibres.graftGraph_injective r
    rw [graftGraph_relabelData, graftGraph_relabelData, Graph.permuteInternal_trans,
      ← blockPerm_symm, Equiv.symm_trans_self, Graph.permuteInternal_refl]

open scoped BigOperators

/-- The fixed-block graft profile is invariant under independent internal
factor labels when the two actual weight tables are invariant. -/
theorem graftProfile_blockPerm {k : Type*} [CommRing k]
    (r : Fin 2) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ (Γ : BinaryGraph a 2) (σ : Equiv.Perm (Fin a)), w (Γ.permuteInternal σ) = w Γ)
    (hv : ∀ (Δ : BinaryGraph b 2) (τ : Equiv.Perm (Fin b)), v (Δ.permuteInternal τ) = v Δ)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) (H : BinaryGraph (a+b) 3) :
    graftProfile r w v (H.permuteInternal (blockPerm σ τ)) = graftProfile r w v H := by
  unfold graftProfile GraphCoefficientProfiles.pushforward
  rw [← Equiv.sum_comp (relabelDataEquiv r σ τ)]
  apply Finset.sum_congr rfl
  intro D hD
  change (if graftGraph r (relabelData r σ τ D) = H.permuteInternal (blockPerm σ τ)
    then w (D.1.permuteInternal σ) * v (D.2.1.permuteInternal τ) else 0) = _
  rw [graftGraph_relabelData, hw, hv]
  have he : (graftGraph r D).permuteInternal (blockPerm σ τ) =
      H.permuteInternal (blockPerm σ τ) ↔ graftGraph r D = H :=
    (Graph.permuteInternalEquiv 2 3 (blockPerm σ τ)).injective.eq_iff
  rw [he]

end EnvelopingIsomorphism.Deformation.GraphBinaryGraftRelabelling
