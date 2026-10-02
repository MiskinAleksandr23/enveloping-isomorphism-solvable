import EnvelopingIsomorphism.Deformation.GeneralGraphSplitSlotRelabelling
import EnvelopingIsomorphism.Deformation.GraphCurvatureLabelCounting
import Mathlib.Logic.Equiv.Option

/-! Every actual permutation of a two-point physical cluster decomposes into
an actual quotient relabelling and a permutation of its two children. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.GeneralGraphSplitPairRelabelling
open scoped Classical
open KontsevichGraph.General GraphLabelledClusterCounting GraphCurvatureLabelCounting
variable {n : ℕ}

def childEquiv (r : Fin (n + 1)) : Fin 2 ≃ (childPair r) :=
  Equiv.ofBijective (fun c => ⟨vertexSplitChild r c, by fin_cases c <;> simp [childPair]⟩) (by
    constructor
    · intro a b h
      exact vertexSplitChild_injective r (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact ⟨0,Subtype.ext hv.symm⟩
      · exact ⟨1,Subtype.ext (Finset.mem_singleton.mp hv).symm⟩)

def outsideChildEquiv (r : Fin (n + 1)) :
    {v : Fin (n + 1) // v ≠ r} ≃ {v : Fin (n + 2) // v ∉ childPair r} :=
  Equiv.ofBijective (fun v => ⟨vertexSplitOldEmbedding r v.val, by
    simp only [childPair, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨vertexSplitOld_ne_child r v.val v.property 0,
      vertexSplitOld_ne_child r v.val v.property 1⟩⟩) (by
    constructor
    · intro v w h
      apply Subtype.ext
      exact splitExternalEmbedding_injective r (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨s,he⟩ := (vertexSplitSourceEquiv r).symm.surjective v
      cases s with
      | inl s => exact ⟨s,Subtype.ext ((vertexSplitSourceEquiv_symm_old r s).symm.trans he)⟩
      | inr c =>
        have hm : v ∈ childPair r := by
          rw [← he, vertexSplitSourceEquiv_symm_child]
          fin_cases c <;> simp [childPair]
        exact (hv hm).elim)

variable (r s : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2)))
variable (hπ : ∀ v, π v ∈ childPair s ↔ v ∈ childPair r)

def clusterData := clusterFiberEquiv (childPair r) (childPair s) ⟨π,hπ⟩

def children : Equiv.Perm (Fin 2) :=
  (childEquiv r).trans ((clusterData r s π hπ).1.trans (childEquiv s).symm)

def outside : {v : Fin (n + 1) // v ≠ r} ≃ {v : Fin (n + 1) // v ≠ s} :=
  (outsideChildEquiv r).trans ((clusterData r s π hπ).2.trans (outsideChildEquiv s).symm)

def quotient : Equiv.Perm (Fin (n + 1)) :=
  (Equiv.optionSubtypeNe r).symm.trans
    ((Equiv.optionCongr (outside r s π hπ)).trans (Equiv.optionSubtypeNe s))

@[simp] theorem quotient_root : quotient r s π hπ r = s := by simp [quotient]

@[simp] theorem quotient_outside (v : Fin (n + 1)) (hv : v ≠ r) :
    quotient r s π hπ v = (outside r s π hπ ⟨v,hv⟩).val := by
  simp [quotient, Equiv.optionSubtypeNe_symm_of_ne hv]

theorem children_spec (c : Fin 2) :
    vertexSplitChild s (children r s π hπ c) = π (vertexSplitChild r c) := by
  change (childEquiv s (children r s π hπ c)).val = _
  simp only [children, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem outside_spec (v : Fin (n + 1)) (hv : v ≠ r) :
    vertexSplitOldEmbedding s (outside r s π hπ ⟨v,hv⟩).val = π (vertexSplitOldEmbedding r v) := by
  change (outsideChildEquiv s (outside r s π hπ ⟨v,hv⟩)).val = _
  simp only [outside, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- The induced quotient and child maps reconstruct the literal original
permutation on every outside vertex and both children. -/
theorem splitVertices_quotient_children :
    SlotRelabelling.splitVertices r s (quotient r s π hπ) (quotient_root r s π hπ)
      (children r s π hπ) = π := by
  apply Equiv.ext
  intro v
  obtain ⟨v,rfl⟩ := (vertexSplitSourceEquiv r).symm.surjective v
  cases v with
  | inl v =>
    rw [vertexSplitSourceEquiv_symm_old,
      SlotRelabelling.splitVertices_old r s _ _ _ v.val v.property, quotient_outside]
    exact outside_spec r s π hπ v.val v.property
  | inr c =>
    rw [vertexSplitSourceEquiv_symm_child, SlotRelabelling.splitVertices_child]
    exact children_spec r s π hπ c

/-- A vector in child zero fixes the child order, not just the unordered pair. -/
theorem children_eq_refl_of_zero (h0 : π (vertexSplitChild r 0) = vertexSplitChild s 0) :
    children r s π hπ = Equiv.refl _ := by
  have hc : children r s π hπ 0 = 0 :=
    vertexSplitChild_injective s ((children_spec r s π hπ 0).trans h0)
  have hp : ∀ δ : Equiv.Perm (Fin 2), δ 0 = 0 → δ = Equiv.refl _ := by decide
  exact hp _ hc

include hπ in
/-- Existential form convenient for scalar-profile covariance proofs. -/
theorem exists_quotient_children :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∃ hr : σ r = s, ∃ δ : Equiv.Perm (Fin 2),
      SlotRelabelling.splitVertices r s σ hr δ = π :=
  ⟨quotient r s π hπ, quotient_root r s π hπ, children r s π hπ,
    splitVertices_quotient_children r s π hπ⟩

end EnvelopingIsomorphism.Deformation.GeneralGraphSplitPairRelabelling
