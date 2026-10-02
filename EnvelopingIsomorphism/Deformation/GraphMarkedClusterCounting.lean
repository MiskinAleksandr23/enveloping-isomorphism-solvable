import EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting
import Mathlib.Logic.Equiv.Option

/-! Exact label fibres for a physical cluster with a retained marked vertex.
The marker may be inside or outside the cluster; no unmarked factorial is
silently used in place of the actual marked permutation count. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphMarkedClusterCounting
open scoped Classical BigOperators
open GraphLabelledClusterCounting

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def equivFixingPoints (x : α) (y : β) :
    {e : α ≃ β // e x = y} ≃ ({a : α // a ≠ x} ≃ {b : β // b ≠ y}) where
  toFun e := Equiv.subtypeEquiv e.val (by
    intro a
    have h : a ≠ x ↔ e.val a ≠ e.val x := e.val.injective.ne_iff.symm
    simpa only [e.property] using h)
  invFun e := ⟨(Equiv.optionSubtypeNe x).symm.trans ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe y)), by
    simp⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    by_cases h : a = x
    · subst a
      simp [e.property]
    · simp [Equiv.optionSubtypeNe_symm_of_ne h]
  right_inv e := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    simp [Equiv.optionSubtypeNe_symm_of_ne a.property]

variable [Fintype α] [Fintype β]

theorem card_equivFixingPoints (x : α) (y : β) (h : Fintype.card α = Fintype.card β) :
    Fintype.card {e : α ≃ β // e x = y} = (Fintype.card α - 1).factorial := by
  rw [Fintype.card_congr (equivFixingPoints x y)]
  have hc : Fintype.card {a : α // a ≠ x} = Fintype.card {b : β // b ≠ y} := by
    simp [Fintype.card_subtype_compl, h]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hc)]
  simp [Fintype.card_subtype_compl]

private def subtypeProdFstEquiv {A B : Type*} (P : A → Prop) :
    {v : A × B // P v.1} ≃ ({a : A // P a} × B) where
  toFun v := (⟨v.val.1,v.property⟩,v.val.2)
  invFun v := ⟨(v.1.val,v.2),v.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def subtypeProdSndEquiv {A B : Type*} (P : B → Prop) :
    {v : A × B // P v.2} ≃ (A × {b : B // P b}) where
  toFun v := (v.val.1,⟨v.val.2,v.property⟩)
  invFun v := ⟨(v.1,v.2.val),v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (S T : Finset α) (x y : α)

def markedInsideFiberEquiv (hx : x ∈ S) (hy : y ∈ T) :
    {σ : ClusterFiber S T // σ.val x = y} ≃
      ({e : S ≃ T // e ⟨x,hx⟩ = ⟨y,hy⟩} × ({a : α // a ∉ S} ≃ {a : α // a ∉ T})) :=
  (Equiv.subtypeEquiv (clusterFiberEquiv S T) (by
    intro σ
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h)).trans (subtypeProdFstEquiv _)

def markedOutsideFiberEquiv (hx : x ∉ S) (hy : y ∉ T) :
    {σ : ClusterFiber S T // σ.val x = y} ≃
      ((S ≃ T) × {e : {a : α // a ∉ S} ≃ {a : α // a ∉ T} // e ⟨x,hx⟩ = ⟨y,hy⟩}) :=
  (Equiv.subtypeEquiv (clusterFiberEquiv S T) (by
    intro σ
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h)).trans (subtypeProdSndEquiv _)

/-- Marking one cluster vertex removes precisely one cluster-label factorial slot. -/
theorem card_markedInsideFiber (hx : x ∈ S) (hy : y ∈ T) (h : S.card = T.card) :
    Fintype.card {σ : ClusterFiber S T // σ.val x = y} =
      (S.card - 1).factorial * (Fintype.card α - S.card).factorial := by
  rw [Fintype.card_congr (markedInsideFiberEquiv S T x y hx hy), Fintype.card_prod,
    card_equivFixingPoints _ _ (by simpa using h)]
  have hc : Fintype.card {a : α // a ∉ S} = Fintype.card {a : α // a ∉ T} := by
    simp [Fintype.card_subtype_compl, h]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hc)]
  simp [Fintype.card_subtype_compl]

/-- A retained vertex outside the cluster removes exactly one outside label slot. -/
theorem card_markedOutsideFiber (hx : x ∉ S) (hy : y ∉ T) (h : S.card = T.card) :
    Fintype.card {σ : ClusterFiber S T // σ.val x = y} =
      S.card.factorial * (Fintype.card α - S.card - 1).factorial := by
  rw [Fintype.card_congr (markedOutsideFiberEquiv S T x y hx hy), Fintype.card_prod,
    Fintype.card_equiv (Finset.equivOfCardEq h), card_equivFixingPoints]
  · simp [Fintype.card_subtype_compl]
  · simp [Fintype.card_subtype_compl, h]

end EnvelopingIsomorphism.Deformation.GraphMarkedClusterCounting
