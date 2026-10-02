import EnvelopingIsomorphism.Descent.SemilinearLieIsomAction
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic

/-! Finite weighted coordinate flags and maps with the prescribed graded identity. -/

namespace EnvelopingIsomorphism.Descent

open Module

noncomputable section

variable {k n V W : Type*} [Field k] [Fintype n] [DecidableEq n]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The decreasing finite flag attached to a weighted basis. -/
def basisWeightFiltration (b : Basis n k V) (weight : n → ℕ) : FiniteFiltration k V where
  step d := Submodule.span k (b '' {i | d ≤ weight i})
  length := Finset.univ.sup weight + 1
  step_zero := by simpa using b.span_eq
  antitone := by
    intro d e hde
    apply Submodule.span_mono
    exact Set.image_mono (fun i hi => le_trans hde hi)
  step_length := by
    have hset : {i | Finset.univ.sup weight + 1 ≤ weight i} = (∅ : Set n) := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have hi : weight i ≤ Finset.univ.sup weight := Finset.le_sup (Finset.mem_univ i)
      omega
    rw [hset, Set.image_empty, Submodule.span_empty]

theorem mem_basisWeightFiltration_iff (b : Basis n k V) (weight : n → ℕ) (d : ℕ) (x : V) :
    x ∈ (basisWeightFiltration b weight).step d ↔
      ∀ i, weight i < d → b.repr x i = 0 := by
  change x ∈ Submodule.span k (b '' {i | d ≤ weight i}) ↔ _
  rw [b.mem_span_image]
  constructor
  · intro hx i hi
    by_contra hne
    exact (not_le_of_gt hi) (hx (Finsupp.mem_support_iff.mpr hne))
  · intro hx i hi
    by_contra hlt
    have hzero := hx i (lt_of_not_ge hlt)
    exact Finsupp.mem_support_iff.mp hi hzero

/-- A map's degree bound on the basis extends to every filtered vector. -/
theorem maps_step_of_basis (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ)
    (T : V →ₗ[k] W) (shift : ℕ)
    (hT : ∀ i, T (bV i) ∈ (basisWeightFiltration bW weight).step (weight i + shift))
    (d : ℕ) (x : V) (hx : x ∈ (basisWeightFiltration bV weight).step d) :
    T x ∈ (basisWeightFiltration bW weight).step (d + shift) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact (basisWeightFiltration bW weight).antitone (Nat.add_le_add_right hi shift) (hT i)
  | zero => simpa using (basisWeightFiltration bW weight).step (d + shift) |>.zero_mem
  | add x y hx hy hfx hfy => simpa only [map_add] using Submodule.add_mem _ hfx hfy
  | smul a x hx hfx => simpa only [map_smul] using Submodule.smul_mem _ a hfx

/-- The reference vector-space equivalence matching the two bases. -/
def basisReference (bV : Basis n k V) (bW : Basis n k W) : V ≃ₗ[k] W :=
  bV.equiv bW (Equiv.refl n)

@[simp] theorem basisReference_basis (bV : Basis n k V) (bW : Basis n k W) (i : n) :
    basisReference bV bW (bV i) = bW i := Basis.equiv_apply _ _ _ _

@[simp] theorem basisReference_repr (bV : Basis n k V) (bW : Basis n k W) (x : V) (i : n) :
    bW.repr (basisReference bV bW x) i = bV.repr x i := by
  simp [basisReference, Basis.equiv]

theorem basisReference_mem_iff (bV : Basis n k V) (bW : Basis n k W)
    (weight : n → ℕ) (d : ℕ) (x : V) :
    basisReference bV bW x ∈ (basisWeightFiltration bW weight).step d ↔
      x ∈ (basisWeightFiltration bV weight).step d := by
  simp only [mem_basisWeightFiltration_iff, basisReference_repr]

/-- Coordinate form of the prescribed identity on the associated graded. -/
def IsMarkedMap (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ) (T : V →ₗ[k] W) : Prop :=
  ∀ i r, weight r ≤ weight i → bW.repr (T (bV i)) r = if r = i then 1 else 0

theorem marked_difference_mem (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ)
    (T : V →ₗ[k] W) (hT : IsMarkedMap bV bW weight T)
    (d : ℕ) (x : V) (hx : x ∈ (basisWeightFiltration bV weight).step d) :
    T x - basisReference bV bW x ∈ (basisWeightFiltration bW weight).step (d + 1) := by
  apply maps_step_of_basis bV bW weight (T - (basisReference bV bW).toLinearMap) 1 _ d x hx
  intro i
  apply (mem_basisWeightFiltration_iff bW weight (weight i + 1) _).mpr
  intro r hr
  simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, LinearEquiv.coe_coe,
    basisReference_basis]
  rw [hT i r (by omega)]
  simp [Finsupp.single_apply, eq_comm]

theorem marked_preserves (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ)
    (T : V →ₗ[k] W) (hT : IsMarkedMap bV bW weight T)
    (d : ℕ) (x : V) (hx : x ∈ (basisWeightFiltration bV weight).step d) :
    T x ∈ (basisWeightFiltration bW weight).step d := by
  have hdiff := (basisWeightFiltration bW weight).antitone (Nat.le_succ d)
    (marked_difference_mem bV bW weight T hT d x hx)
  have href := (basisReference_mem_iff bV bW weight d x).mpr hx
  simpa only [sub_add_cancel] using
    ((basisWeightFiltration bW weight).step d).add_mem hdiff href

/-- A filtration-trivial correction leaves a marked map marked. -/
theorem marked_postcompose (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ)
    (T : V →ₗ[k] W) (hT : IsMarkedMap bV bW weight T) (U : Module.End k W)
    (hU : U - 1 ∈ (basisWeightFiltration bW weight).raisingSubmodule 1) :
    IsMarkedMap bV bW weight (U.comp T) := by
  intro i r hri
  have hbi : bV i ∈ (basisWeightFiltration bV weight).step (weight i) :=
    Submodule.subset_span ⟨i, by simp, rfl⟩
  have hy := marked_preserves bV bW weight T hT (weight i) (bV i) hbi
  have hd := hU (weight i) (T (bV i)) hy
  have hc := (mem_basisWeightFiltration_iff bW weight (weight i + 1) _).mp hd r (by omega)
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, Finsupp.sub_apply] at hc
  change bW.repr (U (T (bV i))) r = _
  rw [sub_eq_zero.mp hc, hT i r hri]

/-- Linear form of the elementary inverse-filtration argument. -/
theorem linear_inverse_preserves (F : FiniteFiltration k W) (u : W ≃ₗ[k] W)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule 1)
    (i : ℕ) (x : W) (hx : x ∈ F.step i) : u.symm x ∈ F.step i := by
  have aux : ∀ j, j ≤ i → u.symm x ∈ F.step j := by
    intro j
    induction j with
    | zero => intro; simp [F.step_zero]
    | succ j ih =>
      intro hji
      have hdiff : x - u.symm x ∈ F.step (j + 1) := by
        simpa using hu j (u.symm x) (ih (by omega))
      have hxj : x ∈ F.step (j + 1) := F.antitone hji hx
      simpa using (F.step (j + 1)).sub_mem hxj hdiff
  exact aux i le_rfl

/-- The inverse of a marked equivalence preserves the weighted flag. -/
theorem marked_inverse_preserves (bV : Basis n k V) (bW : Basis n k W) (weight : n → ℕ)
    (f : V ≃ₗ[k] W) (hf : IsMarkedMap bV bW weight f.toLinearMap)
    (d : ℕ) (y : W) (hy : y ∈ (basisWeightFiltration bW weight).step d) :
    f.symm y ∈ (basisWeightFiltration bV weight).step d := by
  let u : W ≃ₗ[k] W := (basisReference bV bW).symm.trans f
  have hu : u.toLinearMap - 1 ∈ (basisWeightFiltration bW weight).raisingSubmodule 1 := by
    intro i x hx
    have hbase : (basisReference bV bW).symm x ∈ (basisWeightFiltration bV weight).step i := by
      apply (basisReference_mem_iff bV bW weight i _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hx
    change f ((basisReference bV bW).symm x) - x ∈ (basisWeightFiltration bW weight).step (i + 1)
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      marked_difference_mem bV bW weight f.toLinearMap hf i _ hbase
  have h := linear_inverse_preserves (basisWeightFiltration bW weight) u hu d y hy
  apply (basisReference_mem_iff bV bW weight d _).mp
  exact h

section Lie

variable {A B : Type*} [LieRing A] [LieAlgebra k A] [LieRing B] [LieAlgebra k B]

/-- Two marked Lie equivalences differ by a filtration-trivial target automorphism. -/
theorem isomDifference_mem_of_marked (bA : Basis n k A) (bB : Basis n k B) (weight : n → ℕ)
    (f g : A ≃ₗ⁅k⁆ B)
    (hf : IsMarkedMap bA bB weight f.toLinearMap)
    (hg : IsMarkedMap bA bB weight g.toLinearMap) :
    isomDifference f g ∈ (basisWeightFiltration bB weight).automorphismSubgroup 0 := by
  apply isomDifference_mem_of_same_graded (basisWeightFiltration bA weight)
    (basisWeightFiltration bB weight) f g
  · exact marked_inverse_preserves bA bB weight g.toLinearEquiv hg
  · intro d x hx
    have h := (basisWeightFiltration bB weight).step (d + 1) |>.sub_mem
      (marked_difference_mem bA bB weight f.toLinearMap hf d x hx)
      (marked_difference_mem bA bB weight g.toLinearMap hg d x hx)
    change (f x - basisReference bA bB x) - (g x - basisReference bA bB x) ∈
      (basisWeightFiltration bB weight).step (d + 1) at h
    simpa only [sub_sub_sub_cancel_right] using h

end Lie

end

end EnvelopingIsomorphism.Descent
