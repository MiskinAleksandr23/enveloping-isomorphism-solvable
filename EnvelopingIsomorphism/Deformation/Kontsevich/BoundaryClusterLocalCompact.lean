import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterChart
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Local compactness of the actual boundary-cluster domain

The primitive coordinate image is exactly an intersection of open inequalities
and closed normalization/stationarity equalities. The admissible-radius domain
is also locally closed, using the proved fixed base-equality pattern.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set

abbrev BoundaryClusterParameterSpace (n m : ℕ) :=
  ℝ × (Fin n → ℂ) × (Fin n → ℂ) × (Fin m → ℝ) × (Fin m → ℝ)

private theorem isOpen_forall_finite {X J : Type*} [TopologicalSpace X] [Finite J]
    {p : J → X → Prop} (h : ∀ j, IsOpen {x | p j x}) : IsOpen {x | ∀ j, p j x} := by
  simpa only [setOf_forall] using isOpen_iInter_of_finite h

private theorem isClosed_forall {X J : Type*} [TopologicalSpace X]
    {p : J → X → Prop} (h : ∀ j, IsClosed {x | p j x}) : IsClosed {x | ∀ j, p j x} := by
  simpa only [setOf_forall] using isClosed_iInter h

private theorem isOpen_const_imp {X : Type*} [TopologicalSpace X] {p : Prop} {q : X → Prop}
    (hq : IsOpen {x | q x}) : IsOpen {x | p → q x} := by
  by_cases hp : p <;> simp_all

private theorem isClosed_const_imp {X : Type*} [TopologicalSpace X] {p : Prop} {q : X → Prop}
    (hq : IsClosed {x | q x}) : IsClosed {x | p → q x} := by
  by_cases hp : p <;> simp_all

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def closedCoordinateConditions (i a : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1))
    (x : BoundaryClusterParameterSpace n m) : Prop :=
  (∀ j, j ∈ S → x.2.1 j = (x.1 : ℂ)) ∧
  x.2.1 i = Complex.I ∧
  (∀ j, j ∉ S → x.2.2.1 j = 0) ∧
  x.2.2.1 a = Complex.I ∧
  (∀ j, j ∈ boundaryClusterBlock l u → x.2.2.2.1 j = x.1) ∧
  (∀ j, j ∉ boundaryClusterBlock l u → x.2.2.2.2 j = 0)

def openCoordinateConditions (i a : Fin n) (S : Finset (Fin n)) (l u : Fin (m + 1))
    (x : BoundaryClusterParameterSpace n m) : Prop :=
  a ∈ S ∧ i ∉ S ∧ l ≤ u ∧
  (∀ j, j ∉ S → 0 < (x.2.1 j).im) ∧
  (∀ j k, j ∉ S → k ∉ S → j ≠ k → x.2.1 j ≠ x.2.1 k) ∧
  (∀ j, j ∈ S → 0 < (x.2.2.1 j).im) ∧
  (∀ j k, j ∈ S → k ∈ S → j ≠ k → x.2.2.1 j ≠ x.2.2.1 k) ∧
  (∀ j : Fin m, j.val < l.val → x.2.2.2.1 j < x.1) ∧
  (∀ j : Fin m, u.val ≤ j.val → x.1 < x.2.2.2.1 j) ∧
  (∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2.2.2.1 j < x.2.2.2.1 k) ∧
  (∀ j k, j ∈ boundaryClusterBlock l u → k ∈ boundaryClusterBlock l u → j < k →
    x.2.2.2.2 j < x.2.2.2.2 k)

/-- Exact image, including a constructor for every point satisfying the primitive conditions. -/
theorem range_coordinates :
    Set.range (coordinates : BoundaryClusterData i a m S l u → BoundaryClusterParameterSpace n m) =
      {x | openCoordinateConditions i a S l u x} ∩ {x | closedCoordinateConditions i a S l u x} := by
  ext x
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨⟨D.anchor_mem, D.normalized_not_mem, D.block_order, D.base_im_pos_off,
      fun j k hj hk hjk heq => hjk (D.base_injective_off j k hj hk heq), D.velocity_im_pos,
      fun j k hj hk hjk heq => hjk (D.velocity_injective_on j k hj hk heq),
      D.boundaryBase_lt_center, D.center_lt_boundaryBase, D.boundaryBase_lt,
      D.boundaryVelocity_strictMono_on⟩,
      ⟨D.base_eq_center, D.base_normalized, D.velocity_zero_off, D.velocity_anchor,
        D.boundaryBase_eq_center, D.boundaryVelocity_zero_off⟩⟩
  · rintro ⟨⟨ha, hi, hlu, hpos, hbaseinj, hvelpos, hvelinj, hleft, hright, hblt, hvlt⟩,
      ⟨hcenter, hnorm, hveloff, hva, hbcenter, hvboff⟩⟩
    let D : BoundaryClusterData i a m S l u :=
      { center := x.1
        base := x.2.1
        velocity := x.2.2.1
        boundaryBase := x.2.2.2.1
        boundaryVelocity := x.2.2.2.2
        anchor_mem := ha
        normalized_not_mem := hi
        block_order := hlu
        base_eq_center := hcenter
        base_im_pos_off := hpos
        base_injective_off := by
          intro j k hj hk heq
          by_contra hjk
          exact hbaseinj j k hj hk hjk heq
        base_normalized := hnorm
        velocity_im_pos := hvelpos
        velocity_zero_off := hveloff
        velocity_injective_on := by
          intro j k hj hk heq
          by_contra hjk
          exact hvelinj j k hj hk hjk heq
        velocity_anchor := hva
        boundaryBase_eq_center := hbcenter
        boundaryBase_lt_center := hleft
        center_lt_boundaryBase := hright
        boundaryBase_lt := hblt
        boundaryVelocity_zero_off := hvboff
        boundaryVelocity_strictMono_on := hvlt }
    exact ⟨D, rfl⟩

theorem isClosed_closedCoordinateConditions :
    IsClosed {x : BoundaryClusterParameterSpace n m | closedCoordinateConditions i a S l u x} := by
  unfold closedCoordinateConditions
  repeat' first
    | apply IsClosed.and
    | apply isClosed_forall; intro j
    | apply isClosed_const_imp
  all_goals exact isClosed_eq (by fun_prop) (by fun_prop)

theorem isOpen_openCoordinateConditions :
    IsOpen {x : BoundaryClusterParameterSpace n m | openCoordinateConditions i a S l u x} := by
  unfold openCoordinateConditions
  repeat' first
    | exact isOpen_const
    | apply IsOpen.and
    | apply isOpen_forall_finite; intro j
    | apply isOpen_const_imp
  all_goals first
    | exact isOpen_lt (by fun_prop) (by fun_prop)
    | exact (isClosed_eq (by fun_prop) (by fun_prop)).isOpen_compl

theorem isLocallyClosed_range_coordinates :
    IsLocallyClosed (Set.range (coordinates : BoundaryClusterData i a m S l u →
      BoundaryClusterParameterSpace n m)) := by
  rw [range_coordinates]
  exact ⟨_, _, isOpen_openCoordinateConditions, isClosed_closedCoordinateConditions, rfl⟩

instance : LocallyCompactSpace (BoundaryClusterData i a m S l u) :=
  isEmbedding_coordinates.isInducing.locallyCompactSpace isLocallyClosed_range_coordinates

end BoundaryClusterData

namespace BoundaryClusterDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- Strict scale conditions with the proved, fixed combinatorial equality mask. -/
def openScaleConditions (x : BoundaryClusterData i a m S l u × ℝ) : Prop :=
  (∀ j k, ¬(j = k ∨ (j ∈ S ∧ k ∈ S)) →
    x.2 * ‖x.1.velocity j - x.1.velocity k‖ < ‖x.1.base j - x.1.base k‖) ∧
  (∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2 * |x.1.boundaryVelocity k - x.1.boundaryVelocity j| < x.1.boundaryBase k - x.1.boundaryBase j)

theorem admissibleScale_iff_openScaleConditions (x : BoundaryClusterData i a m S l u × ℝ) :
    x.1.AdmissibleScale x.2 ↔ 0 ≤ x.2 ∧ openScaleConditions x := by
  constructor
  · intro hx
    exact ⟨hx.nonneg, fun j k hmask => hx.separation j k
      (fun hbase => hmask ((x.1.base_eq_iff j k).mp hbase)), hx.boundary_separation⟩
  · rintro ⟨hnonneg, hsep, hbsep⟩
    exact ⟨hnonneg, fun j k hbase => hsep j k
      (fun hmask => hbase ((x.1.base_eq_iff j k).mpr hmask)), hbsep⟩

theorem isOpen_openScaleConditions :
    IsOpen {x : BoundaryClusterData i a m S l u × ℝ | openScaleConditions x} := by
  unfold openScaleConditions
  repeat' first
    | apply IsOpen.and
    | apply isOpen_forall_finite; intro j
    | apply isOpen_const_imp
  all_goals exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isLocallyClosed_admissibleScale :
    IsLocallyClosed {x : BoundaryClusterData i a m S l u × ℝ | x.1.AdmissibleScale x.2} := by
  refine ⟨{x | openScaleConditions x}, {x | 0 ≤ x.2}, isOpen_openScaleConditions,
    isClosed_le continuous_const continuous_snd, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, admissibleScale_iff_openScaleConditions, and_comm]

instance : LocallyCompactSpace (BoundaryClusterDomain i a m S l u) := by
  change LocallyCompactSpace {x : BoundaryClusterData i a m S l u × ℝ | x.1.AdmissibleScale x.2}
  exact isLocallyClosed_admissibleScale.locallyCompactSpace

end BoundaryClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
