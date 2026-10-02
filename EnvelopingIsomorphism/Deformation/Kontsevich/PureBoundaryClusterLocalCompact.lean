import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Local compactness of the actual pure boundary-cluster parameter domain

The primitive coordinate range is exactly an open-condition locus intersected
with a closed-equation locus. The converse constructs the native upper-half-plane
interior coordinates. Nonnegative radii with the fixed strict boundary bounds
then form a locally closed subset of the product parameter space.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set
open scoped UpperHalfPlane

abbrev PureBoundaryClusterParameterSpace (n m : ℕ) :=
  ℝ × (Fin n → ℂ) × (Fin m → ℝ) × (Fin m → ℝ)

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

namespace PureBoundaryClusterData

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def closedCoordinateConditions (i : Fin n) (l u : Fin (m + 1)) (a b : Fin m)
    (x : PureBoundaryClusterParameterSpace n m) : Prop :=
  x.2.1 i = Complex.I ∧
  (∀ j, j ∈ boundaryClusterBlock l u → x.2.2.1 j = x.1) ∧
  (∀ j, j ∉ boundaryClusterBlock l u → x.2.2.2 j = 0) ∧
  x.2.2.2 a = 0 ∧ x.2.2.2 b = 1

def openCoordinateConditions (l u : Fin (m + 1)) (a b : Fin m)
    (x : PureBoundaryClusterParameterSpace n m) : Prop :=
  a.val = l.val ∧ b.val + 1 = u.val ∧ a < b ∧
  (∀ j, 0 < (x.2.1 j).im) ∧
  (∀ j k, j ≠ k → x.2.1 j ≠ x.2.1 k) ∧
  (∀ j : Fin m, j.val < l.val → x.2.2.1 j < x.1) ∧
  (∀ j : Fin m, u.val ≤ j.val → x.1 < x.2.2.1 j) ∧
  (∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2.2.1 j < x.2.2.1 k) ∧
  (∀ j k, j ∈ boundaryClusterBlock l u → k ∈ boundaryClusterBlock l u → j < k →
    x.2.2.2 j < x.2.2.2 k)

/-- Exact primitive image, including a native datum for each point of the displayed locus. -/
theorem range_coordinates :
    Set.range (coordinates : PureBoundaryClusterData i m l u a b →
      PureBoundaryClusterParameterSpace n m) =
      {x | openCoordinateConditions l u a b x} ∩ {x | closedCoordinateConditions i l u a b x} := by
  ext x
  constructor
  · rintro ⟨D, rfl⟩
    refine ⟨⟨D.left_endpoint, D.right_endpoint, D.endpoint_lt, fun j => (D.interior j).im_pos,
      ?_, D.boundaryBase_lt_center, D.center_lt_boundaryBase, D.boundaryBase_lt,
      D.boundaryVelocity_strictMono_on⟩,
      ⟨?_, D.boundaryBase_eq_center, D.boundaryVelocity_zero_off,
        D.boundaryVelocity_left, D.boundaryVelocity_right⟩⟩
    · intro j k hjk heq
      exact hjk (D.interior_injective (UpperHalfPlane.ext heq))
    · exact congrArg (fun z : ℍ => (z : ℂ)) D.interior_normalized
  · rintro ⟨⟨hleft, hright, hab, hpos, hinj, hltcenter, hcenterlt, hblt, hvlt⟩,
      ⟨hnorm, hcenter, hvoff, hva, hvb⟩⟩
    let D : PureBoundaryClusterData i m l u a b :=
      { center := x.1
        interior := fun j => ⟨x.2.1 j, hpos j⟩
        boundaryBase := x.2.2.1
        boundaryVelocity := x.2.2.2
        left_endpoint := hleft
        right_endpoint := hright
        endpoint_lt := hab
        interior_injective := by
          intro j k heq
          by_contra hjk
          exact hinj j k hjk (congrArg (fun z : ℍ => (z : ℂ)) heq)
        interior_normalized := UpperHalfPlane.ext hnorm
        boundaryBase_eq_center := hcenter
        boundaryBase_lt_center := hltcenter
        center_lt_boundaryBase := hcenterlt
        boundaryBase_lt := hblt
        boundaryVelocity_zero_off := hvoff
        boundaryVelocity_strictMono_on := hvlt
        boundaryVelocity_left := hva
        boundaryVelocity_right := hvb }
    exact ⟨D, rfl⟩

theorem exists_coordinates_eq (x : PureBoundaryClusterParameterSpace n m)
    (ho : openCoordinateConditions l u a b x) (hc : closedCoordinateConditions i l u a b x) :
    ∃ D : PureBoundaryClusterData i m l u a b, coordinates D = x := by
  change x ∈ Set.range coordinates
  rw [range_coordinates]
  exact ⟨ho, hc⟩

/-- Native data reconstructed from the proved exact primitive coordinate locus. -/
def ofCoordinates (x : PureBoundaryClusterParameterSpace n m)
    (ho : openCoordinateConditions l u a b x) (hc : closedCoordinateConditions i l u a b x) :
    PureBoundaryClusterData i m l u a b :=
  Classical.choose (exists_coordinates_eq x ho hc)

@[simp] theorem coordinates_ofCoordinates (x : PureBoundaryClusterParameterSpace n m)
    (ho : openCoordinateConditions l u a b x) (hc : closedCoordinateConditions i l u a b x) :
    coordinates (ofCoordinates x ho hc) = x :=
  Classical.choose_spec (exists_coordinates_eq x ho hc)

theorem isClosed_closedCoordinateConditions :
    IsClosed {x : PureBoundaryClusterParameterSpace n m | closedCoordinateConditions i l u a b x} := by
  unfold closedCoordinateConditions
  repeat' first
    | apply IsClosed.and
    | apply isClosed_forall; intro j
    | apply isClosed_const_imp
  all_goals exact isClosed_eq (by fun_prop) (by fun_prop)

theorem isOpen_openCoordinateConditions :
    IsOpen {x : PureBoundaryClusterParameterSpace n m | openCoordinateConditions l u a b x} := by
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
    IsLocallyClosed (Set.range (coordinates : PureBoundaryClusterData i m l u a b →
      PureBoundaryClusterParameterSpace n m)) := by
  rw [range_coordinates]
  exact ⟨_, _, isOpen_openCoordinateConditions, isClosed_closedCoordinateConditions, rfl⟩

instance : LocallyCompactSpace (PureBoundaryClusterData i m l u a b) :=
  isEmbedding_coordinates.isInducing.locallyCompactSpace isLocallyClosed_range_coordinates

end PureBoundaryClusterData

namespace PureBoundaryClusterDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

/-- The strict radial bounds depend only on the prescribed boundary-label block. -/
def openScaleConditions (x : PureBoundaryClusterData i m l u a b × ℝ) : Prop :=
  ∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2 * |x.1.boundaryVelocity k - x.1.boundaryVelocity j| <
      x.1.boundaryBase k - x.1.boundaryBase j

theorem admissibleScale_iff_openScaleConditions (x : PureBoundaryClusterData i m l u a b × ℝ) :
    x.1.AdmissibleScale x.2 ↔ 0 ≤ x.2 ∧ openScaleConditions x :=
  ⟨fun hx => ⟨hx.nonneg, hx.boundary_separation⟩, fun hx => ⟨hx.1, hx.2⟩⟩

theorem isOpen_openScaleConditions :
    IsOpen {x : PureBoundaryClusterData i m l u a b × ℝ | openScaleConditions x} := by
  unfold openScaleConditions
  repeat' first
    | apply isOpen_forall_finite; intro j
    | apply isOpen_const_imp
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isLocallyClosed_admissibleScale :
    IsLocallyClosed {x : PureBoundaryClusterData i m l u a b × ℝ | x.1.AdmissibleScale x.2} := by
  refine ⟨{x | openScaleConditions x}, {x | 0 ≤ x.2}, isOpen_openScaleConditions,
    isClosed_le continuous_const continuous_snd, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, admissibleScale_iff_openScaleConditions, and_comm]

instance : LocallyCompactSpace (PureBoundaryClusterDomain i m l u a b) := by
  change LocallyCompactSpace {x : PureBoundaryClusterData i m l u a b × ℝ | x.1.AdmissibleScale x.2}
  exact isLocallyClosed_admissibleScale.locallyCompactSpace

end PureBoundaryClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
