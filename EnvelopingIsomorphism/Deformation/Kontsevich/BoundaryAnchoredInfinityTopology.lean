import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityData
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# The actual boundary-anchored infinity parameter topology

The primitive coordinates are all inner shapes and the real boundary base and
velocity families. Their exact range is locally closed in a finite-dimensional
space. The nonnegative admissible-scale domain is locally closed in its product
with the real line. No outside interior or second boundary label is required.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology Set
open scoped UpperHalfPlane

abbrev BoundaryAnchoredInfinityParameterSpace (n m : ℕ) :=
  (Fin n → ℂ) × (Fin m → ℝ) × (Fin m → ℝ)

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

namespace BoundaryAnchoredInfinityData

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

@[ext] theorem ext {D E : BoundaryAnchoredInfinityData a m l u o}
    (hshape : D.shape = E.shape) (hbase : D.boundaryBase = E.boundaryBase)
    (hvelocity : D.boundaryVelocity = E.boundaryVelocity) : D = E := by
  cases D
  cases E
  cases hshape
  cases hbase
  cases hvelocity
  rfl

/-- The three genuine coordinate families, in the order `(shape, base, velocity)`. -/
def coords (D : BoundaryAnchoredInfinityData a m l u o) : BoundaryAnchoredInfinityParameterSpace n m :=
  (fun j => (D.shape j : ℂ), D.boundaryBase, D.boundaryVelocity)

theorem coords_injective :
    Function.Injective (coords : BoundaryAnchoredInfinityData a m l u o → _) := by
  intro D E h
  apply ext
  · funext j
    exact UpperHalfPlane.ext (congrArg (fun x => x.1 j) h)
  · exact congrArg (fun x => x.2.1) h
  · exact congrArg (fun x => x.2.2) h

instance instTopologicalSpace : TopologicalSpace (BoundaryAnchoredInfinityData a m l u o) :=
  TopologicalSpace.induced coords inferInstance

theorem isEmbedding_coords :
    IsEmbedding (coords : BoundaryAnchoredInfinityData a m l u o → _) :=
  coords_injective.isEmbedding_induced

instance : T2Space (BoundaryAnchoredInfinityData a m l u o) := isEmbedding_coords.t2Space

@[fun_prop] theorem continuous_coords :
    Continuous (coords : BoundaryAnchoredInfinityData a m l u o → _) :=
  isEmbedding_coords.continuous

theorem continuous_shapeCoordinates :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => fun j => (D.shape j : ℂ)) :=
  continuous_coords.fst

@[fun_prop] theorem continuous_boundaryBase :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.boundaryBase) :=
  continuous_coords.snd.fst

@[fun_prop] theorem continuous_boundaryVelocity :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.boundaryVelocity) :=
  continuous_coords.snd.snd

@[fun_prop] theorem continuous_shape_apply (j : Fin n) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => (D.shape j : ℂ)) :=
  (continuous_apply j).comp continuous_shapeCoordinates

@[fun_prop] theorem continuous_boundaryBase_apply (j : Fin m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.boundaryBase j) :=
  (continuous_apply j).comp continuous_boundaryBase

@[fun_prop] theorem continuous_boundaryVelocity_apply (j : Fin m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.boundaryVelocity j) :=
  (continuous_apply j).comp continuous_boundaryVelocity

@[fun_prop] theorem continuous_doubledBase (v : DoubledLabel n m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.doubledBase v) := by
  rcases v with (j | j) | j
  · exact continuous_const
  · exact Complex.continuous_ofReal.comp (continuous_boundaryBase_apply j)
  · exact continuous_const

@[fun_prop] theorem continuous_doubledVelocity (v : DoubledLabel n m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.doubledVelocity v) := by
  rcases v with (j | j) | j
  · exact continuous_shape_apply j
  · exact Complex.continuous_ofReal.comp (continuous_boundaryVelocity_apply j)
  · exact Complex.continuous_conj.comp (continuous_shape_apply j)

@[fun_prop] theorem continuous_pairBase (p : DoubledPair n m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.pairBase p) :=
  (continuous_doubledBase p.val.2).sub (continuous_doubledBase p.val.1)

@[fun_prop] theorem continuous_pairVelocity (p : DoubledPair n m) :
    Continuous (fun D : BoundaryAnchoredInfinityData a m l u o => D.pairVelocity p) :=
  (continuous_doubledVelocity p.val.2).sub (continuous_doubledVelocity p.val.1)

def closedCoordinateConditions (a : Fin n) (l u : Fin (m + 1)) (o : Fin m)
    (x : BoundaryAnchoredInfinityParameterSpace n m) : Prop :=
  x.1 a = Complex.I ∧
  (∀ j, j ∈ boundaryClusterBlock l u → x.2.1 j = 0) ∧
  (∀ j, j ∉ boundaryClusterBlock l u → x.2.2 j = 0) ∧
  x.2.1 o = referenceSign l o

def openCoordinateConditions (l u : Fin (m + 1)) (o : Fin m)
    (x : BoundaryAnchoredInfinityParameterSpace n m) : Prop :=
  l ≤ u ∧ o ∉ boundaryClusterBlock l u ∧
  (∀ j, 0 < (x.1 j).im) ∧
  (∀ j k, j ≠ k → x.1 j ≠ x.1 k) ∧
  (∀ j : Fin m, j.val < l.val → x.2.1 j < 0) ∧
  (∀ j : Fin m, u.val ≤ j.val → 0 < x.2.1 j) ∧
  (∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2.1 j < x.2.1 k) ∧
  (∀ j k, j ∈ boundaryClusterBlock l u → k ∈ boundaryClusterBlock l u → j < k →
    x.2.2 j < x.2.2 k)

/-- Exact coordinate image, with a native datum constructed from every point
satisfying the displayed open and closed conditions. -/
theorem range_coords :
    Set.range (coords : BoundaryAnchoredInfinityData a m l u o →
      BoundaryAnchoredInfinityParameterSpace n m) =
      {x | openCoordinateConditions l u o x} ∩ {x | closedCoordinateConditions a l u o x} := by
  ext x
  constructor
  · rintro ⟨D, rfl⟩
    refine ⟨⟨D.block_order, D.outside_not_mem, fun j => (D.shape j).im_pos,
      ?_, D.boundaryBase_neg_left, D.boundaryBase_pos_right, D.boundaryBase_lt,
      D.boundaryVelocity_strictMono_on⟩,
      ⟨?_, D.boundaryBase_zero_on, D.boundaryVelocity_zero_off, D.boundaryBase_anchor⟩⟩
    · intro j k hjk heq
      exact hjk (D.shape_injective (UpperHalfPlane.ext heq))
    · exact congrArg (fun z : ℍ => (z : ℂ)) D.shape_anchor
  · rintro ⟨⟨horder, houtside, hpos, hinj, hneg, hright, hbase, hvelocity⟩,
      ⟨hanchor, hzero, hvoff, hreference⟩⟩
    let D : BoundaryAnchoredInfinityData a m l u o :=
      { shape := fun j => ⟨x.1 j, hpos j⟩
        boundaryBase := x.2.1
        boundaryVelocity := x.2.2
        shape_injective := by
          intro j k heq
          by_contra hjk
          exact hinj j k hjk (congrArg (fun z : ℍ => (z : ℂ)) heq)
        shape_anchor := UpperHalfPlane.ext hanchor
        block_order := horder
        outside_not_mem := houtside
        boundaryBase_zero_on := hzero
        boundaryBase_neg_left := hneg
        boundaryBase_pos_right := hright
        boundaryBase_lt := hbase
        boundaryVelocity_zero_off := hvoff
        boundaryVelocity_strictMono_on := hvelocity
        boundaryBase_anchor := hreference }
    exact ⟨D, rfl⟩

theorem exists_coords_eq (x : BoundaryAnchoredInfinityParameterSpace n m)
    (ho : openCoordinateConditions l u o x) (hc : closedCoordinateConditions a l u o x) :
    ∃ D : BoundaryAnchoredInfinityData a m l u o, coords D = x := by
  change x ∈ Set.range coords
  rw [range_coords]
  exact ⟨ho, hc⟩

def ofCoordinates (x : BoundaryAnchoredInfinityParameterSpace n m)
    (ho : openCoordinateConditions l u o x) (hc : closedCoordinateConditions a l u o x) :
    BoundaryAnchoredInfinityData a m l u o := Classical.choose (exists_coords_eq x ho hc)

@[simp] theorem coords_ofCoordinates (x : BoundaryAnchoredInfinityParameterSpace n m)
    (ho : openCoordinateConditions l u o x) (hc : closedCoordinateConditions a l u o x) :
    coords (ofCoordinates x ho hc) = x := Classical.choose_spec (exists_coords_eq x ho hc)

theorem isClosed_closedCoordinateConditions :
    IsClosed {x : BoundaryAnchoredInfinityParameterSpace n m | closedCoordinateConditions a l u o x} := by
  unfold closedCoordinateConditions
  repeat' first
    | apply IsClosed.and
    | apply isClosed_forall; intro j
    | apply isClosed_const_imp
  all_goals exact isClosed_eq (by fun_prop) (by fun_prop)

theorem isOpen_openCoordinateConditions :
    IsOpen {x : BoundaryAnchoredInfinityParameterSpace n m | openCoordinateConditions l u o x} := by
  unfold openCoordinateConditions
  repeat' first
    | exact isOpen_const
    | apply IsOpen.and
    | apply isOpen_forall_finite; intro j
    | apply isOpen_const_imp
  all_goals first
    | exact isOpen_lt (by fun_prop) (by fun_prop)
    | exact (isClosed_eq (by fun_prop) (by fun_prop)).isOpen_compl

theorem isLocallyClosed_range_coords :
    IsLocallyClosed (Set.range (coords : BoundaryAnchoredInfinityData a m l u o →
      BoundaryAnchoredInfinityParameterSpace n m)) := by
  rw [range_coords]
  exact ⟨_, _, isOpen_openCoordinateConditions, isClosed_closedCoordinateConditions, rfl⟩

instance instLocallyCompactSpace : LocallyCompactSpace (BoundaryAnchoredInfinityData a m l u o) :=
  isEmbedding_coords.isInducing.locallyCompactSpace isLocallyClosed_range_coords

end BoundaryAnchoredInfinityData

/-- The actual nonnegative-radius domain for the prescribed boundary-anchored infinity data. -/
def BoundaryAnchoredInfinityDomain {n : ℕ} (a : Fin n) (m : ℕ)
    (l u : Fin (m + 1)) (o : Fin m) :=
  {x : BoundaryAnchoredInfinityData a m l u o × ℝ // x.1.AdmissibleScale x.2}

namespace BoundaryAnchoredInfinityDomain

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

instance instTopologicalSpace : TopologicalSpace (BoundaryAnchoredInfinityDomain a m l u o) :=
  inferInstanceAs (TopologicalSpace {x : BoundaryAnchoredInfinityData a m l u o × ℝ //
    x.1.AdmissibleScale x.2})

def datum (x : BoundaryAnchoredInfinityDomain a m l u o) : BoundaryAnchoredInfinityData a m l u o := x.val.1

def scale (x : BoundaryAnchoredInfinityDomain a m l u o) : ℝ := x.val.2

@[fun_prop] theorem continuous_datum :
    Continuous (datum : BoundaryAnchoredInfinityDomain a m l u o → _) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop] theorem continuous_scale :
    Continuous (scale : BoundaryAnchoredInfinityDomain a m l u o → ℝ) :=
  continuous_snd.comp continuous_subtype_val

@[fun_prop] theorem continuous_scaledInterior (j : Fin n) :
    Continuous (fun x : BoundaryAnchoredInfinityDomain a m l u o =>
      x.datum.scaledInterior x.scale j) := by
  unfold BoundaryAnchoredInfinityData.scaledInterior
  exact (Complex.continuous_ofReal.comp continuous_scale).mul
    ((BoundaryAnchoredInfinityData.continuous_shape_apply j).comp continuous_datum)

@[fun_prop] theorem continuous_scaledBoundary (j : Fin m) :
    Continuous (fun x : BoundaryAnchoredInfinityDomain a m l u o =>
      x.datum.scaledBoundary x.scale j) := by
  unfold BoundaryAnchoredInfinityData.scaledBoundary
  fun_prop

def zeroParameter (D : BoundaryAnchoredInfinityData a m l u o) : BoundaryAnchoredInfinityDomain a m l u o :=
  ⟨(D, 0), D.admissibleScale_zero⟩

@[simp] theorem datum_zeroParameter (D : BoundaryAnchoredInfinityData a m l u o) :
    (zeroParameter D).datum = D := rfl

@[simp] theorem scale_zeroParameter (D : BoundaryAnchoredInfinityData a m l u o) :
    (zeroParameter D).scale = 0 := rfl

@[fun_prop] theorem continuous_zeroParameter :
    Continuous (zeroParameter : BoundaryAnchoredInfinityData a m l u o → _) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

def ofSafeScale (D : BoundaryAnchoredInfinityData a m l u o) {ε : ℝ}
    (hε : D.IsSafeScale ε) (r : Set.Icc (0 : ℝ) ε) : BoundaryAnchoredInfinityDomain a m l u o :=
  ⟨(D, r), hε.admissibleScale r.property.1 r.property.2⟩

@[fun_prop] theorem continuous_ofSafeScale (D : BoundaryAnchoredInfinityData a m l u o) {ε : ℝ}
    (hε : D.IsSafeScale ε) : Continuous (ofSafeScale D hε) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

def openScaleConditions (x : BoundaryAnchoredInfinityData a m l u o × ℝ) : Prop :=
  ∀ j k, j < k → ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    x.2 * |x.1.boundaryVelocity k - x.1.boundaryVelocity j| <
      x.1.boundaryBase k - x.1.boundaryBase j

theorem admissibleScale_iff_openScaleConditions (x : BoundaryAnchoredInfinityData a m l u o × ℝ) :
    x.1.AdmissibleScale x.2 ↔ 0 ≤ x.2 ∧ openScaleConditions x :=
  ⟨fun hx => ⟨hx.nonneg, hx.boundary_separation⟩, fun hx => ⟨hx.1, hx.2⟩⟩

theorem isOpen_openScaleConditions :
    IsOpen {x : BoundaryAnchoredInfinityData a m l u o × ℝ | openScaleConditions x} := by
  unfold openScaleConditions
  repeat' first
    | apply isOpen_forall_finite; intro j
    | apply isOpen_const_imp
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem isLocallyClosed_admissibleScale :
    IsLocallyClosed {x : BoundaryAnchoredInfinityData a m l u o × ℝ | x.1.AdmissibleScale x.2} := by
  refine ⟨{x | openScaleConditions x}, {x | 0 ≤ x.2}, isOpen_openScaleConditions,
    isClosed_le continuous_const continuous_snd, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, admissibleScale_iff_openScaleConditions, and_comm]

instance instLocallyCompactSpace : LocallyCompactSpace (BoundaryAnchoredInfinityDomain a m l u o) := by
  change LocallyCompactSpace {x : BoundaryAnchoredInfinityData a m l u o × ℝ | x.1.AdmissibleScale x.2}
  exact isLocallyClosed_admissibleScale.locallyCompactSpace

instance : T2Space (BoundaryAnchoredInfinityDomain a m l u o) := by
  change T2Space {x : BoundaryAnchoredInfinityData a m l u o × ℝ | x.1.AdmissibleScale x.2}
  infer_instance

end BoundaryAnchoredInfinityDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
