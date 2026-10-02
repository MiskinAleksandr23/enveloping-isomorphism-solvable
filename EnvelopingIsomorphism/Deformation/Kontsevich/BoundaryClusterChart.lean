import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPattern
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterTopology

/-!
# Continuous finite real-cluster insertion with all geometric parameters varying

The parameter domain imposes only a fixed combinatorial cluster pattern and
explicit nonnegative-scale bounds. Interior, boundary, and velocity coordinates
vary together. Their insertion into the actual compact closure is continuous
through scale zero. At positive scale it is the encoded distinct-point
configuration constructed from the proved bounds.

The shape anchor has coordinate I, so the proved coordinate-identification formulas
remove translation and scale redundancy. Global coverage is a separate theorem.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

/-- The exact coordinate domain for one prescribed real cluster and consecutive boundary block. -/
def BoundaryClusterDomain {n : ℕ} (i a : Fin n) (m : ℕ) (S : Finset (Fin n)) (l u : Fin (m + 1)) :=
  {x : BoundaryClusterData i a m S l u × ℝ // x.1.AdmissibleScale x.2}

namespace BoundaryClusterDomain

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

instance : TopologicalSpace (BoundaryClusterDomain i a m S l u) :=
  inferInstanceAs (TopologicalSpace {x : BoundaryClusterData i a m S l u × ℝ //
    x.1.AdmissibleScale x.2})

def datum (x : BoundaryClusterDomain i a m S l u) : BoundaryClusterData i a m S l u := x.val.1

def scale (x : BoundaryClusterDomain i a m S l u) : ℝ := x.val.2

@[fun_prop] theorem continuous_datum : Continuous (datum : BoundaryClusterDomain i a m S l u → _) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop] theorem continuous_scale : Continuous (scale : BoundaryClusterDomain i a m S l u → ℝ) :=
  continuous_snd.comp continuous_subtype_val

def coordinates (x : BoundaryClusterDomain i a m S l u) : CompactCoordinateSpace n m :=
  x.datum.resolvedCoordinates x.scale

@[fun_prop] theorem continuous_activeDifference (p : DoubledPair n m) :
    Continuous (fun x : BoundaryClusterDomain i a m S l u =>
      x.datum.activeDifference x.scale p) := by
  unfold BoundaryClusterData.activeDifference
  fun_prop

theorem activeDifference_ne_zero (x : BoundaryClusterDomain i a m S l u) (p : DoubledPair n m)
    (hp : ¬ boundaryClusterPairCollapses S l u p) :
    x.datum.activeDifference x.scale p ≠ 0 :=
  BoundaryClusterData.activeDifference_ne_zero x.property p
    (fun h => hp ((x.datum.pairBase_eq_zero_iff_boundaryClusterPairCollapses p).mp h))

/-- All position, direction, and ratio entries vary continuously, including at scale zero. -/
@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : BoundaryClusterDomain i a m S l u → CompactCoordinateSpace n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    have h : Continuous (fun x : BoundaryClusterDomain i a m S l u =>
        x.datum.doubledBase (Sum.inl v) + (x.scale : ℂ) *
          x.datum.doubledVelocity (Sum.inl v)) := by fun_prop
    exact OnePoint.continuous_coe.comp h
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      change Continuous (fun x : BoundaryClusterDomain i a m S l u =>
        if x.datum.pairBase p = 0 then _ else _)
      simp only [BoundaryClusterData.pairBase_eq_zero_iff_boundaryClusterPairCollapses]
      by_cases hp : boundaryClusterPairCollapses S l u p
      · simp only [if_pos hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne := x.datum.pairVelocity_ne_zero_of_boundaryClusterPairCollapses p hp
        exact (continuousAt_complexPhase hne).comp
          (f := fun y : BoundaryClusterDomain i a m S l u => y.datum.pairVelocity p)
          (x := x) ((BoundaryClusterData.continuous_pairVelocity p).comp continuous_datum).continuousAt
      · simp only [if_neg hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        exact (continuousAt_complexPhase (x.activeDifference_ne_zero p hp)).comp
          (f := fun y : BoundaryClusterDomain i a m S l u =>
            y.datum.activeDifference y.scale p) (x := x)
          (continuous_activeDifference p).continuousAt
    · apply continuous_pi
      intro t
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      change Continuous (fun x : BoundaryClusterDomain i a m S l u =>
        if x.datum.pairBase p = 0 ∧
          x.datum.pairBase q = 0 then _ else _)
      simp only [BoundaryClusterData.pairBase_eq_zero_iff_boundaryClusterPairCollapses]
      by_cases hpq : boundaryClusterPairCollapses S l u p ∧ boundaryClusterPairCollapses S l u q
      · simp only [if_pos hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.pairVelocity p = 0 ∧
            x.datum.pairVelocity q = 0) :=
          fun h => x.datum.pairVelocity_ne_zero_of_boundaryClusterPairCollapses p hpq.1 h.1
        have hpair : Continuous (fun y : BoundaryClusterDomain i a m S l u =>
            (y.datum.pairVelocity p,
              y.datum.pairVelocity q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : BoundaryClusterDomain i a m S l u =>
            (y.datum.pairVelocity p,
              y.datum.pairVelocity q)) (x := x) hpair.continuousAt
      · simp only [if_neg hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.activeDifference x.scale p = 0 ∧
            x.datum.activeDifference x.scale q = 0) := by
          intro h
          by_cases hp : boundaryClusterPairCollapses S l u p
          · have hq : ¬ boundaryClusterPairCollapses S l u q := fun hq => hpq ⟨hp, hq⟩
            exact x.activeDifference_ne_zero q hq h.2
          · exact x.activeDifference_ne_zero p hp h.1
        have hpair : Continuous (fun y : BoundaryClusterDomain i a m S l u =>
            (y.datum.activeDifference y.scale p,
              y.datum.activeDifference y.scale q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : BoundaryClusterDomain i a m S l u =>
            (y.datum.activeDifference y.scale p,
              y.datum.activeDifference y.scale q)) (x := x) hpair.continuousAt

def insertion (x : BoundaryClusterDomain i a m S l u) : Compactification i m :=
  x.datum.compactInsertion x.property

@[fun_prop] theorem continuous_insertion :
    Continuous (insertion : BoundaryClusterDomain i a m S l u → Compactification i m) :=
  continuous_coordinates.subtype_mk _

theorem insertion_pos (x : BoundaryClusterDomain i a m S l u) (hr : 0 < x.scale) :
    x.insertion = compactificationEmbedding i
      (x.datum.normalized (x.property.isSafeScale hr) hr (le_refl x.scale)) :=
  x.datum.compactInsertion_pos x.property hr

def zeroParameter (D : BoundaryClusterData i a m S l u) : BoundaryClusterDomain i a m S l u :=
  ⟨(D, 0), D.admissibleScale_zero⟩

@[simp] theorem insertion_zeroParameter (D : BoundaryClusterData i a m S l u) :
    (zeroParameter D).insertion = D.boundaryPoint := rfl

/-- Every datum provides a genuine interval of admissible radial parameters. -/
def ofSafeScale (D : BoundaryClusterData i a m S l u) {ε : ℝ}
    (hε : D.IsSafeScale ε) (r : Set.Icc (0 : ℝ) ε) : BoundaryClusterDomain i a m S l u :=
  ⟨(D, r), hε.admissibleScale r.property.1 r.property.2⟩

@[fun_prop] theorem continuous_ofSafeScale (D : BoundaryClusterData i a m S l u) {ε : ℝ}
    (hε : D.IsSafeScale ε) : Continuous (ofSafeScale D hε) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The real-center and shape-anchor normalization removes all parameter redundancy. -/
theorem insertion_injective :
    Function.Injective (insertion : BoundaryClusterDomain i a m S l u → Compactification i m) := by
  intro x y hxy
  have h : x.datum.resolvedCoordinates x.scale = y.datum.resolvedCoordinates y.scale :=
    congrArg Subtype.val hxy
  have hcr := BoundaryClusterData.center_scale_eq_of_coordinates_eq h
  have hD : x.datum = y.datum := BoundaryClusterData.ext hcr.1
    (BoundaryClusterData.base_eq_of_coordinates_eq h)
    (BoundaryClusterData.velocity_eq_of_coordinates_eq h)
    (BoundaryClusterData.boundaryBase_eq_of_coordinates_eq h)
    (BoundaryClusterData.boundaryVelocity_eq_of_coordinates_eq h)
  apply Subtype.ext
  exact Prod.ext hD hcr.2

end BoundaryClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
