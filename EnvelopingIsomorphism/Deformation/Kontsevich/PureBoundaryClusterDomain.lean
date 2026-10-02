import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterData
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterTopology

/-!
# Continuous pure external-cluster insertion with all geometric parameters varying

The parameter domain imposes only a fixed combinatorial cluster pattern and
explicit nonnegative-scale bounds. Interior, boundary, and velocity coordinates
vary together. Their insertion into the actual compact closure is continuous
through scale zero. At positive scale it is the encoded distinct-point
configuration constructed from the proved bounds.

The boundary endpoints have shape coordinates 0 and 1, so the proved identification formulas
remove translation and scale redundancy. Global coverage is a separate theorem.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

/-- The exact coordinate domain for one prescribed real cluster and consecutive boundary block. -/
def PureBoundaryClusterDomain {n : ℕ} (i : Fin n) (m : ℕ) (l u : Fin (m + 1)) (a b : Fin m) :=
  {x : PureBoundaryClusterData i m l u a b × ℝ // x.1.AdmissibleScale x.2}

namespace PureBoundaryClusterDomain

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

instance : TopologicalSpace (PureBoundaryClusterDomain i m l u a b) :=
  inferInstanceAs (TopologicalSpace {x : PureBoundaryClusterData i m l u a b × ℝ //
    x.1.AdmissibleScale x.2})

def datum (x : PureBoundaryClusterDomain i m l u a b) : PureBoundaryClusterData i m l u a b := x.val.1

def scale (x : PureBoundaryClusterDomain i m l u a b) : ℝ := x.val.2

@[fun_prop] theorem continuous_datum : Continuous (datum : PureBoundaryClusterDomain i m l u a b → _) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop] theorem continuous_scale : Continuous (scale : PureBoundaryClusterDomain i m l u a b → ℝ) :=
  continuous_snd.comp continuous_subtype_val

def coordinates (x : PureBoundaryClusterDomain i m l u a b) : CompactCoordinateSpace n m :=
  x.datum.resolvedCoordinates x.scale

@[fun_prop] theorem continuous_activeDifference (p : DoubledPair n m) :
    Continuous (fun x : PureBoundaryClusterDomain i m l u a b =>
      x.datum.activeDifference x.scale p) := by
  unfold PureBoundaryClusterData.activeDifference
  fun_prop

theorem activeDifference_ne_zero (x : PureBoundaryClusterDomain i m l u a b) (p : DoubledPair n m)
    (hp : ¬ pureBoundaryClusterPairCollapses l u p) :
    x.datum.activeDifference x.scale p ≠ 0 :=
  PureBoundaryClusterData.activeDifference_ne_zero x.property p
    (fun h => hp ((x.datum.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses p).mp h))

/-- All position, direction, and ratio entries vary continuously, including at scale zero. -/
@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : PureBoundaryClusterDomain i m l u a b → CompactCoordinateSpace n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    have h : Continuous (fun x : PureBoundaryClusterDomain i m l u a b =>
        x.datum.doubledBase (Sum.inl v) + (x.scale : ℂ) *
          x.datum.doubledVelocity (Sum.inl v)) := by fun_prop
    exact OnePoint.continuous_coe.comp h
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      change Continuous (fun x : PureBoundaryClusterDomain i m l u a b =>
        if x.datum.pairBase p = 0 then _ else _)
      simp only [PureBoundaryClusterData.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses]
      by_cases hp : pureBoundaryClusterPairCollapses l u p
      · simp only [if_pos hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne := x.datum.pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses p hp
        exact (continuousAt_complexPhase hne).comp
          (f := fun y : PureBoundaryClusterDomain i m l u a b => y.datum.pairVelocity p)
          (x := x) ((PureBoundaryClusterData.continuous_pairVelocity p).comp continuous_datum).continuousAt
      · simp only [if_neg hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        exact (continuousAt_complexPhase (x.activeDifference_ne_zero p hp)).comp
          (f := fun y : PureBoundaryClusterDomain i m l u a b =>
            y.datum.activeDifference y.scale p) (x := x)
          (continuous_activeDifference p).continuousAt
    · apply continuous_pi
      intro t
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      change Continuous (fun x : PureBoundaryClusterDomain i m l u a b =>
        if x.datum.pairBase p = 0 ∧
          x.datum.pairBase q = 0 then _ else _)
      simp only [PureBoundaryClusterData.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses]
      by_cases hpq : pureBoundaryClusterPairCollapses l u p ∧ pureBoundaryClusterPairCollapses l u q
      · simp only [if_pos hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.pairVelocity p = 0 ∧
            x.datum.pairVelocity q = 0) :=
          fun h => x.datum.pairVelocity_ne_zero_of_pureBoundaryClusterPairCollapses p hpq.1 h.1
        have hpair : Continuous (fun y : PureBoundaryClusterDomain i m l u a b =>
            (y.datum.pairVelocity p,
              y.datum.pairVelocity q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : PureBoundaryClusterDomain i m l u a b =>
            (y.datum.pairVelocity p,
              y.datum.pairVelocity q)) (x := x) hpair.continuousAt
      · simp only [if_neg hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.activeDifference x.scale p = 0 ∧
            x.datum.activeDifference x.scale q = 0) := by
          intro h
          by_cases hp : pureBoundaryClusterPairCollapses l u p
          · have hq : ¬ pureBoundaryClusterPairCollapses l u q := fun hq => hpq ⟨hp, hq⟩
            exact x.activeDifference_ne_zero q hq h.2
          · exact x.activeDifference_ne_zero p hp h.1
        have hpair : Continuous (fun y : PureBoundaryClusterDomain i m l u a b =>
            (y.datum.activeDifference y.scale p,
              y.datum.activeDifference y.scale q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : PureBoundaryClusterDomain i m l u a b =>
            (y.datum.activeDifference y.scale p,
              y.datum.activeDifference y.scale q)) (x := x) hpair.continuousAt

def insertion (x : PureBoundaryClusterDomain i m l u a b) : Compactification i m :=
  x.datum.compactInsertion x.property

@[fun_prop] theorem continuous_insertion :
    Continuous (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m) :=
  continuous_coordinates.subtype_mk _

theorem insertion_pos (x : PureBoundaryClusterDomain i m l u a b) (hr : 0 < x.scale) :
    x.insertion = compactificationEmbedding i
      (x.datum.normalized (x.property.isSafeScale hr) hr (le_refl x.scale)) :=
  x.datum.compactInsertion_pos x.property hr

def zeroParameter (D : PureBoundaryClusterData i m l u a b) : PureBoundaryClusterDomain i m l u a b :=
  ⟨(D, 0), D.admissibleScale_zero⟩

@[simp] theorem insertion_zeroParameter (D : PureBoundaryClusterData i m l u a b) :
    (zeroParameter D).insertion = D.boundaryPoint := rfl

/-- Every datum provides a genuine interval of admissible radial parameters. -/
def ofSafeScale (D : PureBoundaryClusterData i m l u a b) {ε : ℝ}
    (hε : D.IsSafeScale ε) (r : Set.Icc (0 : ℝ) ε) : PureBoundaryClusterDomain i m l u a b :=
  ⟨(D, r), hε.admissibleScale r.property.1 r.property.2⟩

@[fun_prop] theorem continuous_ofSafeScale (D : PureBoundaryClusterData i m l u a b) {ε : ℝ}
    (hε : D.IsSafeScale ε) : Continuous (ofSafeScale D hε) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The left endpoint and unit endpoint-gap normalization removes all parameter redundancy. -/
theorem insertion_injective :
    Function.Injective (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m) := by
  intro x y hxy
  have h : x.datum.resolvedCoordinates x.scale = y.datum.resolvedCoordinates y.scale :=
    congrArg Subtype.val hxy
  have hcr := PureBoundaryClusterData.center_scale_eq_of_coordinates_eq h
  have hD : x.datum = y.datum := PureBoundaryClusterData.ext hcr.1
    (PureBoundaryClusterData.interior_eq_of_coordinates_eq h)
    (PureBoundaryClusterData.boundaryBase_eq_of_coordinates_eq h)
    (PureBoundaryClusterData.boundaryVelocity_eq_of_coordinates_eq h)
  apply Subtype.ext
  exact Prod.ext hD hcr.2

end PureBoundaryClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
