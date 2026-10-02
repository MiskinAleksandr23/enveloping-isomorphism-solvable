import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterPhase
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterPattern
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterTopology

/-!
# Continuous single-cluster insertion with all geometric parameters varying

The parameter domain imposes only a fixed combinatorial cluster pattern and
explicit nonnegative-scale bounds. Interior, boundary, and velocity coordinates
vary together. Their insertion into the actual compact closure is continuous
through scale zero. At positive scale it is the encoded distinct-point
configuration constructed from the proved bounds.

These are redundant geometric parameters, not yet a normalized forest atlas.
No injectivity of this parameter map, openness of its image, or global coverage
is claimed here.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

/-- The exact coordinate domain for one prescribed nonempty interior cluster. -/
def InteriorClusterDomain {n : ℕ} (i : Fin n) (m : ℕ) (S : Finset (Fin n)) :=
  {x : SingleInteriorCluster i m S × ℝ // x.1.toInteriorCollisionData.AdmissibleScale x.2}

namespace InteriorClusterDomain

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

instance : TopologicalSpace (InteriorClusterDomain i m S) :=
  inferInstanceAs (TopologicalSpace {x : SingleInteriorCluster i m S × ℝ //
    x.1.toInteriorCollisionData.AdmissibleScale x.2})

def datum (x : InteriorClusterDomain i m S) : SingleInteriorCluster i m S := x.val.1

def scale (x : InteriorClusterDomain i m S) : ℝ := x.val.2

@[fun_prop] theorem continuous_datum : Continuous (datum : InteriorClusterDomain i m S → _) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop] theorem continuous_scale : Continuous (scale : InteriorClusterDomain i m S → ℝ) :=
  continuous_snd.comp continuous_subtype_val

def coordinates (x : InteriorClusterDomain i m S) : CompactCoordinateSpace n m :=
  x.datum.toInteriorCollisionData.resolvedCoordinates x.scale

@[fun_prop] theorem continuous_activeDifference (p : DoubledPair n m) :
    Continuous (fun x : InteriorClusterDomain i m S =>
      x.datum.toInteriorCollisionData.activeDifference x.scale p) := by
  unfold InteriorCollisionData.activeDifference
  fun_prop

theorem activeDifference_ne_zero (x : InteriorClusterDomain i m S) (p : DoubledPair n m)
    (hp : ¬ clusterPairCollapses S p) :
    x.datum.toInteriorCollisionData.activeDifference x.scale p ≠ 0 :=
  InteriorCollisionData.activeDifference_ne_zero x.property p
    (fun h => hp ((x.datum.pairBase_eq_zero_iff_clusterPairCollapses p).mp h))

/-- All position, direction, and ratio entries vary continuously, including at scale zero. -/
@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates : InteriorClusterDomain i m S → CompactCoordinateSpace n m) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    have h : Continuous (fun x : InteriorClusterDomain i m S =>
        x.datum.toInteriorCollisionData.doubledBase (Sum.inl v) + (x.scale : ℂ) *
          x.datum.toInteriorCollisionData.doubledVelocity (Sum.inl v)) := by fun_prop
    exact OnePoint.continuous_coe.comp h
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      change Continuous (fun x : InteriorClusterDomain i m S =>
        if x.datum.toInteriorCollisionData.pairBase p = 0 then _ else _)
      simp only [SingleInteriorCluster.pairBase_eq_zero_iff_clusterPairCollapses]
      by_cases hp : clusterPairCollapses S p
      · simp only [if_pos hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne := x.datum.pairVelocity_ne_zero_of_clusterPairCollapses p hp
        exact (continuousAt_complexPhase hne).comp
          (f := fun y : InteriorClusterDomain i m S => y.datum.toInteriorCollisionData.pairVelocity p)
          (x := x) ((SingleInteriorCluster.continuous_pairVelocity p).comp continuous_datum).continuousAt
      · simp only [if_neg hp]
        apply continuous_iff_continuousAt.mpr
        intro x
        exact (continuousAt_complexPhase (x.activeDifference_ne_zero p hp)).comp
          (f := fun y : InteriorClusterDomain i m S =>
            y.datum.toInteriorCollisionData.activeDifference y.scale p) (x := x)
          (continuous_activeDifference p).continuousAt
    · apply continuous_pi
      intro t
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      change Continuous (fun x : InteriorClusterDomain i m S =>
        if x.datum.toInteriorCollisionData.pairBase p = 0 ∧
          x.datum.toInteriorCollisionData.pairBase q = 0 then _ else _)
      simp only [SingleInteriorCluster.pairBase_eq_zero_iff_clusterPairCollapses]
      by_cases hpq : clusterPairCollapses S p ∧ clusterPairCollapses S q
      · simp only [if_pos hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.toInteriorCollisionData.pairVelocity p = 0 ∧
            x.datum.toInteriorCollisionData.pairVelocity q = 0) :=
          fun h => x.datum.pairVelocity_ne_zero_of_clusterPairCollapses p hpq.1 h.1
        have hpair : Continuous (fun y : InteriorClusterDomain i m S =>
            (y.datum.toInteriorCollisionData.pairVelocity p,
              y.datum.toInteriorCollisionData.pairVelocity q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : InteriorClusterDomain i m S =>
            (y.datum.toInteriorCollisionData.pairVelocity p,
              y.datum.toInteriorCollisionData.pairVelocity q)) (x := x) hpair.continuousAt
      · simp only [if_neg hpq]
        apply continuous_iff_continuousAt.mpr
        intro x
        have hne : ¬ (x.datum.toInteriorCollisionData.activeDifference x.scale p = 0 ∧
            x.datum.toInteriorCollisionData.activeDifference x.scale q = 0) := by
          intro h
          by_cases hp : clusterPairCollapses S p
          · have hq : ¬ clusterPairCollapses S q := fun hq => hpq ⟨hp, hq⟩
            exact x.activeDifference_ne_zero q hq h.2
          · exact x.activeDifference_ne_zero p hp h.1
        have hpair : Continuous (fun y : InteriorClusterDomain i m S =>
            (y.datum.toInteriorCollisionData.activeDifference y.scale p,
              y.datum.toInteriorCollisionData.activeDifference y.scale q)) := by fun_prop
        simpa only [Function.comp_def] using (continuousAt_normalizedNormRatio _ _ hne).comp
          (f := fun y : InteriorClusterDomain i m S =>
            (y.datum.toInteriorCollisionData.activeDifference y.scale p,
              y.datum.toInteriorCollisionData.activeDifference y.scale q)) (x := x) hpair.continuousAt

def insertion (x : InteriorClusterDomain i m S) : Compactification i m :=
  x.datum.toInteriorCollisionData.compactInsertion x.property

@[fun_prop] theorem continuous_insertion :
    Continuous (insertion : InteriorClusterDomain i m S → Compactification i m) :=
  continuous_coordinates.subtype_mk _

theorem insertion_pos (x : InteriorClusterDomain i m S) (hr : 0 < x.scale) :
    x.insertion = compactificationEmbedding i
      (x.datum.toInteriorCollisionData.normalized (x.property.isSafeScale hr) hr (le_refl x.scale)) :=
  x.datum.toInteriorCollisionData.compactInsertion_pos x.property hr

def zeroParameter (D : SingleInteriorCluster i m S) : InteriorClusterDomain i m S :=
  ⟨(D, 0), D.toInteriorCollisionData.admissibleScale_zero⟩

@[simp] theorem insertion_zeroParameter (D : SingleInteriorCluster i m S) :
    (zeroParameter D).insertion = D.toInteriorCollisionData.boundaryPoint := rfl

/-- Every datum provides a genuine interval of admissible radial parameters. -/
def ofSafeScale (D : SingleInteriorCluster i m S) {ε : ℝ}
    (hε : D.toInteriorCollisionData.IsSafeScale ε) (r : Set.Icc (0 : ℝ) ε) : InteriorClusterDomain i m S :=
  ⟨(D, r), hε.admissibleScale r.property.1 r.property.2⟩

@[fun_prop] theorem continuous_ofSafeScale (D : SingleInteriorCluster i m S) {ε : ℝ}
    (hε : D.toInteriorCollisionData.IsSafeScale ε) : Continuous (ofSafeScale D hε) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

end InteriorClusterDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
