import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterChart
import EnvelopingIsomorphism.Deformation.Kontsevich.RelativeCoordinateIdentification

/-!
# Removing translation and scale redundancy from a single-cluster insertion

Two fixed cluster labels normalize the internal shape: the first velocity is
zero and the second has norm one. The actual compact direction and triple-ratio
coordinates recover every velocity, and finite positions recover the radius,
coarse positions, and real boundary points.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology Set

def NormalizedInteriorClusterSlice {n : ℕ} (i : Fin n) (m : ℕ) (S : Finset (Fin n))
    (a b : Fin n) :=
  {x : InteriorClusterDomain i m S // x.datum.velocity a = 0 ∧ ‖x.datum.velocity b‖ = 1}

namespace NormalizedInteriorClusterSlice

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

instance : TopologicalSpace (NormalizedInteriorClusterSlice i m S a b) :=
  inferInstanceAs (TopologicalSpace {x : InteriorClusterDomain i m S //
    x.datum.velocity a = 0 ∧ ‖x.datum.velocity b‖ = 1})

def insertion (x : NormalizedInteriorClusterSlice i m S a b) : Compactification i m := x.val.insertion

theorem anchor_eq_global_of_mem (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hi : i ∈ S) : a = i :=
  x.val.datum.separated a i (x.val.datum.base_eq_of_mem ha hi)
    (x.property.1.trans x.val.datum.velocity_normalized.symm)

@[fun_prop] theorem continuous_insertion :
    Continuous (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m) :=
  InteriorClusterDomain.continuous_insertion.comp continuous_subtype_val

def scaledPosition (x : NormalizedInteriorClusterSlice i m S a b) (j : Fin n) : ℂ :=
  (x.val.datum.base j : ℂ) + (x.val.scale : ℂ) * x.val.datum.velocity j

theorem insertion_position (x : NormalizedInteriorClusterSlice i m S a b) (j : Fin n) :
    x.insertion.val.1 (Sum.inl j) = (x.scaledPosition j : OnePoint ℂ) := rfl

theorem insertion_boundary (x : NormalizedInteriorClusterSlice i m S a b) (j : Fin m) :
    x.insertion.val.1 (Sum.inr j) = ((x.val.datum.boundary j : ℂ) : OnePoint ℂ) := by
  simp [insertion, InteriorClusterDomain.insertion, InteriorCollisionData.compactInsertion,
    InteriorCollisionData.resolvedCoordinates, InteriorCollisionData.doubledBase,
    InteriorCollisionData.doubledVelocity]

theorem norm_reference_displacement (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hb : b ∈ S) :
    ‖x.scaledPosition b - x.scaledPosition a‖ = x.val.scale := by
  have hbase := x.val.datum.base_eq_of_mem hb ha
  simp only [scaledPosition, hbase, x.property.1, mul_zero, add_zero, add_sub_cancel_left,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, x.property.2, mul_one]
  exact abs_of_nonneg x.val.property.nonneg

def shapePair (a j : Fin n) (hja : j ≠ a) : DoubledPair n m :=
  harmonicNumeratorPair a (Sum.inl j) (fun h => hja (Sum.inl.inj h))

def shapeTriple (a b j : Fin n) (hja : j ≠ a) (hba : b ≠ a) : DoubledTriple n m :=
  ⟨(Sum.inl (Sum.inl a), Sum.inl (Sum.inl j), Sum.inl (Sum.inl b)),
    (fun h => hja (Sum.inl.inj (Sum.inl.inj h)).symm),
    (fun h => hba (Sum.inl.inj (Sum.inl.inj h)).symm)⟩

/-- Relative directions recover the velocity directions at every nonnegative scale. -/
theorem insertion_shape_direction (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (j : Fin n) (hj : j ∈ S) (hja : j ≠ a) :
    x.insertion.val.2.1 (shapePair (m := m) a j hja) = complexPhase (x.val.datum.velocity j) := by
  have hp : x.val.datum.toInteriorCollisionData.pairBase (shapePair (m := m) a j hja) = 0 := by
    change (x.val.datum.base j : ℂ) - (x.val.datum.base a : ℂ) = 0
    simp only [x.val.datum.base_eq_of_mem hj ha, sub_self]
  change (if x.val.datum.toInteriorCollisionData.pairBase _ = 0 then _ else _) = _
  rw [if_pos hp]
  change complexPhase (x.val.datum.velocity j - x.val.datum.velocity a) = _
  rw [x.property.1, sub_zero]

/-- The reference velocity has length one, so the stored triple ratio is the identification ratio. -/
theorem insertion_shape_ratio (x : NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hb : b ∈ S) (j : Fin n) (hj : j ∈ S) (hja : j ≠ a) (hba : b ≠ a) :
    (x.insertion.val.2.2 (shapeTriple (m := m) a b j hja hba) : ℝ) =
      unitNormRatio (x.val.datum.velocity j) := by
  have hp : x.val.datum.toInteriorCollisionData.pairBase (shapePair (m := m) a j hja) = 0 := by
    change (x.val.datum.base j : ℂ) - (x.val.datum.base a : ℂ) = 0
    simp only [x.val.datum.base_eq_of_mem hj ha, sub_self]
  have hq : x.val.datum.toInteriorCollisionData.pairBase (shapePair (m := m) a b hba) = 0 := by
    change (x.val.datum.base b : ℂ) - (x.val.datum.base a : ℂ) = 0
    simp only [x.val.datum.base_eq_of_mem hb ha, sub_self]
  change ((if x.val.datum.toInteriorCollisionData.pairBase _ = 0 ∧
    x.val.datum.toInteriorCollisionData.pairBase _ = 0 then _ else _) : Set.Icc (0 : ℝ) 1).val = _
  rw [if_pos ⟨hp, hq⟩]
  change ‖x.val.datum.velocity j - x.val.datum.velocity a‖ /
    (‖x.val.datum.velocity j - x.val.datum.velocity a‖ +
      ‖x.val.datum.velocity b - x.val.datum.velocity a‖) = _
  simp only [x.property.1, sub_zero, x.property.2, unitNormRatio]

theorem velocity_eq_of_insertion_eq {x y : NormalizedInteriorClusterSlice i m S a b}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hxy : x.insertion = y.insertion) :
    x.val.datum.velocity = y.val.datum.velocity := by
  funext j
  by_cases hj : j ∈ S
  · by_cases hja : j = a
    · simp only [hja, x.property.1, y.property.1]
    · apply complex_eq_of_phase_unitNormRatio
      · have h := congrArg (fun z : Compactification i m => z.val.2.1 (shapePair (m := m) a j hja)) hxy
        simpa only [insertion_shape_direction x ha j hj hja, insertion_shape_direction y ha j hj hja] using h
      · have h := congrArg (fun z : Compactification i m =>
          (z.val.2.2 (shapeTriple (m := m) a b j hja hba) : ℝ)) hxy
        simpa only [insertion_shape_ratio x ha hb j hj hja hba,
          insertion_shape_ratio y ha hb j hj hja hba] using h
  · rw [x.val.datum.velocity_zero_off j hj, y.val.datum.velocity_zero_off j hj]

theorem scaledPosition_eq_of_insertion_eq {x y : NormalizedInteriorClusterSlice i m S a b}
    (hxy : x.insertion = y.insertion) (j : Fin n) : x.scaledPosition j = y.scaledPosition j := by
  apply OnePoint.coe_injective
  exact congrArg (fun z : Compactification i m => z.val.1 (Sum.inl j)) hxy

theorem scale_eq_of_insertion_eq {x y : NormalizedInteriorClusterSlice i m S a b}
    (ha : a ∈ S) (hb : b ∈ S) (hxy : x.insertion = y.insertion) : x.val.scale = y.val.scale := by
  rw [← x.norm_reference_displacement ha hb, ← y.norm_reference_displacement ha hb,
    scaledPosition_eq_of_insertion_eq hxy a, scaledPosition_eq_of_insertion_eq hxy b]

/-- The normalized single-cluster insertion is injective, including at scale zero. -/
theorem insertion_injective (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    Function.Injective (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m) := by
  intro x y hxy
  have hv := velocity_eq_of_insertion_eq ha hb hba hxy
  have hr := scale_eq_of_insertion_eq ha hb hxy
  have hbase : x.val.datum.base = y.val.datum.base := by
    funext j
    apply UpperHalfPlane.ext
    have h := scaledPosition_eq_of_insertion_eq hxy j
    simp only [scaledPosition, hr, hv] at h
    exact add_right_cancel h
  have hboundary : x.val.datum.boundary = y.val.datum.boundary := by
    funext j
    apply Complex.ofReal_injective
    apply OnePoint.coe_injective
    have h := congrArg (fun z : Compactification i m => z.val.1 (Sum.inr j)) hxy
    simpa only [insertion_boundary] using h
  have hD : x.val.datum = y.val.datum :=
    SingleInteriorCluster.ext (InteriorCollisionData.ext hbase hv hboundary)
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hD hr

end NormalizedInteriorClusterSlice

end EnvelopingIsomorphism.Deformation.Kontsevich
