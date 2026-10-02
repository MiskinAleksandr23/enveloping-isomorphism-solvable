import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFullOverlap

/-! Actual reciprocal outside-coordinate extraction on the positive infinity
collar. The forest-to-simple map is identified with explicit physical
coordinates before any orientation multiplier is considered. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestNormalScale
open InfinityForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

private theorem normalize_affine (c t : ℝ) (u v : ℂ) (ht : t ≠ 0) (hu : u.im ≠ 0) :
    RealForestSimpleCluster.normalize ((c : ℂ) + (t : ℂ) * u) ((c : ℂ) + (t : ℂ) * v) =
      RealForestSimpleCluster.normalize u v := by
  unfold RealForestSimpleCluster.normalize
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht, Complex.ofReal_ne_zero.mpr hu]
  <;> ring

include ho in
theorem normalize_position_inside (y : Coord (r+1))
    (ht : y (axis hdim x o) * parentScale hdim x o y ≠ 0)
    (hu : shapeHeight hdim x o 0 y ≠ 0) (j : Configuration.DoubledLabel (n+1) m)
    (hj : j ∈ (RealForestCoarsePositions.node x o).val) :
    RealForestSimpleCluster.normalize (position hdim x (Sum.inl (Sum.inl 0)) y) (position hdim x j y) =
      RealForestSimpleCluster.normalize (shapePosition hdim x o (Sum.inl (Sum.inl 0)) y)
        (shapePosition hdim x o j y) := by
  rw [position_inside_factor hdim x o y _ hj,
    position_inside_factor hdim x o y _
      ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp (InfinityForestSimpleCluster.interior_mem x o ho 0)),
    nodePosition_real hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) y]
  simpa only [Complex.real_smul] using normalize_affine (nodePosition hdim x o y).re
    (y (axis hdim x o) * parentScale hdim x o y) _ _ ht hu

def physicalFace : GraphForms.Coordinates n m →L[ℝ] InfinityForestSimpleOverlap.Face x o q :=
  LinearMap.toContinuousLinearMap {
    toFun p := (fun j ↦ p.1 (j.val.pred j.property), fun j ↦ p.2 j.val)
    map_add' p q := rfl
    map_smul' c p := rfl }

include ho hall in
theorem faceCoordinates_eq_physical (y : Coord (r+1))
    (ht : y (axis hdim x o) * parentScale hdim x o y ≠ 0)
    (hu : shapeHeight hdim x o 0 y ≠ 0) :
    InfinityForestFullOverlap.faceCoordinates hdim x o q y =
      physicalFace x o q (ForestPositiveChartSmooth.forwardCoordinates 0 x
        ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)) := by
  apply Prod.ext
  · funext j
    have h := normalize_position_inside hdim x o ho y ht hu (Sum.inl (Sum.inl j.val))
      ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp (InfinityForestSimpleCluster.interior_mem x o ho j.val))
    change _ = (ForestPositiveChartSmooth.forwardCoordinates 0 x
      ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).1 (j.val.pred j.property)
    unfold ForestPositiveChartSmooth.forwardCoordinates
    simp only [Equiv.swap_self, Equiv.refl_apply, Fin.succ_pred]
    exact h.symm
  · funext j
    have h := congrArg Complex.re (normalize_position_inside hdim x o ho y ht hu (Sum.inl (Sum.inr j.val))
      ((RealForestCoarsePositions.boundary_mem_node_iff x o
        (RealForestCoarsePositions.infinity_isFixed x o ho) j.val).mpr (hall j.val j.property)))
    simp only [RealForestSimpleCluster.normalize_re] at h
    exact h.symm

def reciprocalExtraction (p : GraphForms.Coordinates n m) : Coord (r+1) :=
  faceEmbedding 0 (|p.2 q|⁻¹)
    (InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall (physicalFace x o q p))

include ho hq hne hall in
/-- Literal physical extraction of the full collar: radius is the reciprocal
absolute outside boundary coordinate; the remaining coordinates are shapes. -/
theorem map_eq_reciprocalExtraction (y : Coord (r+1))
    (ht : y (axis hdim x o) * parentScale hdim x o y ≠ 0)
    (hu : shapeHeight hdim x o 0 y ≠ 0) (hh : 0 < height hdim x 0 y) :
    InfinityForestFullOverlap.map hdim x o q ho hq hne hall y =
      reciprocalExtraction hdim x o q ho hq hne hall
        (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)) := by
  rw [InfinityForestFullOverlap.map, faceCoordinates_eq_physical hdim x o q ho hall y ht hu]
  unfold reciprocalExtraction
  congr 1
  rw [InfinityForestNormalScale.simpleRadius_eq_height_ratio hdim x o q ho y]
  change height hdim x 0 y / |InfinityForestNormalScale.offset hdim x q y| =
    |InfinityForestNormalScale.offset hdim x q y / height hdim x 0 y|⁻¹
  rw [abs_div, abs_of_pos hh, inv_div]

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
