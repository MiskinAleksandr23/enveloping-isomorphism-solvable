import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestNormalScale
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionCoordinates

/-! Actual full proper-real collar coordinates, including the positive native
normal scale and the physical insertion in outside-anchor normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullOverlap
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (normalize normalizeReal lower upper)
open RealForestNormalScale BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1))

def normalizedPosition (j : Fin (n+1)) (y : Coord (r+1)) : ℂ :=
  RealForestSimpleCluster.normalize (position hdim x (Sum.inl (Sum.inl b)) y)
    (position hdim x (Sum.inl (Sum.inl j)) y)

def normalizedShape (j : Fin (n+1)) (y : Coord (r+1)) : ℂ :=
  RealForestSimpleCluster.normalize (shapePosition hdim x o (Sum.inl (Sum.inl a)) y)
    (shapePosition hdim x o (Sum.inl (Sum.inl j)) y)

def normalizedBoundary (j : Fin m) (y : Coord (r+1)) : ℝ :=
  normalizeReal (position hdim x (Sum.inl (Sum.inl b)) y) (position hdim x (Sum.inl (Sum.inr j)) y).re

def normalizedBoundaryShape (j : Fin m) (y : Coord (r+1)) : ℝ :=
  normalizeReal (shapePosition hdim x o (Sum.inl (Sum.inl a)) y)
    (shapePosition hdim x o (Sum.inl (Sum.inr j)) y).re

def center (y : Coord (r+1)) : ℝ :=
  normalizeReal (position hdim x (Sum.inl (Sum.inl b)) y) (position hdim x (Sum.inl (Sum.inl a)) y).re

def overlap (y : Coord (r+1)) : BoundaryClusterFreeCoordinates b a (labelsSet x o) m :=
  (fun j ↦ normalizedPosition hdim x b j.val y,
    fun j ↦ normalizedShape hdim x o a j.val y,
    fun j ↦ if j ∈ boundaryClusterBlock (lower x o) (upper x o) then normalizedBoundaryShape hdim x o a j y
      else normalizedBoundary hdim x b j y,
    center hdim x a b y, simpleRadius hdim x o a b y)

@[simp] theorem overlap_radius (y : Coord (r+1)) :
    (overlap hdim x o a b y).radius = simpleRadius hdim x o a b y := rfl

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

include ho ha in
theorem inside_anchor_height (y : Coord (r+1)) :
    height hdim x a y = y (axis hdim x o) * parentScale hdim x o y * shapeHeight hdim x o a y := by
  have h := congrArg Complex.im (position_inside_factor hdim x o y (Sum.inl (Sum.inl a))
    ((mem_interiorLabels 0 x _ _).mp ha))
  rw [nodePosition_real hdim x o ho y] at h
  simpa only [height, shapeHeight, Complex.add_im, Complex.ofReal_im, zero_add,
    Complex.real_smul, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] using h

include ho ha in
theorem simpleRadius_eq_height (y : Coord (r+1)) :
    simpleRadius hdim x o a b y = height hdim x a y / height hdim x b y := by
  rw [inside_anchor_height hdim x o a ho ha y]
  unfold simpleRadius normalScale
  ring

include ho ha in
theorem overlap_face (z : ForestRadialFaceLocalization.source hdim x o) :
    overlap hdim x o a b (facePoint hdim x o z.val) =
      BoundaryClusterFreeCoordinates.faceEmbedding (RealForestSimpleCoordinates.coordinates hdim x o a b z.val) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · change normalizeReal _ (PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inl a))).re = _
          rw [RealForestCoarsePositions.positions_inside hdim x o ho z _ ((mem_interiorLabels 0 x _ _).mp ha)]
          rfl
        · exact simpleRadius_face hdim x o a b z.val

include ho ha hb in
theorem contDiffAt_overlap (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (overlap hdim x o a b) (facePoint hdim x o z.val) := by
  have hB := (contDiff_position hdim x (Sum.inl (Sum.inl b))).contDiffAt (x := facePoint hdim x o z.val)
  have hA := (contDiff_shapePosition hdim x o (Sum.inl (Sum.inl a))).contDiffAt (x := facePoint hdim x o z.val)
  have hpB := RealForestSimpleCluster.coarseAnchor_pos hdim x o ho b hb z
  have hpA := RealForestSimpleCluster.shapeAnchor_pos hdim x o ho a ha z
  unfold overlap
  refine (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hB
    (contDiff_position hdim x _).contDiffAt hpB).prodMk ?_
  refine (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hA
    (contDiff_shapePosition hdim x o _).contDiffAt hpA).prodMk ?_
  refine (contDiffAt_pi.mpr fun j ↦ ?_).prodMk ?_
  · unfold normalizedBoundaryShape normalizedBoundary
    split_ifs
    · exact RealForestSimpleCoordinates.smooth_normalizeReal hA
        (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt) hpA
    · exact RealForestSimpleCoordinates.smooth_normalizeReal hB
        (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_position hdim x _).contDiffAt) hpB
  · refine (RealForestSimpleCoordinates.smooth_normalizeReal hB
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_position hdim x _).contDiffAt) hpB).prodMk ?_
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).contDiff.contDiffAt).mul
      (contDiffAt_normalScale hdim x o ho a b hb z)

include hb in
theorem overlap_base (y : Coord (r+1)) (hB : 0 < height hdim x b y) (j : Fin (n+1)) :
    (overlap hdim x o a b y).base j =
      if j ∈ labelsSet x o then (center hdim x a b y : ℂ) else normalizedPosition hdim x b j y := by
  unfold BoundaryClusterFreeCoordinates.base
  split_ifs with hj hjb
  · rfl
  · subst j
    exact (RealForestSimpleCluster.normalize_self _ hB).symm
  · rfl

include ha in
theorem overlap_velocity (y : Coord (r+1)) (hA : 0 < shapeHeight hdim x o a y) (j : Fin (n+1)) :
    (overlap hdim x o a b y).velocity j =
      if j ∈ labelsSet x o then normalizedShape hdim x o a j y else 0 := by
  unfold BoundaryClusterFreeCoordinates.velocity
  split_ifs with hj hja
  · subst j
    exact (RealForestSimpleCluster.normalize_self _ hA).symm
  · rfl
  · rfl

include ho ha hb in
/-- The literal inserted inside and outside vertices coincide with actual
forest leaf positions after normalization at the chosen outside anchor. -/
theorem insertion_interior (y : Coord (r+1)) (hB : 0 < height hdim x b y)
    (hA : 0 < shapeHeight hdim x o a y) (j : Fin (n+1)) :
    (overlap hdim x o a b y).base j + ((overlap hdim x o a b y).radius : ℂ) *
      (overlap hdim x o a b y).velocity j = normalizedPosition hdim x b j y := by
  rw [overlap_base hdim x o a b hb y hB, overlap_velocity hdim x o a b ha y hA]
  by_cases hj : j ∈ labelsSet x o
  · rw [if_pos hj, if_pos hj, overlap_radius]
    have hja := position_inside_factor hdim x o y (Sum.inl (Sum.inl j)) ((mem_interiorLabels 0 x _ _).mp hj)
    have haa := position_inside_factor hdim x o y (Sum.inl (Sum.inl a)) ((mem_interiorLabels 0 x _ _).mp ha)
    rw [nodePosition_real hdim x o ho y] at hja haa
    have har := congrArg Complex.re haa
    simp only [Complex.add_re, Complex.ofReal_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero] at har
    unfold normalizedPosition normalizedShape center normalizeReal RealForestSimpleCluster.normalize
    unfold simpleRadius normalScale height shapeHeight
    have hnB : ((position hdim x (Sum.inl (Sum.inl b)) y).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
    have hnA : ((shapePosition hdim x o (Sum.inl (Sum.inl a)) y).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    simp only [Complex.real_smul] at hja
    rw [har, hja]
    push_cast
    field_simp
    ring
  · rw [if_neg hj, if_neg hj, mul_zero, add_zero]

include ho ha in
theorem insertion_boundary (y : Coord (r+1)) (hB : 0 < height hdim x b y)
    (hA : 0 < shapeHeight hdim x o a y) (j : Fin m) :
    (overlap hdim x o a b y).boundaryBase (lower x o) (upper x o) j +
      (overlap hdim x o a b y).radius * (overlap hdim x o a b y).boundaryVelocity (lower x o) (upper x o) j =
      normalizedBoundary hdim x b j y := by
  by_cases hj : j ∈ boundaryClusterBlock (lower x o) (upper x o)
  · have hj' := (RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mpr hj
    have hja := congrArg Complex.re (position_inside_factor hdim x o y (Sum.inl (Sum.inr j)) hj')
    have haa := congrArg Complex.re (position_inside_factor hdim x o y (Sum.inl (Sum.inl a))
      ((mem_interiorLabels 0 x _ _).mp ha))
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hja haa
    simp only [BoundaryClusterFreeCoordinates.boundaryBase, BoundaryClusterFreeCoordinates.boundaryVelocity,
      if_pos hj, overlap, BoundaryClusterFreeCoordinates.center, BoundaryClusterFreeCoordinates.radius]
    unfold normalizedBoundary normalizedBoundaryShape center normalizeReal simpleRadius normalScale height shapeHeight
    rw [hja, haa]
    unfold height at hB
    unfold shapeHeight at hA
    field_simp [ne_of_gt hA, ne_of_gt hB]
    <;> ring
  · simp only [BoundaryClusterFreeCoordinates.boundaryBase, BoundaryClusterFreeCoordinates.boundaryVelocity,
      if_neg hj, mul_zero, add_zero, overlap]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullOverlap
