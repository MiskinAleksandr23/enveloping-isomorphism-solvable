import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion

/-! The genuine positive normal scale from a paired forest radius to the
normalized simple-cluster radius. All factors are native radial products,
resolved reference differences, and the actual normalization height. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestNormalScale
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference ForestNormalizationTelescope AncestorScaleRatios
open PairedForestCoarsePositions PairedForestSimpleCluster BoxStokes CompactOrthantStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)

/-- The existing full native real coordinates, before setting any radius to zero. -/
def fullParameters (y : Coord (r + 1)) : ForestDirectionRatioCoordinates.Parameters (tree 0 x) :=
  realization 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)

def fullPosition (y : Coord (r + 1)) (j : Fin (n + 1)) : ℂ :=
  position (tree 0 x) (fullParameters hdim x y).1 (fullParameters hdim x y).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inl j)))

def fullShapePosition (y : Coord (r + 1)) (j : Fin (n + 1)) : ℂ :=
  branchUnit (tree 0 x) (fullParameters hdim x y).1 (fullParameters hdim x y).2
    (node x o ho) (canonicalLeaf 0 x (Sum.inl (Sum.inl j)))

def parentScale (y : Coord (r + 1)) : ℝ :=
  scale (fullParameters hdim x y).1 (Order.pred (node x o ho))

def referenceDifference (y : Coord (r + 1)) : ℂ :=
  fullShapePosition hdim x o ho y (reference x o ho) - fullShapePosition hdim x o ho y (anchor x o ho)

def height (y : Coord (r + 1)) : ℝ := (fullPosition hdim x y 0).im

def normalScale (y : Coord (r + 1)) : ℝ :=
  parentScale hdim x o ho y * ‖referenceDifference hdim x o ho y‖ / height hdim x y

/-- Signed smooth extension of the actual positive simple reference radius. -/
def simpleRadius (y : Coord (r + 1)) : ℝ := y (axis hdim x o) * normalScale hdim x o ho y

def facePoint (z : Coord r) : Coord (r + 1) := faceEmbedding (axis hdim x o) 0 z

@[simp] theorem fullParameters_face (z : ForestRadialFaceLocalization.source hdim x o) :
    fullParameters hdim x (facePoint hdim x o z.val) = PairedForestCoarsePositions.parameters hdim x o z := rfl

@[simp] theorem height_face (z : ForestRadialFaceLocalization.source hdim x o) :
    height hdim x (facePoint hdim x o z.val) = (positions hdim x o z (Sum.inl (Sum.inl 0))).im := rfl

@[simp] theorem referenceDifference_face (z : ForestRadialFaceLocalization.source hdim x o) :
    referenceDifference hdim x o ho (facePoint hdim x o z.val) =
      shapePosition hdim x o ho z (reference x o ho) - shapePosition hdim x o ho z (anchor x o ho) := rfl

theorem parentScale_face_pos (z : ForestRadialFaceLocalization.source hdim x o) :
    0 < parentScale hdim x o ho (facePoint hdim x o z.val) := by
  apply scale_pos_of_not_le hdim x o ho z
  · exact (Order.pred_lt_iff_ne_bot.mpr (upperNode 0 x o ho).property.1).not_ge
  · intro h
    have hm : Sum.inl (Sum.inl (anchor x o ho)) ∈ (node x o ho).val :=
      (mem_interiorLabels 0 x _ _).mp (anchor_mem x o ho)
    exact reflected_not_upper x o ho (anchor x o ho) ((h.trans (Order.pred_le _)) hm)

theorem normalScale_face_pos (z : ForestRadialFaceLocalization.source hdim x o) :
    0 < normalScale hdim x o ho (facePoint hdim x o z.val) :=
  div_pos (mul_pos (parentScale_face_pos hdim x o ho z) (shapeRadius_pos hdim x o ho z))
    (positions_upper_im_pos hdim x o ho z 0)

/-- The actual selected node radius is the existing global-Stokes coordinate axis. -/
theorem selected_radius (y : Coord (r + 1)) :
    (fullParameters hdim x y).1 (node x o ho) = y (axis hdim x o) := by
  change radiusArray 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y) (node x o ho) = _
  rw [radiusArray, dif_pos (upperNode 0 x o ho).property]
  have h := ForestGlobalGraphStokes.sourceCoordinates_radial hdim x
    ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y) (orbitEquiv 0 x o)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [node, orbitEquiv, (upperNode_spec 0 x o ho).1, axis] at h ⊢
  convert h.symm using 1 <;> rfl

/-- Literal radial-product and resolved-unit factorization for the chosen pair. -/
theorem reference_difference_factor (y : Coord (r + 1)) :
    fullPosition hdim x y (reference x o ho) - fullPosition hdim x y (anchor x o ho) =
      (y (axis hdim x o) * parentScale hdim x o ho y) • referenceDifference hdim x o ho y := by
  have ha : node x o ho ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl (anchor x o ho))) :=
    (le_canonicalLeaf_iff 0 x _ _).mpr ((mem_interiorLabels 0 x _ _).mp (anchor_mem x o ho))
  have hb : node x o ho ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl (reference x o ho))) :=
    (le_canonicalLeaf_iff 0 x _ _).mpr ((mem_interiorLabels 0 x _ _).mp (reference_mem x o ho))
  unfold fullPosition
  rw [position_factor_from_ancestor (tree 0 x) _ _ hb, position_factor_from_ancestor (tree 0 x) _ _ ha]
  rw [scale_step (tree 0 x) _ _ (upperNode 0 x o ho).property.1, selected_radius]
  change (_ + _ • _) - (_ + _ • _) = _ • (_ - _)
  simp only [smul_sub]
  abel

theorem contDiff_fullParameters : ContDiff ℝ ⊤ (fullParameters hdim x) :=
  (contDiff_realization 0 x).comp (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff

theorem contDiff_fullPosition (j : Fin (n + 1)) : ContDiff ℝ ⊤ (fun y ↦ fullPosition hdim x y j) :=
  (contDiff_position (tree 0 x) _).comp (contDiff_fullParameters hdim x)

theorem contDiff_parentScale : ContDiff ℝ ⊤ (parentScale hdim x o ho) :=
  (contDiff_scale _).comp (contDiff_fst.comp (contDiff_fullParameters hdim x))

theorem contDiff_referenceDifference : ContDiff ℝ ⊤ (referenceDifference hdim x o ho) :=
  ((contDiff_branchUnit (tree 0 x) _ _).comp (contDiff_fullParameters hdim x)).sub
    ((contDiff_branchUnit (tree 0 x) _ _).comp (contDiff_fullParameters hdim x))

theorem contDiff_height : ContDiff ℝ ⊤ (height hdim x) :=
  Complex.imCLM.contDiff.comp (contDiff_fullPosition hdim x 0)

theorem contDiffAt_normalScale (z : ForestRadialFaceLocalization.source hdim x o) :
    ContDiffAt ℝ ⊤ (normalScale hdim x o ho) (facePoint hdim x o z.val) := by
  have hne : referenceDifference hdim x o ho (facePoint hdim x o z.val) ≠ 0 :=
    norm_pos_iff.mp (shapeRadius_pos hdim x o ho z)
  exact ((contDiff_parentScale hdim x o ho).contDiffAt.mul
    ((contDiff_referenceDifference hdim x o ho).contDiffAt.norm ℝ hne)).div
      (contDiff_height hdim x).contDiffAt (positions_upper_im_pos hdim x o ho z 0).ne'

@[simp] theorem simpleRadius_face (z : Coord r) : simpleRadius hdim x o ho (facePoint hdim x o z) = 0 := by
  simp [simpleRadius, facePoint, faceEmbedding]

/-- The actual differential is the positive normal scalar times the selected
native radius covector; all tangential derivatives vanish automatically. -/
theorem fderiv_simpleRadius_face (z : ForestRadialFaceLocalization.source hdim x o) :
    fderiv ℝ (simpleRadius hdim x o ho) (facePoint hdim x o z.val) =
      normalScale hdim x o ho (facePoint hdim x o z.val) • ContinuousLinearMap.proj (axis hdim x o) := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r + 1) ↦ ℝ) (axis hdim x o)).hasFDerivAt.mul
    ((contDiffAt_normalScale hdim x o ho z).differentiableAt (by simp)).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.proj_apply, facePoint, faceEmbedding, Fin.insertNth_apply_same,
    zero_smul, zero_add] at h
  convert h using 1 <;> rfl

/-- On the genuine inward half-space, the signed smooth radius is exactly the
reference distance in the original normalized configuration coordinates. -/
theorem simpleRadius_eq_actual_reference_distance (y : Coord (r + 1))
    (hy : 0 < height hdim x y) (hp : 0 ≤ parentScale hdim x o ho y) (hr : 0 ≤ y (axis hdim x o)) :
    simpleRadius hdim x o ho y =
      ‖GraphForms.interiorPoint (reference x o ho)
          (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)) -
        GraphForms.interiorPoint (anchor x o ho)
          (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y))‖ := by
  have hy' : (ForestPositiveChartSmooth.anchorPoint 0 x
      ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).im ≠ 0 := hy.ne'
  rw [ForestPositiveChartSmooth.interiorPoint_forwardCoordinates 0 x _ hy',
    ForestPositiveChartSmooth.interiorPoint_forwardCoordinates 0 x _ hy']
  simp only [Equiv.swap_self, Equiv.refl_apply]
  change _ = ‖(fullPosition hdim x y (reference x o ho) - ((fullPosition hdim x y 0).re : ℂ)) /
      (height hdim x y : ℂ) -
    (fullPosition hdim x y (anchor x o ho) - ((fullPosition hdim x y 0).re : ℂ)) / (height hdim x y : ℂ)‖
  rw [← sub_div]
  have hsub : (fullPosition hdim x y (reference x o ho) - ((fullPosition hdim x y 0).re : ℂ)) -
      (fullPosition hdim x y (anchor x o ho) - ((fullPosition hdim x y 0).re : ℂ)) =
        fullPosition hdim x y (reference x o ho) - fullPosition hdim x y (anchor x o ho) := by abel
  rw [hsub, norm_div, reference_difference_factor, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hr hp), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  unfold simpleRadius normalScale
  ring

/-- The full native collar has a neighborhood where the normal multiplier is
smooth and strictly positive and its nonnegative-radius restriction is the
actual normalized reference distance. -/
theorem eventually_actual_reference_distance (z : ForestRadialFaceLocalization.source hdim x o) :
    ∀ᶠ y in nhds (facePoint hdim x o z.val),
      0 < normalScale hdim x o ho y ∧
      (0 ≤ y (axis hdim x o) → simpleRadius hdim x o ho y =
        ‖GraphForms.interiorPoint (reference x o ho)
            (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)) -
          GraphForms.interiorPoint (anchor x o ho)
            (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y))‖) := by
  have hn := (contDiffAt_normalScale hdim x o ho z).continuousAt.eventually
    (isOpen_Ioi.mem_nhds (normalScale_face_pos hdim x o ho z))
  have hp := (contDiff_parentScale hdim x o ho).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (parentScale_face_pos hdim x o ho z))
  have hh := (contDiff_height hdim x).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (positions_upper_im_pos hdim x o ho z 0))
  filter_upwards [hn, hp, hh] with y hyn hyp hyh
  exact ⟨hyn, fun hyr ↦ simpleRadius_eq_actual_reference_distance hdim x o ho y hyh hyp.le hyr⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestNormalScale
