import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope

/-! The actual positive normal scale of a fixed real forest collar. The
outside normalization anchor may be any vertex outside the cluster. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestNormalScale
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestInsertionDifference
open ForestNormalizationTelescope AncestorScaleRatios RealForestCoarsePositions
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)

def fullParameters (y : Coord (r+1)) : ForestDirectionRatioCoordinates.Parameters (tree 0 x) :=
  realization 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)

def position (j : DoubledLabel (n+1) m) (y : Coord (r+1)) : ℂ :=
  ForestInsertionDifference.position (tree 0 x) (fullParameters hdim x y).1 (fullParameters hdim x y).2 (canonicalLeaf 0 x j)

def shapePosition (j : DoubledLabel (n+1) m) (y : Coord (r+1)) : ℂ :=
  branchUnit (tree 0 x) (fullParameters hdim x y).1 (fullParameters hdim x y).2 (node x o) (canonicalLeaf 0 x j)

def nodePosition (y : Coord (r+1)) : ℂ :=
  ForestInsertionDifference.position (tree 0 x) (fullParameters hdim x y).1 (fullParameters hdim x y).2 (node x o)

def parentScale (y : Coord (r+1)) : ℝ := scale (fullParameters hdim x y).1 (Order.pred (node x o))
def height (b : Fin (n+1)) (y : Coord (r+1)) : ℝ := (position hdim x (Sum.inl (Sum.inl b)) y).im
def shapeHeight (a : Fin (n+1)) (y : Coord (r+1)) : ℝ := (shapePosition hdim x o (Sum.inl (Sum.inl a)) y).im

def normalScale (a b : Fin (n+1)) (y : Coord (r+1)) : ℝ :=
  parentScale hdim x o y * shapeHeight hdim x o a y / height hdim x b y

def simpleRadius (a b : Fin (n+1)) (y : Coord (r+1)) : ℝ :=
  y (axis hdim x o) * normalScale hdim x o a b y

def facePoint (z : Coord r) : Coord (r+1) := faceEmbedding (axis hdim x o) 0 z

theorem selected_radius (y : Coord (r+1)) :
    (fullParameters hdim x y).1 (node x o) = y (axis hdim x o) := by
  change radiusArray 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y) (node x o) = _
  rw [radiusArray, dif_pos (representative 0 x o).property]
  have h := ForestGlobalGraphStokes.sourceCoordinates_radial hdim x
    ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y) (orbitEquiv 0 x o)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  change ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y).1
    (orbitEquiv 0 x (ReflectedRadiusCoordinates.orbitClass (tree 0 x) (reflection 0 x)
      (reflection_reflection 0 x) (representative 0 x o))) = _
  rw [representative_orbit]
  exact h.symm

theorem position_inside_factor (y : Coord (r+1)) (j : DoubledLabel (n+1) m)
    (hj : j ∈ (node x o).val) :
    position hdim x j y = nodePosition hdim x o y +
      (y (axis hdim x o) * parentScale hdim x o y) • shapePosition hdim x o j y := by
  unfold position
  rw [position_factor_from_ancestor (tree 0 x) _ _ ((le_canonicalLeaf_iff 0 x _ _).mpr hj),
    scale_step (tree 0 x) _ _ (representative 0 x o).property.1, selected_radius]
  rfl

theorem contDiff_fullParameters : ContDiff ℝ ⊤ (fullParameters hdim x) :=
  (contDiff_realization 0 x).comp (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff

theorem contDiff_position (j : DoubledLabel (n+1) m) : ContDiff ℝ ⊤ (position hdim x j) :=
  (ForestInsertionDifference.contDiff_position (tree 0 x) _).comp (contDiff_fullParameters hdim x)

theorem contDiff_shapePosition (j : DoubledLabel (n+1) m) : ContDiff ℝ ⊤ (shapePosition hdim x o j) :=
  (contDiff_branchUnit (tree 0 x) _ _).comp (contDiff_fullParameters hdim x)

theorem contDiff_nodePosition : ContDiff ℝ ⊤ (nodePosition hdim x o) :=
  (ForestInsertionDifference.contDiff_position (tree 0 x) _).comp (contDiff_fullParameters hdim x)

theorem contDiff_parentScale : ContDiff ℝ ⊤ (parentScale hdim x o) :=
  (contDiff_scale _).comp (contDiff_fst.comp (contDiff_fullParameters hdim x))

theorem contDiff_height (b : Fin (n+1)) : ContDiff ℝ ⊤ (height hdim x b) :=
  Complex.imCLM.contDiff.comp (contDiff_position hdim x _)

theorem contDiff_shapeHeight (a : Fin (n+1)) : ContDiff ℝ ⊤ (shapeHeight hdim x o a) :=
  Complex.imCLM.contDiff.comp (contDiff_shapePosition hdim x o _)

variable (ho : IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho in
theorem parentScale_face_pos : 0 < parentScale hdim x o (facePoint hdim x o z.val) :=
  scale_pos_of_not_le hdim x o ho z _
    (Order.pred_lt_iff_ne_bot.mpr (representative 0 x o).property.1).not_ge

include ho ha hb in
theorem normalScale_face_pos : 0 < normalScale hdim x o a b (facePoint hdim x o z.val) :=
  div_pos (mul_pos (parentScale_face_pos hdim x o ho z)
    (RealForestSimpleCluster.shapeAnchor_pos hdim x o ho a ha z))
    (RealForestSimpleCluster.coarseAnchor_pos hdim x o ho b hb z)

include ho hb in
theorem contDiffAt_normalScale : ContDiffAt ℝ ⊤ (normalScale hdim x o a b) (facePoint hdim x o z.val) :=
  ((contDiff_parentScale hdim x o).contDiffAt.mul (contDiff_shapeHeight hdim x o a).contDiffAt).div
    (contDiff_height hdim x b).contDiffAt (RealForestSimpleCluster.coarseAnchor_pos hdim x o ho b hb z).ne'

@[simp] theorem simpleRadius_face (w : Coord r) : simpleRadius hdim x o a b (facePoint hdim x o w) = 0 := by
  simp [simpleRadius, facePoint, faceEmbedding]

include ho hb in
theorem fderiv_simpleRadius_face :
    fderiv ℝ (simpleRadius hdim x o a b) (facePoint hdim x o z.val) =
      normalScale hdim x o a b (facePoint hdim x o z.val) • ContinuousLinearMap.proj (axis hdim x o) := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).hasFDerivAt.mul
    ((contDiffAt_normalScale hdim x o ho a b hb z).differentiableAt (by simp)).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.proj_apply, facePoint, faceEmbedding, Fin.insertNth_apply_same,
    zero_smul, zero_add] at h
  convert h using 1 <;> rfl

include ho in
theorem nodePosition_real (y : Coord (r+1)) : nodePosition hdim x o y = ((nodePosition hdim x o y).re : ℂ) := by
  have hi := ReflectedForestInsertion.position_im_eq_zero_of_fixed (tree 0 x) (reflection 0 x)
    (fullParameters hdim x y).1 (radiusArray_reflection 0 x _)
    (fullParameters hdim x y).2 (shapeArray_constraints 0 x _).2.1 (node x o) (node_fixed x o ho)
  change (nodePosition hdim x o y).im = 0 at hi
  exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestNormalScale
