import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceDRCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion

/-! Explicit smooth extraction of actual coarse/planar product coordinates
from a paired native forest face, with a local phase branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSmoothProduct
open Configuration ExtractedForestParameters ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestInsertionDifference
open PairedForestSimpleCluster InteriorGraphFaceCoordinates BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

abbrev Product := ProductCoordinates (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m
abbrev Source := ForestRadialFaceLocalization.source hdim x o

def facePoint (z : Source hdim x o) : Coord (r + 1) := faceEmbedding (axis hdim x o) 0 z.val

def rawParameters (w : Coord (r + 1)) :=
  (fun (_ : ForestRadialFaceClassification.Orbit 0 x) ↦
    realization 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm w)) o
def rawPosition (j : DoubledLabel (n + 1) m) (w : Coord (r + 1)) : ℂ :=
  position (tree 0 x) (rawParameters hdim x o w).1 (rawParameters hdim x o w).2 (canonicalLeaf 0 x j)
def rawShape (j : Fin (n + 1)) (w : Coord (r + 1)) : ℂ :=
  branchUnit (tree 0 x) (rawParameters hdim x o w).1 (rawParameters hdim x o w).2
    (PairedForestCoarsePositions.node x o ho) (canonicalLeaf 0 x (Sum.inl (Sum.inl j)))
def rawHeight (w : Coord (r + 1)) : ℝ := (rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).im
def rawShift (w : Coord (r + 1)) : ℝ := -(rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).re / rawHeight hdim x o w

def rawBase (j : Fin (n + 1)) (w : Coord (r + 1)) : ℂ :=
  ((rawHeight hdim x o w)⁻¹ : ℝ) * rawPosition hdim x o (Sum.inl (Sum.inl j)) w + rawShift hdim x o w

def rawBoundary (j : Fin m) (w : Coord (r + 1)) : ℝ :=
  (rawHeight hdim x o w)⁻¹ * (rawPosition hdim x o (Sum.inl (Sum.inr j)) w).re + rawShift hdim x o w

def rawShapeRadius (w : Coord (r + 1)) : ℝ :=
  ‖rawShape hdim x o ho (reference x o ho) w - rawShape hdim x o ho (anchor x o ho) w‖

def rawVelocity (j : Fin (n + 1)) (w : Coord (r + 1)) : ℂ :=
  if j ∈ S x o ho then (rawShape hdim x o ho j w - rawShape hdim x o ho (anchor x o ho) w) /
    (rawShapeRadius hdim x o ho w : ℂ) else 0

theorem rawBase_eq (z : Source hdim x o) (j : Fin (n + 1)) :
    rawBase hdim x o j (facePoint hdim x o z) = (PairedForestSimpleCluster.base hdim x o ho z j : ℂ) := by
  rw [PairedForestSimpleCluster.base, PositiveAffine.coe_onUpper]
  rfl

theorem rawBoundary_eq (z : Source hdim x o) (j : Fin m) :
    rawBoundary hdim x o j (facePoint hdim x o z) = boundary hdim x o ho z j := rfl

theorem rawVelocity_eq (z : Source hdim x o) (j : Fin (n + 1)) :
    rawVelocity hdim x o ho j (facePoint hdim x o z) = PairedForestSimpleCluster.velocity hdim x o ho z j := rfl

theorem contDiff_rawPosition (j : DoubledLabel (n + 1) m) : ContDiff ℝ ⊤ (rawPosition hdim x o j) :=
  (contDiff_position (tree 0 x) (canonicalLeaf 0 x j)).comp
    ((contDiff_realization 0 x).comp (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff)

theorem contDiff_rawShape (j : Fin (n + 1)) : ContDiff ℝ ⊤ (rawShape hdim x o ho j) :=
  (contDiff_branchUnit (tree 0 x) _ _).comp
    ((contDiff_realization 0 x).comp (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff)

theorem contDiff_rawHeight : ContDiff ℝ ⊤ (rawHeight hdim x o) :=
  Complex.imCLM.contDiff.comp (contDiff_rawPosition hdim x o _)

include ho in
theorem rawHeight_pos (z : Source hdim x o) : 0 < rawHeight hdim x o (facePoint hdim x o z) :=
  PairedForestCoarsePositions.positions_upper_im_pos hdim x o ho z 0

include ho in
theorem contDiffAt_rawShift (z : Source hdim x o) : ContDiffAt ℝ ⊤ (rawShift hdim x o) (facePoint hdim x o z) :=
  ((Complex.reCLM.contDiff.comp (contDiff_rawPosition hdim x o _)).neg.contDiffAt).div
    (contDiff_rawHeight hdim x o).contDiffAt (rawHeight_pos hdim x o ho z).ne'

include ho in
theorem contDiffAt_rawBase (z : Source hdim x o) (j : Fin (n + 1)) :
    ContDiffAt ℝ ⊤ (rawBase hdim x o j) (facePoint hdim x o z) :=
  ((Complex.ofRealCLM.contDiff.contDiffAt.comp (facePoint hdim x o z)
    ((contDiff_rawHeight hdim x o).contDiffAt.inv (rawHeight_pos hdim x o ho z).ne')).mul
      (contDiff_rawPosition hdim x o _).contDiffAt).add
        (Complex.ofRealCLM.contDiff.contDiffAt.comp (facePoint hdim x o z) (contDiffAt_rawShift hdim x o ho z))

include ho in
theorem contDiffAt_rawBoundary (z : Source hdim x o) (j : Fin m) :
    ContDiffAt ℝ ⊤ (rawBoundary hdim x o j) (facePoint hdim x o z) :=
  (((contDiff_rawHeight hdim x o).contDiffAt.inv (rawHeight_pos hdim x o ho z).ne').mul
    (Complex.reCLM.contDiff.contDiffAt.comp (facePoint hdim x o z) (contDiff_rawPosition hdim x o _).contDiffAt)).add
      (contDiffAt_rawShift hdim x o ho z)

theorem rawShapeRadius_pos (z : Source hdim x o) : 0 < rawShapeRadius hdim x o ho (facePoint hdim x o z) :=
  shapeRadius_pos hdim x o ho z

theorem contDiffAt_rawVelocity (z : Source hdim x o) (j : Fin (n + 1)) :
    ContDiffAt ℝ ⊤ (rawVelocity hdim x o ho j) (facePoint hdim x o z) := by
  have hd := ((contDiff_rawShape hdim x o ho (reference x o ho)).sub
    (contDiff_rawShape hdim x o ho (anchor x o ho))).contDiffAt (x := (facePoint hdim x o z))
  have hnorm := hd.norm ℝ (norm_pos_iff.mp (rawShapeRadius_pos hdim x o ho z))
  have hr := Complex.ofRealCLM.contDiff.contDiffAt.comp (facePoint hdim x o z) hnorm
  unfold rawVelocity
  split_ifs
  · have hn := ((contDiff_rawShape hdim x o ho j).sub
      (contDiff_rawShape hdim x o ho (anchor x o ho))).contDiffAt (x := (facePoint hdim x o z))
    simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_def, Complex.ofRealCLM_apply, rawShapeRadius] using
      hn.mul (hr.inv (Complex.ofReal_ne_zero.mpr (rawShapeRadius_pos hdim x o ho z).ne'))
  · exact contDiffAt_const

def phase (z : Source hdim x o) : Circle :=
  ⟨rawVelocity hdim x o ho (reference x o ho) (facePoint hdim x o z),
    mem_sphere_zero_iff_norm.mpr (velocity_reference_norm hdim x o ho z)⟩

def angle (u : Circle) (w : Coord (r + 1)) : ℝ := Complex.arg (u : ℂ) +
  ForestShapeProjectionSmooth.angleInverseRaw u (rawVelocity hdim x o ho (reference x o ho) w)

theorem circleParameter_angle (u : Circle) (z : Source hdim x o) :
    circleParameter (angle hdim x o ho u (facePoint hdim x o z)) = rawVelocity hdim x o ho (reference x o ho) (facePoint hdim x o z) := by
  change circleParameter (Complex.arg (u : ℂ) +
    rotatedAnglePotential (u : ℂ)⁻¹ (phase hdim x o ho z : ℂ)) = (phase hdim x o ho z : ℂ)
  rw [circleParameter_eq, Circle.exp_add, Circle.exp_arg]
  have he : rotatedAnglePotential (u : ℂ)⁻¹ (phase hdim x o ho z : ℂ) =
      Complex.arg ((u⁻¹ * phase hdim x o ho z : Circle) : ℂ) := by
    simp only [rotatedAnglePotential, Complex.log_im, Circle.coe_mul, Circle.coe_inv]
  rw [he, Circle.exp_arg]
  simp

theorem rawVelocity_reference_norm (w : Coord (r + 1)) (hw : 0 < rawShapeRadius hdim x o ho w) :
    ‖rawVelocity hdim x o ho (reference x o ho) w‖ = 1 := by
  rw [rawVelocity, if_pos (reference_mem x o ho), norm_div, Complex.norm_real,
    Real.norm_of_nonneg hw.le]
  exact div_self hw.ne'

theorem circleParameter_angle_full (u : Circle) (w : Coord (r + 1))
    (hw : 0 < rawShapeRadius hdim x o ho w) :
    circleParameter (angle hdim x o ho u w) = rawVelocity hdim x o ho (reference x o ho) w := by
  let v : Circle := ⟨rawVelocity hdim x o ho (reference x o ho) w,
    mem_sphere_zero_iff_norm.mpr (rawVelocity_reference_norm hdim x o ho w hw)⟩
  change circleParameter (Complex.arg (u : ℂ) + rotatedAnglePotential (u : ℂ)⁻¹ (v : ℂ)) = (v : ℂ)
  rw [circleParameter_eq, Circle.exp_add, Circle.exp_arg]
  have he : rotatedAnglePotential (u : ℂ)⁻¹ (v : ℂ) = Complex.arg ((u⁻¹ * v : Circle) : ℂ) := by
    simp only [rotatedAnglePotential, Complex.log_im, Circle.coe_mul, Circle.coe_inv]
  rw [he, Circle.exp_arg]
  simp

theorem contDiffAt_angle (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (angle hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) := by
  apply ContDiffAt.add contDiffAt_const
  apply (ForestShapeProjectionSmooth.contDiffAt_angleInverseRaw _ _ ?_).comp (facePoint hdim x o z)
    (contDiffAt_rawVelocity hdim x o ho z (reference x o ho))
  change ((phase hdim x o ho z : ℂ)⁻¹ * (phase hdim x o ho z : ℂ)) ∈ Complex.slitPlane
  simp [(phase hdim x o ho z).coe_ne_zero]

def fullToProduct (u : Circle) (w : Coord (r + 1)) : Product x o ho :=
  ((angle hdim x o ho u w, fun j ↦
      rawVelocity hdim x o ho (shapeEnum.symm j).val w /
        rawVelocity hdim x o ho (reference x o ho) w),
    (fun j ↦ rawBase hdim x o (coarseEnum.symm j).val w, fun j ↦ rawBoundary hdim x o j w))

theorem contDiffAt_fullToProduct (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (fullToProduct hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) := by
  apply ContDiffAt.prodMk
  · apply ContDiffAt.prodMk (contDiffAt_angle hdim x o ho z)
    apply contDiffAt_pi.mpr
    intro j
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      (contDiffAt_rawVelocity hdim x o ho z (shapeEnum.symm j).val).mul
        ((contDiffAt_rawVelocity hdim x o ho z (reference x o ho)).inv (phase hdim x o ho z).coe_ne_zero)
  · exact (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBase hdim x o ho z (coarseEnum.symm j).val).prodMk
      (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBoundary hdim x o ho z j)

def toProduct (u : Circle) (w : Coord r) : Product x o ho :=
  fullToProduct hdim x o ho u (faceEmbedding (axis hdim x o) 0 w)

theorem contDiffAt_toProduct (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (toProduct hdim x o ho (phase hdim x o ho z)) z.val :=
  (contDiffAt_fullToProduct hdim x o ho z).comp z.val (faceTangent (axis hdim x o)).contDiff.contDiffAt

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSmoothProduct
