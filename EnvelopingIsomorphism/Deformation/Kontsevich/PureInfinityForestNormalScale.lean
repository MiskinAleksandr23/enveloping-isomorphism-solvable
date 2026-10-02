import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestNormalScale
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCoordinates

/-! Positive normal multipliers for the actual pure and infinity collars.
The formulas use full forest leaf positions and branch units, not a product
extension chosen independently of the physical forest insertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestNormalScale
open scoped Classical
namespace PureForestNormalScale
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin m)

def gap (y : Coord (r+1)) : ℝ :=
  (shapePosition hdim x o (Sum.inl (Sum.inr b)) y).re -
    (shapePosition hdim x o (Sum.inl (Sum.inr a)) y).re

def normalScale (y : Coord (r+1)) : ℝ :=
  parentScale hdim x o y * gap hdim x o a b y / height hdim x 0 y

def simpleRadius (y : Coord (r+1)) : ℝ :=
  y (axis hdim x o) * normalScale hdim x o a b y

theorem contDiff_gap : ContDiff ℝ ⊤ (gap hdim x o a b) :=
  (Complex.reCLM.contDiff.comp (contDiff_shapePosition hdim x o _)).sub
    (Complex.reCLM.contDiff.comp (contDiff_shapePosition hdim x o _))

variable (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (PureForestSimpleCluster.lower x o).val)
  (hu : b.val + 1 = (PureForestSimpleCluster.upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hl hu hab in
/-- The full pure radius is the actual normalized distance between its two
boundary endpoints, also away from the face. -/
theorem simpleRadius_eq_boundary_gap (y : Coord (r+1)) :
    simpleRadius hdim x o a b y =
      ((position hdim x (Sum.inl (Sum.inr b)) y).re -
        (position hdim x (Sum.inl (Sum.inr a)) y).re) / height hdim x 0 y := by
  have ha := (RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) a).mpr
    (PureForestSimpleCluster.left_mem x o a b hl hu hab)
  have hb := (RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) b).mpr
    (PureForestSimpleCluster.right_mem x o a b hl hu hab)
  rw [position_inside_factor hdim x o y _ ha, position_inside_factor hdim x o y _ hb]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  unfold simpleRadius normalScale gap
  ring

include ho hl hu hab in
theorem normalScale_face_pos : 0 < normalScale hdim x o a b (facePoint hdim x o z.val) :=
  div_pos (mul_pos (parentScale_face_pos hdim x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z)
    (PureForestSimpleCluster.gap_pos hdim x o ho a b hl hu hab z))
    (PureForestSimpleCluster.anchor_pos hdim x o ho z)

include ho in
theorem contDiffAt_normalScale : ContDiffAt ℝ ⊤ (normalScale hdim x o a b) (facePoint hdim x o z.val) :=
  ((contDiff_parentScale hdim x o).contDiffAt.mul (contDiff_gap hdim x o a b).contDiffAt).div
    (contDiff_height hdim x 0).contDiffAt (PureForestSimpleCluster.anchor_pos hdim x o ho z).ne'

@[simp] theorem simpleRadius_face (w : Coord r) : simpleRadius hdim x o a b (facePoint hdim x o w) = 0 := by
  simp [simpleRadius, facePoint, faceEmbedding]

include ho in
theorem fderiv_simpleRadius_face :
    fderiv ℝ (simpleRadius hdim x o a b) (facePoint hdim x o z.val) =
      normalScale hdim x o a b (facePoint hdim x o z.val) • ContinuousLinearMap.proj (axis hdim x o) := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).hasFDerivAt.mul
    ((contDiffAt_normalScale hdim x o a b ho z).differentiableAt (by simp)).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.proj_apply, facePoint, faceEmbedding, Fin.insertNth_apply_same,
    zero_smul, zero_add] at h
  convert h using 1 <;> rfl
end PureForestNormalScale

namespace InfinityForestNormalScale
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)

def offset (j : Fin m) (y : Coord (r+1)) : ℝ :=
  (position hdim x (Sum.inl (Sum.inr j)) y).re - (position hdim x (Sum.inl (Sum.inl 0)) y).re

def normalScale (y : Coord (r+1)) : ℝ :=
  parentScale hdim x o y * shapeHeight hdim x o 0 y / |offset hdim x q y|

def simpleRadius (y : Coord (r+1)) : ℝ :=
  y (axis hdim x o) * normalScale hdim x o q y

theorem contDiff_offset (j : Fin m) : ContDiff ℝ ⊤ (offset hdim x j) :=
  (Complex.reCLM.contDiff.comp (contDiff_position hdim x _)).sub
    (Complex.reCLM.contDiff.comp (contDiff_position hdim x _))

variable (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (InfinityForestSimpleCluster.lower x o) (InfinityForestSimpleCluster.upper x o))
  (hne : (boundaryClusterBlock (InfinityForestSimpleCluster.lower x o) (InfinityForestSimpleCluster.upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho in
theorem offset_face (j : Fin m) :
    offset hdim x j (facePoint hdim x o z.val) = InfinityForestSimpleCluster.offset hdim x o z j := by
  have hi := position_inside_factor hdim x o (facePoint hdim x o z.val) (Sum.inl (Sum.inl 0))
    ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp (InfinityForestSimpleCluster.interior_mem x o ho 0))
  simp only [facePoint, faceEmbedding, Fin.insertNth_apply_same, zero_mul, zero_smul, add_zero] at hi
  change position hdim x (Sum.inl (Sum.inl 0)) (facePoint hdim x o z.val) =
    nodePosition hdim x o (facePoint hdim x o z.val) at hi
  unfold offset
  rw [hi]
  rfl

include ho in
/-- The full infinity radius is the actual anchor height divided by the
outside-anchor distance in the same translated configuration. -/
theorem simpleRadius_eq_height_ratio (y : Coord (r+1)) :
    simpleRadius hdim x o q y = height hdim x 0 y / |offset hdim x q y| := by
  have hi := congrArg Complex.im (position_inside_factor hdim x o y (Sum.inl (Sum.inl 0))
    ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp (InfinityForestSimpleCluster.interior_mem x o ho 0)))
  rw [nodePosition_real hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) y] at hi
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.real_smul,
    Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] at hi
  unfold simpleRadius normalScale height shapeHeight
  rw [hi]
  ring

include ho hq hne in
theorem normalScale_face_pos : 0 < normalScale hdim x o q (facePoint hdim x o z.val) := by
  unfold normalScale
  rw [offset_face hdim x o ho z q]
  exact div_pos (mul_pos (parentScale_face_pos hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z)
    (InfinityForestSimpleCluster.shapeAnchor_pos hdim x o ho z))
    (InfinityForestSimpleCluster.coarseScale_pos hdim x o ho q hq hne z)

include ho hq hne in
theorem contDiffAt_normalScale : ContDiffAt ℝ ⊤ (normalScale hdim x o q) (facePoint hdim x o z.val) := by
  have hg : 0 < |offset hdim x q (facePoint hdim x o z.val)| := by
    rw [offset_face hdim x o ho z q]
    exact InfinityForestSimpleCluster.coarseScale_pos hdim x o ho q hq hne z
  have hn : ContDiffAt ℝ ⊤ (fun y ↦ |offset hdim x q y|) (facePoint hdim x o z.val) := by
    simpa only [Real.norm_eq_abs] using (contDiff_offset hdim x q).contDiffAt.norm ℝ (abs_pos.mp hg)
  exact ((contDiff_parentScale hdim x o).contDiffAt.mul (contDiff_shapeHeight hdim x o 0).contDiffAt).div hn hg.ne'

@[simp] theorem simpleRadius_face (w : Coord r) : simpleRadius hdim x o q (facePoint hdim x o w) = 0 := by
  simp [simpleRadius, facePoint, faceEmbedding]

include ho hq hne in
theorem fderiv_simpleRadius_face :
    fderiv ℝ (simpleRadius hdim x o q) (facePoint hdim x o z.val) =
      normalScale hdim x o q (facePoint hdim x o z.val) • ContinuousLinearMap.proj (axis hdim x o) := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (axis hdim x o)).hasFDerivAt.mul
    ((contDiffAt_normalScale hdim x o q ho hq hne z).differentiableAt (by simp)).hasFDerivAt).fderiv
  simp only [ContinuousLinearMap.proj_apply, facePoint, faceEmbedding, Fin.insertNth_apply_same,
    zero_smul, zero_add] at h
  convert h using 1 <;> rfl
end InfinityForestNormalScale
end EnvelopingIsomorphism.Deformation.Kontsevich
