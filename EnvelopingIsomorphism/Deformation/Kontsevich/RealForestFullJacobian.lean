import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport

/-! The proper-real full collar in the literal radial-first native basis.
The normal cofactor and physical insertion determinant are computed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullJacobian
open Configuration ForestRadialFaceClassification BoxStokes RealForestNormalScale
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestFullOverlap
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

def fullCoordinates : BoundaryClusterFreeCoordinates b a (labelsSet x o) m ≃L[ℝ] Coord (r+1) :=
  BoundaryClusterFreeCoordinates.splitRadius.toContinuousLinearEquiv.trans
    (((RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
      ((BoundaryGraphNativeOrientation.appendRadius r).toContinuousLinearEquiv.trans
        (BoundaryGraphRadiusFirstTransport.rotateRadius r)))

def map (y : Coord (r+1)) : Coord (r+1) :=
  fullCoordinates hdim x o a b ha hb (overlap hdim x o a b y)

@[simp] theorem fullCoordinates_radius (q : BoundaryClusterFreeCoordinates b a (labelsSet x o) m) :
    fullCoordinates hdim x o a b ha hb q 0 = q.radius := by
  simp [fullCoordinates, BoundaryGraphRadiusFirstTransport.rotateRadius,
    BoundaryGraphNativeOrientation.appendRadius, BoundaryClusterFreeCoordinates.splitRadius,
    BoundaryClusterFreeCoordinates.radius]
  have hlast : (-1 : Fin (r+1)) = Fin.last r := by
    apply Fin.ext
    simp
  rw [hlast, Fin.snoc_last]

@[simp] theorem fullCoordinates_face (q : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m) :
    fullCoordinates hdim x o a b ha hb (BoundaryClusterFreeCoordinates.faceEmbedding q) =
      faceEmbedding 0 0 (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb q) := by
  change BoundaryGraphRadiusFirstTransport.rotateRadius r
    (faceEmbedding (Fin.last r) 0 (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb q)) = _
  exact BoundaryGraphRadiusFirstTransport.rotateRadius_face r _

include ha in
theorem overlap_face_all (w : Coord r) :
    overlap hdim x o a b (facePoint hdim x o w) =
      BoundaryClusterFreeCoordinates.faceEmbedding (RealForestSimpleCoordinates.coordinates hdim x o a b w) := by
  have hi := position_inside_factor hdim x o (facePoint hdim x o w) (Sum.inl (Sum.inl a))
    ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp ha)
  simp only [facePoint, faceEmbedding, Fin.insertNth_apply_same, zero_mul, zero_smul, add_zero] at hi
  change position hdim x (Sum.inl (Sum.inl a)) (facePoint hdim x o w) =
    nodePosition hdim x o (facePoint hdim x o w) at hi
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · change RealForestSimpleCluster.normalizeReal _ (position hdim x (Sum.inl (Sum.inl a))
            (facePoint hdim x o w)).re = _
          rw [hi]
          rfl
        · exact simpleRadius_face hdim x o a b w

theorem map_face (w : Coord r) :
    map hdim x o a b ha hb (facePoint hdim x o w) =
      faceEmbedding 0 0 (RealForestFaceChangeVariables.map hdim x o a b ha hb w) := by
  rw [map, overlap_face_all hdim x o a b ha, fullCoordinates_face]
  rfl

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho in
theorem contDiffAt_map : ContDiffAt ℝ ⊤ (map hdim x o a b ha hb) (facePoint hdim x o z.val) :=
  (fullCoordinates hdim x o a b ha hb).contDiff.contDiffAt.comp _
    (contDiffAt_overlap hdim x o a b ho ha hb z)

include ho in
theorem normal_differential (v : Coord (r+1)) :
    fderiv ℝ (map hdim x o a b ha hb) (facePoint hdim x o z.val) v 0 =
      normalScale hdim x o a b (facePoint hdim x o z.val) * v (axis hdim x o) := by
  let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) (0 : Fin (r+1))
  have h := (proj.hasFDerivAt.comp (facePoint hdim x o z.val)
    ((contDiffAt_map hdim x o a b ha hb ho z).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : proj ∘ map hdim x o a b ha hb = simpleRadius hdim x o a b := by
    funext y
    simp [proj, map]
  rw [he, fderiv_simpleRadius_face hdim x o ho a b hb z] at h
  exact (congrArg (fun L : Coord (r+1) →L[ℝ] ℝ ↦ L v) h).symm

include ho in
theorem face_derivative :
    RadialFaceJacobian.faceDerivative (axis hdim x o) 0
      (fderiv ℝ (map hdim x o a b ha hb) (facePoint hdim x o z.val)) =
      fderiv ℝ (RealForestFaceChangeVariables.map hdim x o a b ha hb) z.val := by
  have h := (ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1))).hasFDerivAt.comp z.val
    ((((contDiffAt_map hdim x o a b ha hb ho z).differentiableAt (by simp)).hasFDerivAt).comp z.val
      (hasFDerivAt_faceEmbedding (axis hdim x o) 0 z.val))
  have he : ForestRadialFaceImmersion.faceProjection (0 : Fin (r+1)) ∘
      map hdim x o a b ha hb ∘ facePoint hdim x o =
      RealForestFaceChangeVariables.map hdim x o a b ha hb := by
    funext w
    change ForestRadialFaceImmersion.faceProjection 0 (map hdim x o a b ha hb (facePoint hdim x o w)) = _
    rw [map_face]
    ext j
    simp [ForestRadialFaceImmersion.faceProjection, faceEmbedding]
  rw [he] at h
  exact h.fderiv.symm

include ho in
theorem jacobian_eq_normal_mul_face :
    OrientedFormChangeVariables.jacobian (map hdim x o a b ha hb) (facePoint hdim x o z.val) =
      (-1 : ℝ) ^ (axis hdim x o).val * normalScale hdim x o a b (facePoint hdim x o z.val) *
        RealForestFaceChangeVariables.jacobian hdim x o a b ha hb z.val := by
  rw [OrientedFormChangeVariables.jacobian,
    RadialFaceJacobian.det_eq_normal_mul_face _ 0 _ _ (normal_differential hdim x o a b ha hb ho z),
    face_derivative hdim x o a b ha hb ho z]
  simp only [Fin.val_zero, Nat.zero_add, RealForestFaceChangeVariables.jacobian]

include ho hne in
theorem jacobian_ne_zero :
    OrientedFormChangeVariables.jacobian (map hdim x o a b ha hb) (facePoint hdim x o z.val) ≠ 0 := by
  rw [jacobian_eq_normal_mul_face hdim x o a b ha hb ho z]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (normalScale_face_pos hdim x o ho a b ha hb z).ne')
    (RealForestFaceChangeVariables.jacobian_ne_zero hdim x o a b ha hb ho hne z)

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFullJacobian
