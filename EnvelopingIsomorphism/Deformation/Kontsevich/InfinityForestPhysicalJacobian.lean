import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
import Mathlib.Analysis.Calculus.Deriv.Abs
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoorientation
import Mathlib.Topology.Instances.Sign

/-! Exact reciprocal-coordinate Jacobian of the full infinity extraction.
The remaining determinant is one explicitly defined linear coordinate map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
open Configuration ForestRadialFaceClassification BoxStokes RealForestNormalScale
open OrientedFormChangeVariables
open InfinityForestSimpleCluster (lower upper)
open scoped Classical Topology

private def reciprocalFirst {r : ℕ} (y : Coord (r+1)) : Coord (r+1) :=
  Function.update y 0 (|y 0|⁻¹)

private def firstDerivative {r : ℕ} (c : ℝ) : Coord (r+1) →L[ℝ] Coord (r+1) :=
  ContinuousLinearMap.pi fun j ↦ if j = 0 then c • ContinuousLinearMap.proj 0 else ContinuousLinearMap.proj j

private theorem hasFDerivAt_reciprocalFirst {r : ℕ} (y : Coord (r+1)) (hy : y 0 ≠ 0) :
    HasFDerivAt reciprocalFirst (firstDerivative (r := r) (-(SignType.sign (y 0) : ℝ) / |y 0|^2)) y := by
  apply hasFDerivAt_pi.mpr
  intro j
  by_cases hj : j = 0
  · subst j
    have h := ((hasDerivAt_abs hy).inv (abs_ne_zero.mpr hy)).comp_hasFDerivAt y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) 0).hasFDerivAt
    simpa [reciprocalFirst, firstDerivative, Function.comp_def, Pi.inv_apply] using h
  · simp only [reciprocalFirst, Function.update_of_ne hj, firstDerivative,
      ContinuousLinearMap.pi_apply, if_neg hj]
    convert (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r+1) ↦ ℝ) j).hasFDerivAt (x := y) using 1 <;> rfl

private theorem det_firstDerivative {r : ℕ} (c : ℝ) : (firstDerivative (r := r) c).det = c := by
  change LinearMap.det (firstDerivative (r := r) c).toLinearMap = c
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (firstDerivative (r := r) c).toLinearMap =
      Matrix.diagonal (fun j : Fin (r+1) ↦ if j = 0 then c else 1) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, firstDerivative, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.pi_apply, Matrix.diagonal_apply]
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j; simp
      · simp [hj, Ne.symm hj, Pi.single_apply]
    · by_cases hj : i = j
      · subst j
        simp [hi, Pi.single_apply]
      · simp [hi, hj, Ne.symm hj, Pi.single_apply]
  rw [hm, Matrix.det_diagonal]
  simp

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

def linearExtraction : Coord (r+1) →L[ℝ] Coord (r+1) :=
  (ContinuousLinearMap.pi fun j ↦ Fin.cases
    ((ContinuousLinearMap.proj q).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin m → ℝ)))
    (fun k ↦ (ContinuousLinearMap.proj k).comp
      ((InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall).toContinuousLinearMap.comp
        (physicalFace x o q))) j).comp
    (ForestGlobalGraphStokes.nativeCoordinates hdim).symm.toContinuousLinearMap

def realExtraction (y : Coord (r+1)) : Coord (r+1) :=
  reciprocalExtraction hdim x o q ho hq hne hall ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y)

private theorem realExtraction_eq : realExtraction hdim x o q ho hq hne hall =
    reciprocalFirst ∘ linearExtraction hdim x o q ho hq hne hall := by
  funext y
  ext j
  cases j using Fin.cases with
  | zero => simp [realExtraction, reciprocalExtraction, reciprocalFirst, linearExtraction, faceEmbedding]
  | succ j => simp [realExtraction, reciprocalExtraction, reciprocalFirst, linearExtraction,
      faceEmbedding, Fin.insertNth_zero']

/-- Exact determinant: reciprocal of the absolute outside coordinate supplies
its computed derivative, while every remaining coordinate is linear. -/
theorem jacobian_realExtraction (y : Coord (r+1))
    (hy : ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 q ≠ 0) :
    jacobian (realExtraction hdim x o q ho hq hne hall) y =
      (-(SignType.sign (((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 q) : ℝ) /
        |((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 q|^2) *
      (linearExtraction hdim x o q ho hq hne hall).det := by
  have hy' : linearExtraction hdim x o q ho hq hne hall y 0 ≠ 0 := hy
  have h := (hasFDerivAt_reciprocalFirst _ hy').comp y
    (linearExtraction hdim x o q ho hq hne hall).hasFDerivAt
  rw [← realExtraction_eq hdim x o q ho hq hne hall] at h
  unfold jacobian
  rw [h.fderiv]
  change LinearMap.det ((firstDerivative _).toLinearMap.comp
    (linearExtraction hdim x o q ho hq hne hall).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (firstDerivative (r := r) _).det * (linearExtraction hdim x o q ho hq hne hall).det = _
  rw [det_firstDerivative]
  rfl

include ho hq hne hall in
/-- The actual full extraction agrees locally with the explicit reciprocal
physical-coordinate map, so this is an equality of actual derivatives. -/
theorem jacobian_factor (y : Coord (r+1))
    (ht : y (axis hdim x o) * parentScale hdim x o y ≠ 0)
    (hu : shapeHeight hdim x o 0 y ≠ 0) (hh : 0 < height hdim x 0 y)
    (hqraw : InfinityForestNormalScale.offset hdim x q y ≠ 0) :
    jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) y =
      (-(SignType.sign ((ForestPositiveChartSmooth.forwardCoordinates 0 x
          ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).2 q) : ℝ) /
        |(ForestPositiveChartSmooth.forwardCoordinates 0 x
          ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).2 q|^2) *
      (linearExtraction hdim x o q ho hq hne hall).det *
      jacobian (ForestGlobalGraphStokes.chart hdim x) y := by
  have he : InfinityForestFullOverlap.map hdim x o q ho hq hne hall =ᶠ[nhds y]
      realExtraction hdim x o q ho hq hne hall ∘ ForestGlobalGraphStokes.chart hdim x := by
    have ht' := ((continuous_apply (axis hdim x o)).mul (contDiff_parentScale hdim x o).continuous).continuousAt.eventually_ne ht
    have hu' := (contDiff_shapeHeight hdim x o 0).continuous.continuousAt.eventually_ne hu
    have hh' := (contDiff_height hdim x 0).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hh)
    filter_upwards [ht',hu',hh'] with w hw₁ hw₂ hw₃
    rw [map_eq_reciprocalExtraction hdim x o q ho hq hne hall w hw₁ hw₂ hw₃]
    simp [realExtraction, ForestGlobalGraphStokes.chart_apply]
  have hc : ContDiffAt ℝ ⊤ (ForestGlobalGraphStokes.chart hdim x) y :=
    (ForestGlobalGraphStokes.nativeCoordinates hdim).contDiff.contDiffAt.comp _
      ((ForestPositiveChartSmooth.contDiffAt_forwardCoordinates 0 x _ hh.ne').comp _
        (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff.contDiffAt)
  have hq' : ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm (ForestGlobalGraphStokes.chart hdim x y)).2 q ≠ 0 := by
    rw [ForestGlobalGraphStokes.chart_apply, ContinuousLinearEquiv.symm_apply_apply]
    change InfinityForestNormalScale.offset hdim x q y / height hdim x 0 y ≠ 0
    exact div_ne_zero hqraw hh.ne'
  have hr := (hasFDerivAt_reciprocalFirst
    (linearExtraction hdim x o q ho hq hne hall (ForestGlobalGraphStokes.chart hdim x y)) hq').comp _
      (linearExtraction hdim x o q ho hq hne hall).hasFDerivAt
  rw [← realExtraction_eq hdim x o q ho hq hne hall] at hr
  have hd := (hr.differentiableAt.hasFDerivAt.comp y (hc.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [← he.fderiv_eq] at hd
  unfold jacobian
  rw [hd]
  change LinearMap.det ((fderiv ℝ (realExtraction hdim x o q ho hq hne hall)
    (ForestGlobalGraphStokes.chart hdim x y)).toLinearMap.comp
      (fderiv ℝ (ForestGlobalGraphStokes.chart hdim x) y).toLinearMap) = _
  rw [LinearMap.det_comp]
  change jacobian (realExtraction hdim x o q ho hq hne hall) (ForestGlobalGraphStokes.chart hdim x y) *
    jacobian (ForestGlobalGraphStokes.chart hdim x) y = _
  rw [jacobian_realExtraction hdim x o q ho hq hne hall _ hq',
    ForestGlobalGraphStokes.chart_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

private theorem signed_factor (ε A J : ℝ) (h : ε * J = |J|) :
    ε * (A * J) = (SignType.sign A : ℝ) * |A * J| := by
  rw [abs_mul]
  calc
    _ = A * (ε * J) := by ring
    _ = A * |J| := by rw [h]
    _ = _ := by rw [← mul_assoc, sign_mul_abs]

private theorem reciprocal_sign (t d : ℝ) (ht : t ≠ 0) :
    (SignType.sign ((-(SignType.sign t : ℝ) / |t|^2) * d) : ℝ) =
      -(SignType.sign t : ℝ) * (SignType.sign d : ℝ) := by
  rw [sign_mul, SignType.coe_mul]
  have hd : 0 < |t|^2 := sq_pos_of_pos (abs_pos.mpr ht)
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hc : 0 < -(SignType.sign t : ℝ) / |t|^2 := by
      rw [sign_neg ht]
      simpa using div_pos (show (0 : ℝ) < 1 by norm_num) hd
    rw [sign_pos hc, sign_neg ht]
    simp
  · have hc : -(SignType.sign t : ℝ) / |t|^2 < 0 := by
      rw [sign_pos ht]
      simpa using div_neg_of_neg_of_pos (show (-1 : ℝ) < 0 by norm_num) hd
    rw [sign_neg hc, sign_pos ht]
    simp

include ho hq hne hall in
/-- The original chart orientation determines the actual full infinity
collar orientation through the computed reciprocal derivative. -/
theorem full_orientation_in_collar (y : Coord (r+1))
    (ht : y (axis hdim x o) * parentScale hdim x o y ≠ 0)
    (hu : shapeHeight hdim x o 0 y ≠ 0) (hh : 0 < height hdim x 0 y)
    (hqraw : InfinityForestNormalScale.offset hdim x q y ≠ 0)
    (ε : ℝ) (hε : ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
      |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) y =
      (-(SignType.sign ((ForestPositiveChartSmooth.forwardCoordinates 0 x
        ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).2 q) : ℝ) *
        (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ)) *
      |jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) y| := by
  have hq' : (ForestPositiveChartSmooth.forwardCoordinates 0 x
      ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).2 q ≠ 0 := by
    change InfinityForestNormalScale.offset hdim x q y / height hdim x 0 y ≠ 0
    exact div_ne_zero hqraw hh.ne'
  rw [jacobian_factor hdim x o q ho hq hne hall y ht hu hh hqraw]
  rw [← reciprocal_sign ((ForestPositiveChartSmooth.forwardCoordinates 0 x
    ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y)).2 q)
    (linearExtraction hdim x o q ho hq hne hall).det hq']
  exact signed_factor ε _ _ hε

include ho in
private theorem height_factor (y : Coord (r+1)) : height hdim x 0 y =
    y (axis hdim x o) * parentScale hdim x o y * shapeHeight hdim x o 0 y := by
  have hi := congrArg Complex.im (position_inside_factor hdim x o y (Sum.inl (Sum.inl 0))
    ((ForestRadialClusterLabels.mem_interiorLabels 0 x _ _).mp (InfinityForestSimpleCluster.interior_mem x o ho 0)))
  rw [nodePosition_real hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) y] at hi
  simpa only [height, shapeHeight, Complex.add_im, Complex.ofReal_im, zero_add, Complex.real_smul,
    Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] using hi

private theorem sign_div_positive (t h : ℝ) (ht : t ≠ 0) (hh : 0 < h) :
    SignType.sign (t/h) = SignType.sign t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [sign_neg (div_neg_of_neg_of_pos ht hh), sign_neg ht]
  · rw [sign_pos (div_pos ht hh), sign_pos ht]

include ho hq hne hall in
/-- The full infinity sign reaches radius zero along the genuine inward
path. Its only remaining combinatorics is the concrete linear extraction. -/
theorem full_orientation_at_face (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) (facePoint hdim x o z.val) =
      (-(SignType.sign (InfinityForestSimpleCluster.offset hdim x o z q) : ℝ) *
        (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ)) *
      |jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) (facePoint hdim x o z.val)| := by
  have ht := PairedForestOverlapJacobian.inward_tendsto hdim x o z
  have hp : 0 < parentScale hdim x o (facePoint hdim x o z.val) :=
    parentScale_face_pos hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) z
  have hs : 0 < shapeHeight hdim x o 0 (facePoint hdim x o z.val) :=
    InfinityForestSimpleCluster.shapeAnchor_pos hdim x o ho z
  have hq0 : InfinityForestNormalScale.offset hdim x q (facePoint hdim x o z.val) ≠ 0 := by
    rw [InfinityForestNormalScale.offset_face hdim x o ho z q]
    exact abs_pos.mp (InfinityForestSimpleCluster.coarseScale_pos hdim x o ho q hq hne z)
  have hparent := ht.eventually ((contDiff_parentScale hdim x o).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hp))
  have hshape := ht.eventually ((contDiff_shapeHeight hdim x o 0).continuous.continuousAt.eventually (isOpen_Ioi.mem_nhds hs))
  have hoffset := ht.eventually ((InfinityForestNormalScale.contDiff_offset hdim x q).continuous.continuousAt.eventually_ne hq0)
  have hsign := ht.eventually (((continuousAt_sign_of_ne_zero hq0).comp
    (InfinityForestNormalScale.contDiff_offset hdim x q).continuous.continuousAt).eventually
      (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton _)))
  have heq : (fun t ↦ ε * jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall)
      (PairedForestOverlapJacobian.inward hdim x o z.val t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun t ↦ (-(SignType.sign (InfinityForestSimpleCluster.offset hdim x o z q) : ℝ) *
        (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ)) *
        |jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall)
          (PairedForestOverlapJacobian.inward hdim x o z.val t)|) := by
    filter_upwards [hparent,hshape,hoffset,hsign,
      PairedForestOverlapJacobian.inward_eventually_positiveRegion hdim x o z hz,
      self_mem_nhdsWithin] with t hp hs hq' hsign hregion htpos
    have htp : 0 < PairedForestOverlapJacobian.inward hdim x o z.val t (axis hdim x o) *
        parentScale hdim x o (PairedForestOverlapJacobian.inward hdim x o z.val t) := by
      simpa only [PairedForestOverlapJacobian.inward, faceEmbedding, Fin.insertNth_apply_same] using mul_pos htpos hp
    have hh : 0 < height hdim x 0 (PairedForestOverlapJacobian.inward hdim x o z.val t) := by
      rw [height_factor hdim x o ho]
      exact mul_pos htp hs
    have h := full_orientation_in_collar hdim x o q ho hq hne hall _ htp.ne' hs.ne' hh hq' ε (hε _ hregion)
    change SignType.sign (InfinityForestNormalScale.offset hdim x q (PairedForestOverlapJacobian.inward hdim x o z.val t)) =
      SignType.sign (InfinityForestNormalScale.offset hdim x q (facePoint hdim x o z.val)) at hsign
    change ε * _ = (-(SignType.sign (InfinityForestNormalScale.offset hdim x q _ / height hdim x 0 _) : ℝ) * _) * _ at h
    rw [sign_div_positive _ _ hq' hh, hsign, InfinityForestNormalScale.offset_face hdim x o ho z q] at h
    exact h
  have hJ : ContinuousAt (jacobian (InfinityForestFullOverlap.map hdim x o q ho hq hne hall)) (facePoint hdim x o z.val) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((InfinityForestFullOverlap.contDiffAt_map hdim x o q ho hq hne hall z).continuousAt_fderiv (by simp))
  exact tendsto_nhds_unique ((hJ.const_mul ε).tendsto.comp ht)
    (((hJ.abs.const_mul _).tendsto.comp ht).congr' heq.symm)

include ho hq hne hall in
theorem native_face_orientation (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ)^(axis hdim x o).val)) *
      InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val =
      ((SignType.sign (InfinityForestSimpleCluster.offset hdim x o z q) : ℝ) *
        (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ)) *
      |InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val| := by
  have h := RadialFaceJacobian.outward_sign_transport (axis hdim x o) 0
    (fderiv ℝ (InfinityForestFullOverlap.map hdim x o q ho hq hne hall) (facePoint hdim x o z.val))
    (InfinityForestNormalScale.normalScale hdim x o q (facePoint hdim x o z.val))
    (InfinityForestNormalScale.normalScale_face_pos hdim x o q ho hq hne z)
    (InfinityForestFullOverlap.normal_differential hdim x o q ho hq hne hall z) ε _
    (full_orientation_at_face hdim x o q ho hq hne hall z hz ε hε)
  rw [InfinityForestFullOverlap.face_derivative hdim x o q ho hq hne hall z] at h
  simpa only [Fin.val_zero, pow_zero, neg_mul, mul_neg, mul_one, neg_neg,
    InfinityForestFaceChangeVariables.jacobian] using h

include ho hq hne in
theorem outside_offset_sign (z : ForestRadialFaceLocalization.source hdim x o) :
    (SignType.sign (InfinityForestSimpleCluster.offset hdim x o z q) : ℝ) =
      BoundaryAnchoredInfinityData.referenceSign (lower x o) q := by
  by_cases hleft : q.val < (lower x o).val
  · rw [sign_neg (InfinityForestSimpleCluster.offset_neg hdim x o ho hne z q hleft)]
    simp [BoundaryAnchoredInfinityData.referenceSign, hleft]
  · have hright : (upper x o).val ≤ q.val := by
      have hnot := hq
      simp only [mem_boundaryClusterBlock] at hnot
      omega
    rw [sign_pos (InfinityForestSimpleCluster.offset_pos hdim x o ho hne z q hright)]
    simp [BoundaryAnchoredInfinityData.referenceSign, hleft]

include ho hq hne hall in
theorem native_face_orientation_reference (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ)^(axis hdim x o).val)) *
      InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val =
      (BoundaryAnchoredInfinityData.referenceSign (lower x o) q *
        (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ)) *
      |InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val| := by
  rw [native_face_orientation hdim x o q ho hq hne hall z hz ε hε,
    outside_offset_sign hdim x o q ho hq hne z]

include ho hq hne hall in
/-- Exact remaining finite computation: the literal infinity slot sign is
now equivalent to the sign of the displayed linear extraction, with all
analytic, collar, and original-orientation statements already proved. -/
theorem native_face_orientation_slot_iff (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    (ε * (-((-1 : ℝ)^(axis hdim x o).val)) *
      InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val =
      (BoundaryAnchoredInfinityData.referenceSign (lower x o) q * (-1 : ℝ)^q.val) *
        |InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val|) ↔
      (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ) = (-1 : ℝ)^q.val := by
  rw [native_face_orientation_reference hdim x o q ho hq hne hall z hz ε hε]
  have hj := abs_ne_zero.mpr (InfinityForestFaceChangeVariables.jacobian_ne_zero hdim x o q ho hq hne hall z)
  have href : BoundaryAnchoredInfinityData.referenceSign (lower x o) q ≠ 0 := by
    unfold BoundaryAnchoredInfinityData.referenceSign
    split_ifs <;> norm_num
  constructor
  · intro h
    exact mul_left_cancel₀ href (mul_right_cancel₀ hj h)
  · intro h
    rw [h]

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
