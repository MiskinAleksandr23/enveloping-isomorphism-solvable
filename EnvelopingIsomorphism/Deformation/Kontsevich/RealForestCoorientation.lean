import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalFactor
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoorientation

/-! The original orientation certificate determines the actual proper-real
face sign through physical insertion, positive outside-anchor normalization,
and the genuine inward path. No face-orientation contract is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoorientation
open Configuration ForestRadialFaceClassification BoxStokes RealForestNormalScale
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestFullOverlap RealForestFullJacobian RealForestPhysicalFactor
open OrientedFormChangeVariables
open scoped Classical Topology ContDiff
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (ho : RealForestCoarsePositions.IsFixed x o)

private theorem cancel_positive_factor (ε δ P J : ℝ) (hδ : δ * δ = 1) (hP : 0 < P)
    (h : ε * (δ * P * J) = |δ * P * J|) : ε * J = δ * |J| := by
  have hδabs : |δ| = 1 := by
    rcases mul_self_eq_one_iff.mp hδ with h | h <;> rw [h] <;> norm_num
  rw [abs_mul, abs_mul, hδabs, one_mul, abs_of_pos hP] at h
  apply mul_left_cancel₀ hP.ne'
  calc
    P * (ε * J) = δ * (ε * (δ * P * J)) := by
      calc
        _ = (P * (ε * J)) * (δ * δ) := by rw [hδ, mul_one]
        _ = _ := by ring
    _ = δ * (P * |J|) := congrArg (fun t ↦ δ * t) h
    _ = P * (δ * |J|) := by ring

include ho ha hb in
theorem orientation_at_positive_point (y : Coord (r+1))
    (hy : y ∈ ForestGlobalGraphStokes.positiveRegion hdim x)
    (hB : 0 < height hdim x b y) (hA : 0 < shapeHeight hdim x o a y)
    (hR : 0 < simpleRadius hdim x o a b y)
    (hd : DifferentiableAt ℝ (overlap hdim x o a b) y)
    (ε : ℝ) (hε : ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
      |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (RealForestFullJacobian.map hdim x o a b ha hb) y =
      physicalSign hdim x o a b ha hb * |jacobian (RealForestFullJacobian.map hdim x o a b ha hb) y| := by
  have hsource : (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm y ∈ ForestPositiveChartSmooth.Source 0 x := by
    simpa only [ForestGlobalGraphStokes.chart_source, Set.mem_preimage] using
      ForestGlobalGraphStokes.positiveRegion_subset_source hdim x hy
  have h0 : 0 < height hdim x 0 y :=
    ForestPositiveChartSmooth.anchorPoint_im_pos 0 x _ hsource
  have hbpos : 0 < (GraphForms.interiorPoint b (originalCoordinates hdim x y)).im := by
    rw [originalCoordinates_interior hdim x y h0, RealForestSimpleCluster.normalize_im]
    exact div_pos hB h0
  have hN : 0 < 1 / (GraphForms.interiorPoint b (originalCoordinates hdim x y)).im ^ (GraphForms.dimension n m + 1) := by
    positivity
  have hn : ε * jacobian (normalizedChart hdim x b) y = |jacobian (normalizedChart hdim x b) y| := by
    rw [jacobian_normalized_original hdim x b y h0 hB, abs_mul, abs_of_pos hN]
    calc
      _ = (1 / (GraphForms.interiorPoint b (originalCoordinates hdim x y)).im ^ (GraphForms.dimension n m + 1)) *
          (ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y) := by ring
      _ = _ := by rw [hε]
  rw [jacobian_normalized_physical hdim x o a b ha hb ho y h0 hB hA hd] at hn
  let K := (physicalOutput hdim x o a b ha hb).toLinearMap.det
  let P := (simpleRadius hdim x o a b y) ^
    (2 * (labelsSet x o).card + (boundaryClusterBlock (lower x o) (upper x o)).card - 2)
  have hK : K ≠ 0 := physicalOutput_det_ne_zero hdim x o a b ha hb
  have hP : 0 < |K| * P := mul_pos (abs_pos.mpr hK) (pow_pos hR _)
  apply cancel_positive_factor ε (physicalSign hdim x o a b ha hb) (|K| * P) _
    (physicalSign_sq hdim x o a b ha hb) hP
  have he : physicalSign hdim x o a b ha hb * (|K| * P) = K * P := by
    unfold physicalSign
    dsimp only [K]
    have hn := abs_ne_zero.mpr (physicalOutput_det_ne_zero hdim x o a b ha hb)
    field_simp [hn]
  rw [he]
  exact hn

include ho ha hb in
/-- The existing original-chart certificate reaches radius zero along the
actual inward collar. The multiplier is an explicit physical coordinate determinant. -/
theorem full_orientation_at_face (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * jacobian (RealForestFullJacobian.map hdim x o a b ha hb) (facePoint hdim x o z.val) =
      physicalSign hdim x o a b ha hb *
        |jacobian (RealForestFullJacobian.map hdim x o a b ha hb) (facePoint hdim x o z.val)| := by
  let f := RealForestFullJacobian.map hdim x o a b ha hb
  have ht := PairedForestOverlapJacobian.inward_tendsto hdim x o z
  have hB := ht.eventually ((contDiff_height hdim x b).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (RealForestSimpleCluster.coarseAnchor_pos hdim x o ho b hb z)))
  have hA := ht.eventually ((contDiff_shapeHeight hdim x o a).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (RealForestSimpleCluster.shapeAnchor_pos hdim x o ho a ha z)))
  have hR := ht.eventually ((contDiffAt_normalScale hdim x o ho a b hb z).continuousAt.eventually
    (isOpen_Ioi.mem_nhds (normalScale_face_pos hdim x o ho a b ha hb z)))
  have hdiff := ht.eventually (((contDiffAt_overlap hdim x o a b ho ha hb z).of_le
    (show (1 : ℕ∞ω) ≤ ⊤ by simp)).eventually (by simp))
  have heq : (fun t => ε * jacobian f (PairedForestOverlapJacobian.inward hdim x o z.val t)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t => physicalSign hdim x o a b ha hb *
        |jacobian f (PairedForestOverlapJacobian.inward hdim x o z.val t)|) := by
    filter_upwards [PairedForestOverlapJacobian.inward_eventually_positiveRegion hdim x o z hz,
      hB, hA, hR, hdiff, self_mem_nhdsWithin] with t hregion hb' ha' hr hd htpos
    apply orientation_at_positive_point hdim x o a b ha hb ho _ hregion hb' ha' _
      (hd.differentiableAt (by simp)) ε (hε _ hregion)
    change 0 < PairedForestOverlapJacobian.inward hdim x o z.val t (axis hdim x o) * _
    simpa [PairedForestOverlapJacobian.inward, faceEmbedding] using mul_pos htpos hr
  have hJ : ContinuousAt (jacobian f) (facePoint hdim x o z.val) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((RealForestFullJacobian.contDiffAt_map hdim x o a b ha hb ho z).continuousAt_fderiv (by simp))
  exact tendsto_nhds_unique ((hJ.const_mul ε).tendsto.comp ht)
    ((hJ.abs.const_mul (physicalSign hdim x o a b ha hb)).tendsto.comp ht |>.congr' heq.symm)

include ho ha hb in
/-- Proper-real outward coorientation in the genuine radius-first native
face basis, derived from the original orientation and positive normal scale. -/
theorem native_face_orientation (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      RealForestFaceChangeVariables.jacobian hdim x o a b ha hb z.val =
      -physicalSign hdim x o a b ha hb *
        |RealForestFaceChangeVariables.jacobian hdim x o a b ha hb z.val| := by
  have h := RadialFaceJacobian.outward_sign_transport (axis hdim x o) 0
    (fderiv ℝ (RealForestFullJacobian.map hdim x o a b ha hb) (facePoint hdim x o z.val))
    (normalScale hdim x o a b (facePoint hdim x o z.val))
    (normalScale_face_pos hdim x o ho a b ha hb z)
    (RealForestFullJacobian.normal_differential hdim x o a b ha hb ho z) ε
    (physicalSign hdim x o a b ha hb)
    (full_orientation_at_face hdim x o a b ha hb ho z hz ε hε)
  rw [RealForestFullJacobian.face_derivative hdim x o a b ha hb ho z] at h
  simpa only [Fin.val_zero, pow_zero, neg_mul, mul_neg, mul_one,
    RealForestFaceChangeVariables.jacobian] using h

include ho ha hb in
/-- Signed weighted graph-form transport with the actual coorientation
supplied above. The proper-real face sign is no longer a caller hypothesis. -/
theorem signed_weighted_graph_integral
    (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
    (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (hsmall : ∀ w (hw : w ∈ s), PairedForestOverlapJacobian.SmallFace hdim x o ⟨w,hsub hw⟩)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (ε * (-((-1 : ℝ) ^ (axis hdim x o).val))) *
      (∫ w in s, κ w * density (RealForestFaceChangeVariables.nativeForm hdim x o edges) w) =
    -physicalSign hdim x o a b ha hb *
      (∫ y in RealForestFaceChangeVariables.map hdim x o a b ha hb '' s,
        κ (RealForestFaceChangeVariables.inverseReal hdim x o a b ha hb y) *
          density (RealForestFaceChangeVariables.simpleForm hdim x o a b ha hb edges) y) := by
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    RealForestFaceChangeVariables.integral_image_source hdim x o a b ha hb ho hne s hs hsub]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro w hw
  dsimp only
  rw [RealForestFaceChangeVariables.inverseReal_map hdim x o a b ha hb ho hne ⟨w,hsub hw⟩,
    RealForestFaceChangeVariables.native_density_eq_jacobian hdim x o a b ha hb ho hne ⟨w,hsub hw⟩]
  have h := native_face_orientation hdim x o a b ha hb ho ⟨w,hsub hw⟩ (hsmall w hw) ε hε
  linear_combination (κ w * density (RealForestFaceChangeVariables.simpleForm hdim x o a b ha hb edges)
    (RealForestFaceChangeVariables.map hdim x o a b ha hb w)) * h

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoorientation
