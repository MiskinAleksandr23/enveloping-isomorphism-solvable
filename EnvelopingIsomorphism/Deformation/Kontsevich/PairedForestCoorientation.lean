import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestFaceJacobian

/-! The global positive-chart orientation certificate extends to the actual
paired face along its inward radial path. The normal multiplier is the proved
positive native geometric scale, and both outward coordinate signs remain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestFullOverlap
open BoxStokes OrientedFormChangeVariables ForestRadialFaceClassification
open OrthantInteriorIntegration CompactOrthantStokes
open ForestChartOrientation ForestGlobalGraphStokes RadialFaceJacobian
open Set Filter
open scoped Classical Topology ContDiff
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

/-- Vary only the selected native radius, keeping all other actual face coordinates fixed. -/
def inward (z : Coord r) (t : ℝ) : Coord (r + 1) := faceEmbedding (axis hdim x o) t z

theorem continuous_inward (z : Coord r) : Continuous (inward hdim x o z) :=
  by
    unfold inward faceEmbedding
    exact Continuous.finInsertNth (A := fun _ : Fin (r + 1) ↦ ℝ) (axis hdim x o)
      continuous_id (show Continuous (fun _ : ℝ ↦ z) from continuous_const)

theorem inward_tendsto (z : Source hdim x o) :
    Tendsto (inward hdim x o z.val) (𝓝[>] (0 : ℝ)) (𝓝 (facePoint hdim x o z)) :=
  (continuous_inward hdim x o z.val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem inward_strictOrthant (z : Source hdim x o) {t : ℝ} (ht : 0 < t) :
    inward hdim x o z.val t ∈ strictOrthant (radialIndices hdim x) := by
  intro j hj
  induction j using (axis hdim x o).succAboveCases with
  | x => simpa [inward, faceEmbedding] using ht
  | p k =>
    have hk : k ∈ faceIndices (radialIndices hdim x) (axis hdim x o) :=
      (mem_faceIndices _ _ _).mpr hj
    simpa [inward, faceEmbedding] using z.property.1 k hk

/-- The support-relevant small chart condition is exactly the original ambient ball. -/
def SmallFace (z : Source hdim x o) : Prop :=
  (sourceCoordinates hdim x).symm (facePoint hdim x o z) ∈
    Metric.ball (center 0 x) (radius 0 x)

theorem inward_eventually_positiveRegion (z : Source hdim x o) (hz : SmallFace hdim x o z) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), inward hdim x o z.val t ∈ positiveRegion hdim x := by
  have hc := (sourceCoordinates hdim x).symm.continuous.continuousAt.tendsto.comp (inward_tendsto hdim x o z)
  filter_upwards [hc (Metric.isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with t ht hpos
  refine ⟨ht, ?_⟩
  have h := (sourceCoordinates_mem_strictOrthant hdim x
    ((sourceCoordinates hdim x).symm (inward hdim x o z.val t))).mp ?_
  · exact h
  · rw [ContinuousLinearEquiv.apply_symm_apply]
    exact inward_strictOrthant hdim x o z hpos

private theorem cancel_positive_physical_factor (ε δ P J : ℝ) (hδ : δ * δ = 1) (hP : 0 < P)
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

theorem contDiffAt_overlap_of_slit (z : Source hdim x o) (u : Circle)
    (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane) :
    ContDiffAt ℝ ⊤ (overlap hdim x o ho u) (facePoint hdim x o z) := by
  have ha : ContDiffAt ℝ ⊤ (angle hdim x o ho u) (facePoint hdim x o z) :=
    contDiffAt_const.add ((ForestShapeProjectionSmooth.contDiffAt_angleInverseRaw u _ hslit).comp (facePoint hdim x o z)
      (contDiffAt_rawVelocity hdim x o ho z (reference x o ho)))
  have hf : ContDiffAt ℝ ⊤ (fullToProduct hdim x o ho u) (facePoint hdim x o z) := by
    apply ContDiffAt.prodMk
    · apply ContDiffAt.prodMk ha
      apply contDiffAt_pi.mpr
      intro j
      simpa only [div_eq_mul_inv, Pi.inv_apply] using
        (contDiffAt_rawVelocity hdim x o ho z (InteriorGraphFaceCoordinates.shapeEnum.symm j).val).mul
          ((contDiffAt_rawVelocity hdim x o ho z (reference x o ho)).inv (phase hdim x o ho z).coe_ne_zero)
    · exact (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBase hdim x o ho z
        (InteriorGraphFaceCoordinates.coarseEnum.symm j).val).prodMk
          (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBoundary hdim x o ho z j)
  have hq := InteriorGraphFaceCoordinates.contDiff_toAngular.contDiffAt.comp (facePoint hdim x o z) hf
  have hr : ContDiffAt ℝ ⊤ (PairedForestNormalScale.simpleRadius hdim x o ho) (facePoint hdim x o z) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r + 1) ↦ ℝ) (axis hdim x o)).contDiff.contDiffAt).mul
      (PairedForestNormalScale.contDiffAt_normalScale hdim x o ho z)
  exact hq.fst.prodMk (hq.snd.fst.prodMk (hq.snd.snd.fst.prodMk (hq.snd.snd.snd.fst.prodMk hr)))

theorem contDiffAt_realOverlap_of_slit (z : Source hdim x o) (u : Circle)
    (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane) :
    ContDiffAt ℝ ⊤ (realOverlap hdim x o ho u) (facePoint hdim x o z) :=
  (simpleCoordinates hdim x o ho).contDiff.contDiffAt.comp _ (contDiffAt_overlap_of_slit hdim x o ho z u hslit)

/-- The existing full-chart sign determines the actual overlap sign at the
face. It is transported by a genuine inward path, not assumed at radius zero. -/
theorem full_orientation_at_face_of_slit (z : Source hdim x o) (hz : SmallFace hdim x o z)
    (u : Circle) (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane)
    (ε : ℝ) (hε : ∀ y ∈ positiveRegion hdim x,
      ε * jacobian (chart hdim x) y = |jacobian (chart hdim x) y|) :
    ε * jacobian (realOverlap hdim x o ho u) (facePoint hdim x o z) =
      simpleSign (m := m) x o ho *
        |jacobian (realOverlap hdim x o ho u) (facePoint hdim x o z)| := by
  let f := realOverlap hdim x o ho u
  have ht := inward_tendsto hdim x o z
  have hheight := ht.eventually ((contDiff_rawHeight hdim x o).continuous.continuousAt.eventually_ne
    (rawHeight_pos hdim x o ho z).ne')
  have hR : Continuous (rawShapeRadius hdim x o ho) :=
    ((contDiff_rawShape hdim x o ho (reference x o ho)).continuous.sub
      (contDiff_rawShape hdim x o ho (anchor x o ho)).continuous).norm
  have hshape := ht.eventually (hR.continuousAt.eventually (isOpen_Ioi.mem_nhds (rawShapeRadius_pos hdim x o ho z)))
  have hnorm := ht.eventually ((PairedForestNormalScale.contDiffAt_normalScale hdim x o ho z).continuousAt.eventually
    (isOpen_Ioi.mem_nhds (PairedForestNormalScale.normalScale_face_pos hdim x o ho z)))
  have hdiff := ht.eventually (((contDiffAt_overlap_of_slit hdim x o ho z u hslit).of_le (show (1 : ℕ∞ω) ≤ ⊤ by simp)).eventually (by simp))
  have heq : (fun t ↦ ε * jacobian f (inward hdim x o z.val t)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t ↦ simpleSign (m := m) x o ho * |jacobian f (inward hdim x o z.val t)|) := by
    filter_upwards [inward_eventually_positiveRegion hdim x o z hz, hheight, hshape, hnorm, hdiff,
      self_mem_nhdsWithin] with t hregion hh hr hn hd htpos
    have h := hε _ hregion
    rw [jacobian_chart_factor hdim x o ho _ _ hh hr (hd.differentiableAt (by simp))] at h
    apply cancel_positive_physical_factor ε (simpleSign (m := m) x o ho) _ _ (simpleSign_sq x o ho) _ h
    apply pow_pos
    change 0 < inward hdim x o z.val t (axis hdim x o) * _
    simpa [inward, faceEmbedding] using mul_pos htpos hn
  have hJ : ContinuousAt (jacobian f) (facePoint hdim x o z) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((contDiffAt_realOverlap_of_slit hdim x o ho z u hslit).continuousAt_fderiv (by simp))
  have hL := (hJ.const_mul ε).tendsto.comp ht
  have hR := (hJ.abs.const_mul (simpleSign (m := m) x o ho)).tendsto.comp ht
  exact tendsto_nhds_unique hL (hR.congr' heq.symm)

theorem full_orientation_at_face (z : Source hdim x o) (hz : SmallFace hdim x o z)
    (ε : ℝ) (hε : ∀ y ∈ positiveRegion hdim x,
      ε * jacobian (chart hdim x) y = |jacobian (chart hdim x) y|) :
    ε * jacobian (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) =
      simpleSign (m := m) x o ho *
        |jacobian (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z)| :=
  full_orientation_at_face_of_slit hdim x o ho z hz (phase hdim x o ho z)
    (by simp [(phase hdim x o ho z).coe_ne_zero]) ε hε

/-- Final exact coorientation certificate for the actual native face map. -/
theorem native_face_orientation (z : Source hdim x o) (hz : SmallFace hdim x o z)
    (ε : ℝ) (hε : ∀ y ∈ positiveRegion hdim x,
      ε * jacobian (chart hdim x) y = |jacobian (chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
        jacobian (nativeFaceMap hdim x o ho (phase hdim x o ho z)) z.val =
      simpleSign (m := m) x o ho * (-((-1 : ℝ) ^ r)) *
        |jacobian (nativeFaceMap hdim x o ho (phase hdim x o ho z)) z.val| := by
  have h := outward_sign_transport (axis hdim x o) (Fin.last r)
    (fderiv ℝ (realOverlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z))
    (PairedForestNormalScale.normalScale hdim x o ho (facePoint hdim x o z))
    (PairedForestNormalScale.normalScale_face_pos hdim x o ho z)
    (normal_differential hdim x o ho z) ε (simpleSign (m := m) x o ho)
    (full_orientation_at_face hdim x o ho z hz ε hε)
  rw [← fderiv_nativeFaceMap] at h
  exact h

/-- The same normal identity for every valid fixed phase branch of a local chart. -/
theorem normal_differential_of_slit (z : Source hdim x o) (u : Circle)
    (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane) (v : Coord (r + 1)) :
    fderiv ℝ (realOverlap hdim x o ho u) (facePoint hdim x o z) v (Fin.last r) =
      PairedForestNormalScale.normalScale hdim x o ho (facePoint hdim x o z) * v (axis hdim x o) := by
  let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r + 1) ↦ ℝ) (Fin.last r)
  have h := (proj.hasFDerivAt.comp (facePoint hdim x o z)
    ((contDiffAt_realOverlap_of_slit hdim x o ho z u hslit).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : proj ∘ realOverlap hdim x o ho u = PairedForestNormalScale.simpleRadius hdim x o ho :=
    funext (realOverlap_radius hdim x o ho u)
  rw [he] at h
  have hr := PairedForestNormalScale.fderiv_simpleRadius_face hdim x o ho z
  change fderiv ℝ (PairedForestNormalScale.simpleRadius hdim x o ho) (facePoint hdim x o z) = _ at hr
  rw [hr] at h
  exact (congrArg (fun L : Coord (r + 1) →L[ℝ] ℝ ↦ L v) h).symm

theorem fderiv_nativeFaceMap_of_slit (z : Source hdim x o) (u : Circle)
    (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane) :
    fderiv ℝ (nativeFaceMap hdim x o ho u) z.val = faceDerivative (axis hdim x o) (Fin.last r)
      (fderiv ℝ (realOverlap hdim x o ho u) (facePoint hdim x o z)) := by
  have h := (ForestRadialFaceImmersion.faceProjection (Fin.last r)).hasFDerivAt.comp z.val
    ((((contDiffAt_realOverlap_of_slit hdim x o ho z u hslit).differentiableAt (by simp)).hasFDerivAt).comp z.val
      (faceTangent (axis hdim x o)).hasFDerivAt)
  exact h.fderiv

/-- Signed native face transport in a fixed local phase chart. Every analytic
and normal-orientation premise is supplied by the actual paired geometry. -/
theorem native_face_orientation_of_slit (z : Source hdim x o) (hz : SmallFace hdim x o z)
    (u : Circle) (hslit : (u : ℂ)⁻¹ * (phase hdim x o ho z : ℂ) ∈ Complex.slitPlane)
    (ε : ℝ) (hε : ∀ y ∈ positiveRegion hdim x,
      ε * jacobian (chart hdim x) y = |jacobian (chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) * jacobian (nativeFaceMap hdim x o ho u) z.val =
      simpleSign (m := m) x o ho * (-((-1 : ℝ) ^ r)) * |jacobian (nativeFaceMap hdim x o ho u) z.val| := by
  have h := outward_sign_transport (axis hdim x o) (Fin.last r)
    (fderiv ℝ (realOverlap hdim x o ho u) (facePoint hdim x o z))
    (PairedForestNormalScale.normalScale hdim x o ho (facePoint hdim x o z))
    (PairedForestNormalScale.normalScale_face_pos hdim x o ho z)
    (normal_differential_of_slit hdim x o ho z u hslit) ε (simpleSign (m := m) x o ho)
    (full_orientation_at_face_of_slit hdim x o ho z hz u hslit ε hε)
  rw [← fderiv_nativeFaceMap_of_slit hdim x o ho z u hslit] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestOverlapJacobian
