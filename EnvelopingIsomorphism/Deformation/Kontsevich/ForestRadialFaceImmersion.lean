import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceDRInverse

/-! Actual smooth native face embedding and its explicit smooth left inverse.
The differential identity is derived on the open localized face source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion
open Configuration ExtractedForestParameters ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestRadialFaceDRInverse
open BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)

def forward (z : Coord r) : CompactDRCoordinates.Ambient (n + 1) m :=
  CompactDRCoordinates.forestAmbient (tree 0 x) (canonicalLeaf 0 x)
    (realization 0 x (faceAmbient hdim x o z))

def faceProjection (a : Fin (r + 1)) : Coord (r + 1) →L[ℝ] Coord r :=
  ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (a.succAbove j)

def inverse (d : CompactDRCoordinates.Ambient (n + 1) m) : Coord r :=
  faceProjection (axis hdim x o) (ForestGlobalGraphStokes.sourceCoordinates hdim x (inverseAmbient x o d))

theorem isOpen_source : IsOpen (Source hdim x o) := by
  apply (ForestRadialFaceLocalization.isOpen_strictFace hdim x o).inter
  exact (ForestOrthantCharts.chart 0 x).open_source.preimage
    ((ForestPositiveChartSmooth.continuous_ofAmbient 0 x).comp
      (ForestRadialFaceLocalization.continuous_faceAmbient hdim x o))

theorem forward_data (z : Source hdim x o) :
    forward hdim x o z.val = CompactDRCoordinates.dataEmbedding (data hdim x o z) := by
  have h := ambientDR_eq_chart 0 x (model hdim x o z) z.property.2
  rw [show includeOrthant 0 x (model hdim x o z) = faceAmbient hdim x o z.val from
    ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x _
      (ForestRadialFaceLocalization.faceAmbient_nonneg hdim x o z.val z.property.1)] at h
  exact (CompactDRCoordinates.realCoordinates (n + 1) m).injective h

theorem inverse_forward (z : Source hdim x o) : inverse hdim x o (forward hdim x o z.val) = z.val := by
  rw [forward_data]
  unfold inverse
  rw [inverseAmbient_data]
  change faceProjection (axis hdim x o)
    ((ForestGlobalGraphStokes.sourceCoordinates hdim x)
      ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm
        (faceEmbedding (axis hdim x o) 0 z.val))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext j
  simp [faceProjection, faceEmbedding]

theorem contDiff_faceAmbient : ContDiff ℝ ⊤ (faceAmbient hdim x o) :=
  (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff.comp
    (faceTangent (axis hdim x o)).contDiff

theorem contDiffAt_forward (z : Source hdim x o) : ContDiffAt ℝ ⊤ (forward hdim x o) z.val := by
  have hp : ForestDirectionRatioCoordinates.Admissible (tree 0 x) (canonicalLeaf 0 x)
      (realization 0 x (faceAmbient hdim x o z.val)) := by
    rw [← parameter_eq_realization]
    exact ⟨(parameter hdim x o z).val.property.1.2.2.2, (parameter hdim x o z).property.1⟩
  exact (CompactDRCoordinates.contDiffAt_forestAmbient _ _ _ hp).comp z.val
    ((contDiff_realization 0 x).comp (contDiff_faceAmbient hdim x o)).contDiffAt

theorem contDiffAt_inverse (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (inverse hdim x o) (forward hdim x o z.val) := by
  rw [forward_data]
  exact (faceProjection (axis hdim x o)).contDiff.contDiffAt.comp _
    ((ForestGlobalGraphStokes.sourceCoordinates hdim x).contDiff.contDiffAt.comp _
      (contDiffAt_inverseAmbient hdim x o z))

/-- The derivative of the genuine explicit native inverse is a left inverse,
so no rank or nonsingular-chart premise is supplied. -/
theorem differential_leftInverse (z : Source hdim x o) :
    (fderiv ℝ (inverse hdim x o) (forward hdim x o z.val)).comp
      (fderiv ℝ (forward hdim x o) z.val) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hd := ((contDiffAt_inverse hdim x o z).differentiableAt (by simp)).hasFDerivAt.comp z.val
    ((contDiffAt_forward hdim x o z).differentiableAt (by simp)).hasFDerivAt
  have he : (inverse hdim x o ∘ forward hdim x o) =ᶠ[𝓝 z.val] id :=
    Filter.eventuallyEq_of_mem ((isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ inverse_forward hdim x o ⟨w, hw⟩)
  have h := hd.fderiv
  rw [he.fderiv_eq, fderiv_id] at h
  exact h.symm

theorem differential_injective (z : Source hdim x o) :
    Function.Injective (fderiv ℝ (forward hdim x o) z.val) := by
  intro u v huv
  have h := congrArg (fderiv ℝ (inverse hdim x o) (forward hdim x o z.val)) huv
  have hd := differential_leftInverse hdim x o z
  have hu := congrArg (fun A : Coord r →L[ℝ] Coord r ↦ A u) hd
  have hv := congrArg (fun A : Coord r →L[ℝ] Coord r ↦ A v) hd
  exact hu.symm.trans (h.trans hv)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion
