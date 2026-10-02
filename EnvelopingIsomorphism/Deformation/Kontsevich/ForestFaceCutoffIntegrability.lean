import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

/-! Actual compact forest face densities, with the cutoff inherited from the
finite ambient partition. Integrability comes from compact orthant Stokes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestFaceCutoffIntegrability
open Set MeasureTheory BoxStokes CompactOrthantStokes
open ForestGlobalGraphStokes ForestRadialFaceClassification ForestRadialFaceLocalization
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : Orbit 0 x)

def cutoff (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (z : Coord r) : ℝ :=
  ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x)
    (CompactDRAmbientPartition.cutoff 0 ρ)
    (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z))

def graphDensity (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) (z : Coord r) : ℝ :=
  ((ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z)).compContinuousLinearMap
    (fderiv ℝ (faceAmbient hdim x o) z)) (standardBasis r)

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (edges : Fin r → GraphForms.Edge n m)
  (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
  (κ : ForestOrthantRealization.Ambient 0 x → ℝ)

theorem local_density_eq (hmatch : LocalizationAgreement x ρ edges hloop κ)
    (z : Coord r) (hz : z ∈ source hdim x o) :
    facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 z (standardBasis r) =
      cutoff hdim x o ρ z * graphDensity hdim x o
        (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) z := by
  have hincl := ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x
    (faceAmbient hdim x o z) (faceAmbient_nonneg hdim x o z hz.1)
  have hm := hmatch (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z))
  rw [hincl] at hm
  have hd : fderiv ℝ (faceAmbient hdim x o) z =
      (sourceCoordinates hdim x).symm.toContinuousLinearMap.comp
        (fderiv ℝ (faceEmbedding (axis hdim x o) 0) z) := by
    unfold faceAmbient
    rw [fderiv_faceEmbedding]
    exact ((sourceCoordinates hdim x).symm.hasFDerivAt.comp z
      (hasFDerivAt_faceEmbedding (axis hdim x o) 0 z)).fderiv
  simp only [facePullback, localForm, linearForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ForestOrthantLocalization.localized 0 x ρ _ κ (faceAmbient hdim x o z) _ = _
  rw [hm]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  unfold graphDensity cutoff
  rw [hd]
  rfl

theorem integrableOn_cutoff_graphDensity
    (hmatch : LocalizationAgreement x ρ edges hloop κ)
    (hcont : Continuous (localForm hdim x ρ edges hloop κ))
    (hcompact : HasCompactSupport (localForm hdim x ρ edges hloop κ)) :
    IntegrableOn (fun z ↦ cutoff hdim x o ρ z * graphDensity hdim x o
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) z)
      (source hdim x o) := by
  have hi := integrableOn_lower_face (localForm hdim x ρ edges hloop κ)
    (radialIndices hdim x) hcont hcompact (axis hdim x o)
  have hs : source hdim x o ⊆ orthant (faceIndices (radialIndices hdim x) (axis hdim x o)) :=
    fun z hz j hj ↦ (hz.1 j hj).le
  exact (hi.mono_set hs).congr_fun
    (fun z hz ↦ local_density_eq hdim x o ρ edges hloop κ hmatch z hz)
    (measurableSet_source hdim x o)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestFaceCutoffIntegrability
