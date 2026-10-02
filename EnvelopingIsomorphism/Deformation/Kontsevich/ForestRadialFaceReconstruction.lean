import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

/-! The reverse geometric part of codimension-one coverage. An actual forest
chart parameter with one vanishing radial orbit has a unique native strict
face parameter. Identifying which orbit occurs for a simple collision is a
separate combinatorial assertion about its extracted tree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceReconstruction

open Configuration BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open ForestOrthantRealization ForestRadialFaceClassification
open ReflectedRadiusCoordinates ExtractedForestParameters ExtractedForestFrames
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)

/-- Delete the selected radial axis from the literal native source coordinates. -/
def faceCoordinates (w : Ambient 0 x) : Coord r :=
  fun j => ForestGlobalGraphStokes.sourceCoordinates hdim x w ((axis hdim x o).succAbove j)

theorem faceAmbient_faceCoordinates (w : Ambient 0 x)
    (hw : w.1 (orbitEquiv 0 x o) = 0) :
    faceAmbient hdim x o (faceCoordinates hdim x o w) = w := by
  apply (ForestGlobalGraphStokes.sourceCoordinates hdim x).injective
  rw [faceAmbient, ContinuousLinearEquiv.apply_symm_apply]
  funext j
  induction j using (axis hdim x o).succAboveCases with
  | x =>
    simp only [faceEmbedding, Fin.insertNth_apply_same]
    exact (ForestGlobalGraphStokes.sourceCoordinates_radial hdim x w (orbitEquiv 0 x o)).trans hw |>.symm
  | p j => simp only [faceEmbedding, Fin.insertNth_apply_succAbove, faceCoordinates]

@[simp] theorem faceCoordinates_faceAmbient (z : Coord r) :
    faceCoordinates hdim x o (faceAmbient hdim x o z) = z := by
  funext j
  simp only [faceCoordinates, faceAmbient, ContinuousLinearEquiv.apply_symm_apply,
    faceEmbedding, Fin.insertNth_apply_succAbove]

theorem faceAmbient_injective : Function.Injective (faceAmbient hdim x o) := by
  intro z z' h
  have := congrArg (faceCoordinates hdim x o) h
  simpa only [faceCoordinates_faceAmbient] using this

/-- Every other radial coordinate is strictly positive exactly when deleting
this zero coordinate lands in the strict native face. -/
theorem faceCoordinates_strict_iff (w : Ambient 0 x)
    (hw : w.1 (orbitEquiv 0 x o) = 0) :
    faceCoordinates hdim x o w ∈ strictOrthant
      (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)) ↔
      ∀ o' : ForestRadialFaceClassification.Orbit 0 x,
        o' ≠ o → 0 < w.1 (orbitEquiv 0 x o') := by
  constructor
  · intro hz o' hne
    have h := faceAmbient_other_positive hdim x o o' _ hz hne
    rwa [faceAmbient_faceCoordinates hdim x o w hw] at h
  · intro h
    apply (strict_face_iff _ _ _).mpr
    intro b hb hba
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨o', rfl⟩ := (orbitEquiv 0 x).surjective j
    have hne : o' ≠ o := fun he => hba (congrArg (axis hdim x) he)
    have hp := h o' hne
    rw [← faceAmbient_faceCoordinates hdim x o w hw, faceAmbient_radial] at hp
    exact hp

/-- The constructed face parameter belongs to the actual localized chart
source, so it can be passed directly to the simple-overlap theorems. -/
theorem faceCoordinates_mem_source (w : Ambient 0 x)
    (hw : w.1 (orbitEquiv 0 x o) = 0)
    (hpos : ∀ o' : ForestRadialFaceClassification.Orbit 0 x,
      o' ≠ o → 0 < w.1 (orbitEquiv 0 x o'))
    (hchart : ForestPositiveChartSmooth.ofAmbient 0 x w ∈ (ForestOrthantCharts.chart 0 x).source) :
    faceCoordinates hdim x o w ∈ ForestRadialFaceLocalization.source hdim x o := by
  refine ⟨(faceCoordinates_strict_iff hdim x o w hw).mpr hpos, ?_⟩
  change ForestPositiveChartSmooth.ofAmbient 0 x
    (faceAmbient hdim x o (faceCoordinates hdim x o w)) ∈ (ForestOrthantCharts.chart 0 x).source
  rwa [faceAmbient_faceCoordinates hdim x o w hw]

/-- Exact reverse coverage of the one-zero-orbit locus in a forest chart. -/
theorem existsUnique_source_parameter (w : Ambient 0 x)
    (hw : w.1 (orbitEquiv 0 x o) = 0)
    (hpos : ∀ o' : ForestRadialFaceClassification.Orbit 0 x,
      o' ≠ o → 0 < w.1 (orbitEquiv 0 x o'))
    (hchart : ForestPositiveChartSmooth.ofAmbient 0 x w ∈ (ForestOrthantCharts.chart 0 x).source) :
    ∃! z : ForestRadialFaceLocalization.source hdim x o, faceAmbient hdim x o z.val = w := by
  refine ⟨⟨faceCoordinates hdim x o w,
    faceCoordinates_mem_source hdim x o w hw hpos hchart⟩,
    faceAmbient_faceCoordinates hdim x o w hw, ?_⟩
  intro z hz
  apply Subtype.ext
  exact faceAmbient_injective hdim x o (hz.trans (faceAmbient_faceCoordinates hdim x o w hw).symm)

/-- Orbit coordinates can be read off any representative's native radius. -/
theorem radiusArray_representative (w : Ambient 0 x)
    (o' : ForestRadialFaceClassification.Orbit 0 x) :
    radiusArray 0 x w (representative 0 x o').val = w.1 (orbitEquiv 0 x o') := by
  rw [radiusArray, dif_pos (representative 0 x o').property]
  change w.1 (orbitEquiv 0 x (orbitClass _ _ _ (representative 0 x o'))) = _
  rw [representative_orbit]

/-- A native radius zero pattern suffices: nonnegativity upgrades every other
radius to strict positivity, and the native face parameter is unique. -/
theorem existsUnique_source_parameter_of_radiusArray (w : Ambient 0 x)
    (hnonneg : ∀ v : tree 0 x, 0 ≤ radiusArray 0 x w v)
    (hzero : ∀ v : tree 0 x, radiusArray 0 x w v = 0 ↔
      ∃ hv : Active (tree 0 x) v, orbitClass (tree 0 x) (reflection 0 x)
        (reflection_reflection 0 x) ⟨v, hv⟩ = o)
    (hchart : ForestPositiveChartSmooth.ofAmbient 0 x w ∈ (ForestOrthantCharts.chart 0 x).source) :
    ∃! z : ForestRadialFaceLocalization.source hdim x o, faceAmbient hdim x o z.val = w := by
  apply existsUnique_source_parameter hdim x o w
  · rw [← radiusArray_representative x w o]
    exact (hzero _).mpr ⟨(representative 0 x o).property, representative_orbit 0 x o⟩
  · intro o' hne
    rw [← radiusArray_representative x w o']
    apply lt_of_le_of_ne (hnonneg _)
    intro he
    obtain ⟨hv, heo⟩ := (hzero _).mp he.symm
    exact hne ((representative_orbit 0 x o').symm.trans heo)
  · exact hchart

/-- The reconstructed native face represents the identical compactification
point; this is literal equality through the original forest chart. -/
theorem exists_source_chart_eq (w : ForestOrthantCharts.Model 0 x)
    (hchart : w ∈ (ForestOrthantCharts.chart 0 x).source)
    (hw : (w.1 (orbitEquiv 0 x o) : ℝ) = 0)
    (hpos : ∀ o' : ForestRadialFaceClassification.Orbit 0 x,
      o' ≠ o → 0 < (w.1 (orbitEquiv 0 x o') : ℝ)) :
    ∃ z : ForestRadialFaceLocalization.source hdim x o,
      ForestOrthantCharts.chart 0 x
        (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val)) =
          ForestOrthantCharts.chart 0 x w := by
  obtain ⟨z, hz, _⟩ := existsUnique_source_parameter hdim x o (includeOrthant 0 x w) hw hpos
    (by simpa only [ForestPositiveChartSmooth.ofAmbient_includeOrthant] using hchart)
  exact ⟨z, by rw [hz, ForestPositiveChartSmooth.ofAmbient_includeOrthant]⟩

/-- Every free radial coordinate of the canonical extracted center vanishes.
Thus reverse simple-face coverage at this center is exactly a statement about
the number of reflection orbits in the extracted tree. -/
theorem center_radial_zero (o' : ForestRadialFaceClassification.Orbit 0 x) :
    (((ForestOrthantCharts.chart 0 x).symm x).1 (orbitEquiv 0 x o') : ℝ) = 0 := by
  change ((ExtractedForestShapeCoordinates.coordinatesHomeomorph 0 x
    ((ForestChartOpenImage.parameterChart 0 x).symm x)).1 (orbitEquiv 0 x o') : ℝ) = 0
  rw [← ForestPositiveChartSmooth.radialRaw_eq,
    ForestPositiveChartSmooth.parameterChart_inverse_val 0 x x (ForestChartOpenImage.self_mem_target 0 x)]
  unfold ForestPositiveChartSmooth.radialRaw ForestChartOpenImage.decoder
  rw [ExtractedForestDRRegion.decode_eq_limitingParameters]
  change limitingRadii 0 x (((orbitEquiv 0 x).symm (orbitEquiv 0 x o')).out).val = 0
  rw [Equiv.symm_apply_apply]
  have hv : Active (tree 0 x) o'.out.val := o'.out.property
  simp only [limitingRadii, if_neg hv.1,
    if_pos (ExtractedForestIdentification.nonleaf_large 0 x _ hv.2)]

/-- For an extracted tree with exactly one radial orbit, its actual center is
covered by the localized strict face, with no forward-image assumption. -/
theorem exists_source_center_of_unique_orbit
    (hunique : ∀ o' : ForestRadialFaceClassification.Orbit 0 x, o' = o) :
    ∃ z : ForestRadialFaceLocalization.source hdim x o,
      ForestOrthantCharts.chart 0 x
        (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val)) = x := by
  obtain ⟨z, hz⟩ := exists_source_chart_eq hdim x o ((ForestOrthantCharts.chart 0 x).symm x)
    ((ForestOrthantCharts.chart 0 x).map_target (ForestOrthantCharts.mem_chart_target 0 x))
    (center_radial_zero x o) (fun o' hne => (hne (hunique o')).elim)
  exact ⟨z, hz.trans ((ForestOrthantCharts.chart 0 x).right_inv (ForestOrthantCharts.mem_chart_target 0 x))⟩

/-- Conversely, a strict radial face representing the canonical center forces
all active nodes to lie in the selected orbit. This isolates the precise
remaining tree-identification obligation for reverse simple-face coverage. -/
theorem unique_orbit_of_source_center
    (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : ForestOrthantCharts.chart 0 x
      (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val)) = x) :
    ∀ o' : ForestRadialFaceClassification.Orbit 0 x, o' = o := by
  have he := congrArg (ForestOrthantCharts.chart 0 x).symm hz
  rw [(ForestOrthantCharts.chart 0 x).left_inv z.property.2] at he
  intro o'
  by_contra hne
  have hpos := faceAmbient_other_positive hdim x o o' z.val z.property.1 hne
  have hr := congrArg (fun w : ForestOrthantCharts.Model 0 x => (w.1 (orbitEquiv 0 x o') : ℝ)) he
  rw [center_radial_zero] at hr
  change ((faceAmbient hdim x o z.val).1 (orbitEquiv 0 x o')).toNNReal = (0 : ℝ) at hr
  rw [Real.coe_toNNReal _ hpos.le] at hr
  exact hpos.ne' hr

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceReconstruction
