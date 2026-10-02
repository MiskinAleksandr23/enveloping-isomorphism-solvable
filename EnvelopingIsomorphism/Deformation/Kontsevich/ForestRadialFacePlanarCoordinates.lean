import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDescendantPlanarCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceClassification

/-! Actual original planar cluster coordinates on strict native radial faces.
The positivity required by subtree extraction is derived from the literal
one-zero-orbit face; it is not an overlap or regularity premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFacePlanarCoordinates
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestDescendantPlanarCoordinates
open BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open scoped Classical NNReal
variable {n m r N : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (z : Coord r)
  (hz : z ∈ strictOrthant (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)))

include hz in
theorem faceAmbient_nonneg (j : Fin (ForestOrthantCharts.R 0 x)) :
    0 ≤ (faceAmbient hdim x o z).1 j := by
  obtain ⟨o', rfl⟩ := (orbitEquiv 0 x).surjective j
  by_cases h : o' = o
  · subst o'; rw [faceAmbient_selected_zero]
  · exact (faceAmbient_other_positive hdim x o o' z hz h).le

def model : ForestOrthantCharts.Model 0 x :=
  (fun j ↦ ⟨(faceAmbient hdim x o z).1 j, faceAmbient_nonneg hdim x o z hz j⟩,
    (faceAmbient hdim x o z).2)

@[simp] theorem include_model : includeOrthant 0 x (model hdim x o z hz) = faceAmbient hdim x o z := rfl

variable (hchart : model hdim x o z hz ∈ (ForestOrthantCharts.chart 0 x).source)

def source : ForestChartOpenImage.Source 0 x := sourcePoint 0 x (model hdim x o z hz) hchart

theorem source_parameters : (source hdim x o z hz hchart).val.val =
    realization 0 x (faceAmbient hdim x o z) :=
  (realization_eq_model 0 x (model hdim x o z hz)).symm

variable (c : ReflectedRadiusCoordinates.ActiveNode (tree 0 x))
  (hc : ReflectedRadiusCoordinates.orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) c = o)

include hc in
theorem positiveBelow : ForestDescendantPlanarCoordinates.PositiveBelow 0 x c.val
    (source hdim x o z hz hchart).val := by
  intro v hv hn
  rw [source_parameters]
  apply radiusArray_face_descendant_pos hdim x o z hz c hc
  exact lt_of_le_of_ne v.property (fun h ↦ hv (Subtype.ext h.symm))

variable (labels : InteriorFiberAngleSplit.Point N → Fin (n + 1))
  (hinj : Function.Injective labels)
  (hbelow : ∀ j, c.val ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl (labels j))))

/-- A fully constructed original planar factor of the actual forest face. -/
def coordinates : Circle × PlanarNormalizedCoordinates.Configuration N :=
  ForestDescendantPlanarCoordinates.coordinates 0 x c.val labels hinj hbelow
    (source hdim x o z hz hchart) (positiveBelow hdim x o z hz hchart c hc)

include hchart hc hbelow in
/-- Every original cluster direction and ratio is retained, for the actual
forest chart point on this strict radial face. -/
theorem chart_retainedDR :
    ForestDescendantPlanarCoordinates.project labels hinj
      (projectDR (ForestOrthantCharts.chart 0 x (model hdim x o z hz)).val) =
    MarkedDRIdentification.ofPositions (ForestDescendantPlanarCoordinates.positions 0 x c.val labels
      (realization 0 x (faceAmbient hdim x o z))) := by
  rw [chart_eq_forward 0 x (model hdim x o z hz) hchart]
  have h := ForestDescendantPlanarCoordinates.project_forward_eq_ofPositions
    0 x c.val labels hinj hbelow (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart c hc)
  rw [source_parameters] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFacePlanarCoordinates
