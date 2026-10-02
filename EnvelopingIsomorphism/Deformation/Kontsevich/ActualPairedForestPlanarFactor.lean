import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFacePlanarCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialClusterLabels
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

/-! The planar factor of an actual paired radial orbit, with every descendant
label enumerated and all chart-domain and radius conditions derived natively. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ActualPairedForestPlanarFactor
open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestRadialFaceClassification ForestRadialClusterLabels
open ForestRadialFacePlanarCoordinates
open BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)

def labelsSet : Finset (Fin (n + 1)) := interiorLabels 0 x (upperNode 0 x o ho).val

def size : ℕ := (labelsSet x o ho).card - 2

theorem card_labelsSet : Fintype.card (labelsSet x o ho) = size x o ho + 2 := by
  rw [Fintype.card_coe]
  have h := upperNode_card 0 x o ho
  change 1 < (labelsSet x o ho).card at h
  dsimp [size]
  omega

def labelEquiv : labelsSet x o ho ≃ InteriorFiberAngleSplit.Point (size x o ho) :=
  Fintype.equivFinOfCardEq (card_labelsSet x o ho)

def labels (j : InteriorFiberAngleSplit.Point (size x o ho)) : Fin (n + 1) :=
  ((labelEquiv x o ho).symm j).val

theorem labels_injective : Function.Injective (labels x o ho) :=
  Subtype.val_injective.comp (labelEquiv x o ho).symm.injective

theorem labels_below (j : InteriorFiberAngleSplit.Point (size x o ho)) :
    (upperNode 0 x o ho).val ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl (labels x o ho j))) :=
  (le_canonicalLeaf_iff 0 x _ _).mpr
    ((mem_interiorLabels 0 x _ _).mp ((labelEquiv x o ho).symm j).property)

theorem labels_range : Set.range (labels x o ho) = (labelsSet x o ho : Set (Fin (n + 1))) := by
  ext j
  constructor
  · rintro ⟨k, rfl⟩
    exact ((labelEquiv x o ho).symm k).property
  · intro hj
    refine ⟨labelEquiv x o ho ⟨j, hj⟩, ?_⟩
    simp [labels]

variable (z : Coord r)
  (hz : z ∈ strictOrthant (faceIndices (ForestGlobalGraphStokes.radialIndices hdim x) (axis hdim x o)))
  (hchart : model hdim x o z hz ∈ (ForestOrthantCharts.chart 0 x).source)

/-- The circle and original Cartesian planar configuration extracted from this
actual face, with no assumed labeling, positivity, or shape configuration. -/
def coordinates : Circle × PlanarNormalizedCoordinates.Configuration (size x o ho) :=
  ForestRadialFacePlanarCoordinates.coordinates hdim x o z hz hchart (upperNode 0 x o ho)
    (upperNode_spec 0 x o ho).1 (labels x o ho) (labels_injective x o ho) (labels_below x o ho)

def normalized : PlanarNormalizedCoordinates.Normalized (size x o ho) :=
  ForestDescendantPlanarCoordinates.normalized 0 x (upperNode 0 x o ho).val
    (labels x o ho) (labels_injective x o ho) (labels_below x o ho)
    (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart (upperNode 0 x o ho) (upperNode_spec 0 x o ho).1)

/-- Equality with all retained directions and ratios in the actual forest face. -/
theorem retainedDR_eq_encode :
    ForestDescendantPlanarCoordinates.project (labels x o ho) (labels_injective x o ho)
      (projectDR (ForestOrthantCharts.chart 0 x (model hdim x o z hz)).val) =
    PlanarClusterCompactification.encode 0 1 (normalized hdim x o ho z hz hchart) := by
  rw [ForestOrthantRealization.chart_eq_forward 0 x (model hdim x o z hz) hchart]
  exact (ForestDescendantPlanarCoordinates.project_forward_eq_ofPositions
    0 x (upperNode 0 x o ho).val (labels x o ho) (labels_injective x o ho) (labels_below x o ho)
    (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart (upperNode 0 x o ho) (upperNode_spec 0 x o ho).1)).trans
    (ForestDescendantPlanarCoordinates.normalized_encode
    0 x (upperNode 0 x o ho).val (labels x o ho) (labels_injective x o ho) (labels_below x o ho)
    (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart (upperNode 0 x o ho) (upperNode_spec 0 x o ho).1)).symm


/-- A pointwise angular representative; no smoothness across its argument cut is claimed. -/
def rotatingParameters : InteriorFiberAngleSplit.Parameters (size x o ho) :=
  (Complex.arg ((coordinates hdim x o ho z hz hchart).1 : ℂ),
    (coordinates hdim x o ho z hz hchart).2.val)

theorem rotating_shape_configuration : (rotatingParameters hdim x o ho z hz hchart).2 ∈
    InteriorFiberAngleSplit.shapeConfiguration (size x o ho) :=
  (coordinates hdim x o ho z hz hchart).2.property

theorem positions_eq_rotated (j : InteriorFiberAngleSplit.Point (size x o ho)) :
    ForestDescendantPlanarCoordinates.positions 0 x (upperNode 0 x o ho).val (labels x o ho)
      (ForestOrthantRealization.realization 0 x (faceAmbient hdim x o z)) j =
    ForestDescendantPlanarCoordinates.positions 0 x (upperNode 0 x o ho).val (labels x o ho)
      (ForestOrthantRealization.realization 0 x (faceAmbient hdim x o z)) 0 +
    (ForestDescendantPlanarCoordinates.referenceRadius 0 x (upperNode 0 x o ho).val (labels x o ho)
      (ForestOrthantRealization.realization 0 x (faceAmbient hdim x o z)) : ℂ) *
    InteriorFiberAngleSplit.rotatedPoint (rotatingParameters hdim x o ho z hz hchart) j := by
  have h := ForestDescendantPlanarCoordinates.positions_reconstruct
    0 x (upperNode 0 x o ho).val (labels x o ho) (labels_injective x o ho) (labels_below x o ho)
    (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart (upperNode 0 x o ho) (upperNode_spec 0 x o ho).1) j
  change _ = _ + _ * ((coordinates hdim x o ho z hz hchart).1 : ℂ) *
    InteriorFiberAngleSplit.normalizedPoint (coordinates hdim x o ho z hz hchart).2.val j at h
  rw [source_parameters] at h
  simpa only [InteriorFiberAngleSplit.rotatedPoint, rotatingParameters,
    circleParameter_eq, Circle.exp_arg, mul_assoc] using h


/-- The actual phase-carrying planar extraction written directly in native
real Stokes face coordinates. -/
def nativeNormalized (w : Coord r) : InteriorFiberAngleSplit.Point (size x o ho) → ℂ :=
  ForestDescendantPlanarCoordinates.ambientNormalized 0 x (upperNode 0 x o ho).val
    (labels x o ho) (ForestOrthantRealization.realization 0 x (faceAmbient hdim x o w))

theorem normalized_eq_native : (normalized hdim x o ho z hz hchart).val =
    nativeNormalized hdim x o ho z := by
  change ForestDescendantPlanarCoordinates.ambientNormalized 0 x (upperNode 0 x o ho).val
    (labels x o ho) (source hdim x o z hz hchart).val.val = _
  rw [source_parameters]
  rfl

include hz hchart in
/-- Smoothness is of the genuine map from native face coordinates, including
its phase, without a global smooth argument choice. -/
theorem contDiffAt_nativeNormalized : ContDiffAt ℝ ⊤ (nativeNormalized hdim x o ho) z := by
  have hn := ForestDescendantPlanarCoordinates.contDiffAt_ambientNormalized
    0 x (upperNode 0 x o ho).val (labels x o ho) (labels_injective x o ho) (labels_below x o ho)
    (source hdim x o z hz hchart)
    (positiveBelow hdim x o z hz hchart (upperNode 0 x o ho) (upperNode_spec 0 x o ho).1)
  rw [source_parameters] at hn
  have hf : ContDiff ℝ ⊤ (faceAmbient hdim x o) :=
    (ForestGlobalGraphStokes.sourceCoordinates hdim x).symm.contDiff.comp
      (faceTangent (axis hdim x o)).contDiff
  exact hn.comp z ((ForestOrthantRealization.contDiff_realization 0 x).comp hf).contDiffAt

theorem model_eq_ofAmbient : model hdim x o z hz =
    ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z) := by
  apply Prod.ext
  · funext j
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (ForestRadialFacePlanarCoordinates.faceAmbient_nonneg hdim x o z hz j)).symm
  · rfl

omit z hz hchart in
/-- Actual planar factor on precisely the native domain of the localized Stokes
face integral; chart membership is supplied by that domain itself. -/
def onSource (z : ForestRadialFaceLocalization.source hdim x o) :
    Circle × PlanarNormalizedCoordinates.Configuration (size x o ho) :=
  coordinates hdim x o ho z.val z.property.1
    ((model_eq_ofAmbient hdim x o z.val z.property.1).symm ▸ z.property.2)

end EnvelopingIsomorphism.Deformation.Kontsevich.ActualPairedForestPlanarFactor
