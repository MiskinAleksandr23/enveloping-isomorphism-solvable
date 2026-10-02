import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRFaceSmoothDecoder
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

/-! An actual smooth left inverse of the native strict-face full-DR embedding.
The zero orbit is fixed in the explicit scalar decoder before differentiating. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceDRInverse
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestPositiveChartSmooth
open ForestOrthantCharts BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)

abbrev Source := ForestRadialFaceLocalization.source hdim x o

def model (z : Source hdim x o) : ForestOrthantCharts.Model 0 x :=
  ofAmbient 0 x (faceAmbient hdim x o z.val)

def parameter (z : Source hdim x o) : ForestChartOpenImage.Source 0 x :=
  sourcePoint 0 x (model hdim x o z) z.property.2

def point (z : Source hdim x o) : Compactification (0 : Fin (n + 1)) m :=
  ForestOrthantCharts.chart 0 x (model hdim x o z)

def data (z : Source hdim x o) : DRData (n + 1) m := projectDR (point hdim x o z).val

theorem parameter_eq_realization (z : Source hdim x o) :
    (parameter hdim x o z).val.val = realization 0 x (faceAmbient hdim x o z.val) := by
  have h := realization_eq_model 0 x (model hdim x o z)
  rw [show includeOrthant 0 x (model hdim x o z) = faceAmbient hdim x o z.val from
    includeOrthant_ofAmbient 0 x _ (ForestRadialFaceLocalization.faceAmbient_nonneg hdim x o z.val z.property.1)] at h
  exact h.symm

theorem point_eq_forward (z : Source hdim x o) :
    point hdim x o z = ForestChartOpenImage.forward 0 x (parameter hdim x o z) :=
  chart_eq_forward 0 x (model hdim x o z) z.property.2

theorem point_mem_referenceRegion (z : Source hdim x o) :
    point hdim x o z ∈ ForestChartOpenImage.referenceRegion 0 x := by
  have h := (ForestOrthantCharts.chart 0 x).map_source z.property.2
  have h' := h.1.1.1
  rw [ForestChartOpenImage.parameterChart_target] at h'
  exact h'.1

theorem data_mem_region (z : Source hdim x o) :
    data hdim x o z ∈ ForestDRInverse.Region (tree 0 x) (ExtractedForestDRReferences.lab 0 x)
      (frames 0 x) (ExtractedForestDRReferences.reference 0 x) :=
  point_mem_referenceRegion hdim x o z

theorem decoder_data (z : Source hdim x o) :
    ForestDRInverse.decode (tree 0 x) (ExtractedForestDRReferences.lab 0 x)
      (frames 0 x) (ExtractedForestDRReferences.reference 0 x) (data hdim x o z) =
    realization 0 x (faceAmbient hdim x o z.val) := by
  change ForestChartOpenImage.decoder 0 x (point hdim x o z) = _
  have h := point_mem_referenceRegion hdim x o z
  rw [point_eq_forward] at h ⊢
  rw [ForestChartOpenImage.decoder_forward 0 x _ h]
  exact parameter_eq_realization hdim x o z

def zeroNodes : Set (tree 0 x) := {v | ∃ hv : ReflectedRadiusCoordinates.Active (tree 0 x) v,
  ReflectedRadiusCoordinates.orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) ⟨v, hv⟩ = o}

def decoder : CompactDRCoordinates.Ambient (n + 1) m → ForestParameterSpace.Ambient (tree 0 x) :=
  ForestDRFaceSmoothDecoder.decode (tree 0 x) (ExtractedForestDRReferences.lab 0 x)
    (frames 0 x) (ExtractedForestDRReferences.reference 0 x) (zeroNodes x o)

theorem decoder_embed_data (z : Source hdim x o) :
    decoder x o (CompactDRCoordinates.dataEmbedding (data hdim x o z)) =
      realization 0 x (faceAmbient hdim x o z.val) := by
  change ForestDRFaceSmoothDecoder.decode _ _ _ _ _ (ForestDRFaceSmoothDecoder.embed (data hdim x o z)) = _
  rw [ForestDRFaceSmoothDecoder.decode_embed]
  · exact decoder_data hdim x o z
  · intro v hv
    rw [decoder_data]
    exact (radiusArray_face_zero_iff hdim x o z.val z.property.1 v).mpr hv

theorem contDiffAt_decoder (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (decoder x o) (CompactDRCoordinates.dataEmbedding (data hdim x o z)) := by
  apply ForestDRFaceSmoothDecoder.contDiffAt_decode _ _ _ _ _ _ (data_mem_region hdim x o z)
  intro B hmax hroot hB
  rw [decoder_data]
  have hn := (radiusArray_face_zero_iff hdim x o z.val z.property.1 B).not.mpr hB
  have hnon : 0 ≤ radiusArray 0 x (faceAmbient hdim x o z.val) B := by
    have h := (parameter hdim x o z).val.property.1.2.2.2 B
    change 0 ≤ (parameter hdim x o z).val.val.1 B at h
    rwa [parameter_eq_realization] at h
  exact lt_of_le_of_ne hnon (Ne.symm hn)

theorem angleBranch (z : Source hdim x o) :
    AngleBranch 0 x (realization 0 x (faceAmbient hdim x o z.val)) := by
  rw [← parameter_eq_realization]
  apply angleBranch_of_angles_target
  change ExtractedForestShapeCoordinates.coordinatesHomeomorph 0 x
    ((ExtractedForestShapeCoordinates.coordinatesHomeomorph 0 x).symm
      (angles 0 x (splitHomeomorph 0 x (model hdim x o z)))) ∈ _
  rw [Homeomorph.apply_symm_apply]
  exact (angles 0 x).map_source z.property.2.2.1

/-- Explicit smooth identification of every native orthant/angle/free coordinate. -/
def inverseAmbient (d : CompactDRCoordinates.Ambient (n + 1) m) : Ambient 0 x :=
  freeInverse 0 x (decoder x o d)

theorem contDiffAt_inverseAmbient (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (inverseAmbient x o) (CompactDRCoordinates.dataEmbedding (data hdim x o z)) := by
  have ha := angleBranch hdim x o z
  rw [← decoder_embed_data] at ha
  exact (contDiffAt_freeInverse 0 x _ ha).comp _ (contDiffAt_decoder hdim x o z)

theorem inverseAmbient_data (z : Source hdim x o) :
    inverseAmbient x o (CompactDRCoordinates.dataEmbedding (data hdim x o z)) =
      faceAmbient hdim x o z.val := by
  rw [inverseAmbient, decoder_embed_data, ← parameter_eq_realization,
    freeInverse_eq]
  change includeOrthant 0 x ((splitHomeomorph 0 x).symm ((angles 0 x).symm
    ((ExtractedForestShapeCoordinates.coordinatesHomeomorph 0 x)
      ((ExtractedForestShapeCoordinates.coordinatesHomeomorph 0 x).symm
        (angles 0 x (splitHomeomorph 0 x (model hdim x o z))))))) = _
  have hsource : splitHomeomorph 0 x (model hdim x o z) ∈ (angles 0 x).source := z.property.2.2.1
  rw [Homeomorph.apply_symm_apply, (angles 0 x).left_inv hsource,
    Homeomorph.symm_apply_apply]
  exact includeOrthant_ofAmbient 0 x _
    (ForestRadialFaceLocalization.faceAmbient_nonneg hdim x o z.val z.property.1)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceDRInverse
