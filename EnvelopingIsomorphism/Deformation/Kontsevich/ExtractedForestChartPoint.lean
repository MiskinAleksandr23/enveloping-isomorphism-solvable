import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestNormalizedPoint
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartConfigurations

/-! Every actual extracted marked-limit point satisfies the open geometric
conditions and the closed normalized reflected equations of forest charts. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartPoint

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedForestNormalizedPoint ExtractedMarkedFrameReflection

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

theorem stableFixed : ReflectedRadiusOrthant.StableFixed (tree i x) (reflection i x) (frames i x) := by
  intro v hv
  have ht := frames_typeCorrect i x v hv
  cases hf : frames i x v hv with
  | complex a b ha hb hne => trivial
  | stableHeight a ha =>
    rw [hf] at ht
    exact ht.1
  | stableRealPair a b ha hb hne =>
    rw [hf] at ht
    exact ht.1

theorem openConditions : ForestChartConfigurations.OpenConditions (shapeData i x) (parameters i x) :=
  ⟨regularUnits i x, upper_unit_pos i x, boundary_unit_pos i x⟩

theorem cornerConditions : ForestChartConfigurations.CornerConditions (shapeData i x) (parameters i x) :=
  ⟨radii_admissible i x, limitingIncrements_reflection i x, openConditions i x⟩

/-- The actual point in the forward geometric forest corner domain. -/
def chartPoint : ForestChartConfigurations.CornerDomain (shapeData i x) :=
  ⟨parameters i x, cornerConditions i x⟩

theorem chartPoint_normalized : ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x)
    (chartPoint i x).val := constraints i x

theorem decoder_openConditions : ForestChartConfigurations.OpenConditions (shapeData i x)
    (ForestDRInverse.decode (tree i x) (ExtractedForestDRReferences.lab i x) (frames i x)
      (ExtractedForestDRReferences.reference i x) (projectDR x.val)) := by
  rw [ExtractedForestDRRegion.decode_eq_limitingParameters]
  exact openConditions i x

theorem decoder_cornerConditions : ForestChartConfigurations.CornerConditions (shapeData i x)
    (ForestDRInverse.decode (tree i x) (ExtractedForestDRReferences.lab i x) (frames i x)
      (ExtractedForestDRReferences.reference i x) (projectDR x.val)) := by
  rw [ExtractedForestDRRegion.decode_eq_limitingParameters]
  exact cornerConditions i x

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartPoint
