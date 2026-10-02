import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOpenImage

/-! Actual free orthant/circle/real-vector models and charts at every extracted
compactification point. All frame metadata are constructed, not assumed. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeCoordinates

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestShapeCoordinates
open scoped Classical NNReal

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def shapePoint : ForestParameterProduct.ShapeSpace (tree i x) (reflection i x) (frames i x) :=
  ((ForestParameterProduct.productHomeomorph (tree i x) (reflection i x) (frames i x)
    (ExtractedForestChartPoint.stableFixed i x)) (ExtractedForestNormalizedPoint.parameterPoint i x)).2

theorem realPairFixed : ForestShapeCoordinates.RealPairFixed (tree i x) (reflection i x) (frames i x) :=
  ExtractedForestOriginalDecode.realPairFixed i x

def pairedMarks (v : PairParent (tree i x) (reflection i x)) :=
  complexMarks (tree i x) (reflection i x) (frames i x) (ExtractedMarkedFrameReflection.compatible i x) v

def fixedMarks (v : FixedParent (tree i x) (reflection i x)) :=
  stableMarks (tree i x) (reflection i x) (frames i x) (ExtractedMarkedFrameReflection.compatible i x)
    (realPairFixed i x) (shapePoint i x) v

def radialCount : ℕ := ReflectedRadiusCoordinates.freeRadiusCount (tree i x) (reflection i x) (reflection_reflection i x)
def circleCount : ℕ := ForestShapeCoordinates.circleCount (tree i x) (reflection i x)
def realCount : ℕ := ForestShapeCoordinates.realCount (tree i x) (reflection i x) (reflection_reflection i x)
  (frames i x) (pairedMarks i x) (fixedMarks i x)

abbrev Model := (Fin (radialCount i x) → ℝ≥0) × ((Fin (circleCount i x) → Circle) × (Fin (realCount i x) → ℝ))

/-- The explicit actual free model, with all metadata discharged at the
original compactification point x. -/
def coordinatesHomeomorph : ForestChartOpenImage.ParameterSpace i x ≃ₜ Model i x :=
  finParameterHomeomorph (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
    (ExtractedForestChartPoint.stableFixed i x) (pairedMarks i x) (fixedMarks i x)

/-- Genuine local compactification chart with free radial, circle, and real
coordinates. Local circle-to-angle charts can be composed later. -/
def chart : OpenPartialHomeomorph (Model i x) (Compactification i m) :=
  (coordinatesHomeomorph i x).symm.toOpenPartialHomeomorph.trans (ForestChartOpenImage.parameterChart i x)

theorem chart_target : (chart i x).target = ForestChartOpenImage.target i x := by
  simp only [chart, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    Set.preimage_univ, Set.inter_univ, ForestChartOpenImage.parameterChart_target]

theorem mem_chart_target : x ∈ (chart i x).target := by
  rw [chart_target]
  exact ForestChartOpenImage.self_mem_target i x

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeCoordinates
