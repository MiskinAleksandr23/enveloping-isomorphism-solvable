import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Explicit smooth ambient realization of the standard forest orthant chart.
Real radial coordinates may be negative in this extension. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantRealization

open Configuration ExtractedForestParameters ExtractedForestFrames ForestShapeCoordinates
open ExtractedForestShapeCoordinates ForestOrthantCharts
open scoped Classical NNReal ContDiff

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

abbrev Ambient := (Fin (R i x) → ℝ) × (Fin (C i x + Q i x) → ℝ)

def includeOrthant (z : ForestOrthantCharts.Model i x) : Ambient i x :=
  (fun j => (z.1 j : ℝ), z.2)

def radiusArray (z : Ambient i x) (v : tree i x) : ℝ :=
  if hv : ReflectedRadiusCoordinates.Active (tree i x) v then
    z.1 (Fintype.equivFin (ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x) (reflection_reflection i x))
      (ReflectedRadiusCoordinates.orbitClass (tree i x) (reflection i x) (reflection_reflection i x) ⟨v, hv⟩))
  else 1

def circleArray (z : Ambient i x) (v : PairParent (tree i x) (reflection i x)) : Circle :=
  angleChart ((centerModel i x).2.1 (Fintype.equivFin _ v))
    (((combineReal i x).symm z.2).1 (Fintype.equivFin _ v))

def realArray (z : Ambient i x) :
    RealIndex (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
      (pairedMarks i x) (fixedMarks i x) → ℝ :=
  fun v => ((combineReal i x).symm z.2).2 (Fintype.equivFin _ v)

/-- This is the actual free-shape inverse, whose explicit scalar reconstruction
was proved smooth in `ForestShapeSmooth`. -/
def shapeArray (z : Ambient i x) : tree i x → ℂ :=
  ((shapeRealHomeomorph (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
    (pairedMarks i x) (fixedMarks i x)).symm (circleArray i x z, realArray i x z)).val

def realization (z : Ambient i x) : ForestParameterSpace.Ambient (tree i x) :=
  (radiusArray i x z, shapeArray i x z)

theorem radiusArray_root (z : Ambient i x) : radiusArray i x z ⊥ = 1 := by
  simp [radiusArray, ReflectedRadiusCoordinates.Active]

theorem radiusArray_leaf (z : Ambient i x) (v : tree i x) (hv : IsMax v) : radiusArray i x z v = 1 := by
  simp [radiusArray, ReflectedRadiusCoordinates.Active, hv]

theorem radiusArray_reflection (z : Ambient i x) (v : tree i x) :
    radiusArray i x z (reflection i x v) = radiusArray i x z v := by
  by_cases hv : ReflectedRadiusCoordinates.Active (tree i x) v
  · have hrv := (ReflectedRadiusCoordinates.active_reflect_iff (tree i x) (reflection i x) v).mpr hv
    simp only [radiusArray, dif_pos hv, dif_pos hrv]
    apply congrArg z.1
    apply congrArg (Fintype.equivFin _)
    exact ReflectedRadiusCoordinates.orbitClass_reflect (tree i x) (reflection i x) (reflection_reflection i x) ⟨v, hv⟩
  · have hrv : ¬ ReflectedRadiusCoordinates.Active (tree i x) (reflection i x v) :=
      fun h => hv ((ReflectedRadiusCoordinates.active_reflect_iff (tree i x) (reflection i x) v).mp h)
    simp [radiusArray, hv, hrv]

theorem shapeArray_constraints (z : Ambient i x) :
    ForestParameterProduct.ShapeConstraints (tree i x) (reflection i x) (frames i x) (shapeArray i x z) :=
  ((shapeRealHomeomorph (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
    (pairedMarks i x) (fixedMarks i x)).symm (circleArray i x z, realArray i x z)).property

variable {ν : ℕ∞ω}

theorem contDiff_radiusArray : ContDiff ℝ ν (radiusArray i x) := by
  apply contDiff_pi.mpr
  intro v
  unfold radiusArray
  split_ifs <;> fun_prop

theorem contDiff_realArray : ContDiff ℝ ν (realArray i x) := by
  apply contDiff_pi.mpr
  intro v
  change ContDiff ℝ ν (fun z : Ambient i x => z.2 (finSumFinEquiv (Sum.inr (Fintype.equivFin _ v))))
  fun_prop

theorem contDiff_circleArray (v : PairParent (tree i x) (reflection i x)) :
    ContDiff ℝ ν (fun z : Ambient i x => (circleArray i x z v : ℂ)) := by
  change ContDiff ℝ ν (fun z : Ambient i x =>
    (angleChart ((centerModel i x).2.1 (Fintype.equivFin _ v))
      (z.2 (finSumFinEquiv (Sum.inl (Fintype.equivFin _ v)))) : ℂ))
  exact (contDiff_angleChart_coe _).comp (by fun_prop)

/-- No abstract smoothness of a homeomorphism is invoked: this theorem uses
the explicit component reconstruction, conjugation, re/im, and marked constants. -/
theorem contDiff_shapeArray : ContDiff ℝ ν (shapeArray i x) :=
  ForestShapeSmooth.contDiff_shape_inverse (tree i x) (reflection i x) (reflection_reflection i x)
    (frames i x) (pairedMarks i x) (fixedMarks i x) (circleArray i x) (realArray i x)
    (contDiff_circleArray i x) (contDiff_realArray i x)

/-- Global smooth extension on ALL real radial coordinates and all real
angles, hence in particular near every nonnegative-radius corner. -/
theorem contDiff_realization : ContDiff ℝ ν (realization i x) :=
  (contDiff_radiusArray i x).prodMk (contDiff_shapeArray i x)

theorem analyticAt_realization (z : Ambient i x) : AnalyticAt ℝ (realization i x) z :=
  (contDiff_realization (ν := ω) i x).contDiffAt.analyticAt

/-- Exact restriction identity: the explicit real ambient extension reconstructs
the very same radius/increment arrays as the actual standard orthant chart. -/
theorem realization_eq_model (z : ForestOrthantCharts.Model i x) :
    realization i x (includeOrthant i x z) =
      ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm
        (angles i x (splitHomeomorph i x z))).val := by
  apply Prod.ext
  · funext v
    rfl
  · rfl

def parameterPoint (z : ForestOrthantCharts.Model i x) : ForestChartOpenImage.ParameterSpace i x :=
  (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm (angles i x (splitHomeomorph i x z))

theorem realization_constraints (z : ForestOrthantCharts.Model i x) :
    ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x)
      (realization i x (includeOrthant i x z)) := by
  rw [realization_eq_model]
  exact (parameterPoint i x z).property

theorem parameterPoint_signs (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    parameterPoint i x z ∈ ForestChartOpenImage.signs i x := by
  have hsplit := hz.2
  have hfree := hsplit.2
  have hparameter := hfree.2
  simpa [parameterPoint] using hparameter.1

def sourcePoint (z : ForestOrthantCharts.Model i x) (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ForestChartOpenImage.Source i x := ⟨parameterPoint i x z, parameterPoint_signs i x z hz⟩

/-- On its source, the native angle chart is literally the original forest
insertion of the reconstructed parameter point. -/
theorem chart_eq_forward (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ForestOrthantCharts.chart i x z = ForestChartOpenImage.forward i x (sourcePoint i x z hz) := by
  let e := (⟨ForestChartOpenImage.signs i x, ForestChartOpenImage.isOpen_signs i x⟩ :
    TopologicalSpace.Opens (ForestChartOpenImage.ParameterSpace i x)).openPartialHomeomorphSubtypeCoe
      ⟨ForestChartOpenImage.sourcePoint i x⟩
  have hp : parameterPoint i x z ∈ e.target := by
    simpa [e] using
      parameterPoint_signs i x z hz
  change ForestChartOpenImage.forward i x (e.symm (parameterPoint i x z)) = _
  apply congrArg (ForestChartOpenImage.forward i x)
  apply Subtype.ext
  exact e.right_inv hp

theorem realization_admissible (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ForestDirectionRatioCoordinates.Admissible (tree i x) (ExtractedForestChildShapes.canonicalLeaf i x)
      (realization i x (includeOrthant i x z)) := by
  rw [realization_eq_model]
  exact ⟨(parameterPoint i x z).property.1.2.2.2, (parameterPoint_signs i x z hz).1⟩

def ambientDR (z : Ambient i x) : Fin (CompactDRCoordinates.dimension n m) → ℝ :=
  CompactDRCoordinates.forestReal (tree i x) (ExtractedForestChildShapes.canonicalLeaf i x) (realization i x z)

/-- The finite real full-DR realization is smooth at every point of the actual
orthant chart, including every zero-radius corner. -/
theorem contDiffAt_ambientDR (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ContDiffAt ℝ ⊤ (ambientDR i x) (includeOrthant i x z) :=
  (CompactDRCoordinates.contDiffAt_forestReal (tree i x) (ExtractedForestChildShapes.canonicalLeaf i x)
    _ (realization_admissible i x z hz)).comp _ (contDiff_realization i x).contDiffAt

/-- Exact chart realization in the actual finite real ambient full-DR space. -/
theorem ambientDR_eq_chart (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ambientDR i x (includeOrthant i x z) =
      CompactDRCoordinates.embedding i (ForestOrthantCharts.chart i x z) := by
  rw [chart_eq_forward i x z hz]
  unfold ambientDR CompactDRCoordinates.embedding
  rw [realization_eq_model]
  change CompactDRCoordinates.forestReal (tree i x) (ExtractedForestChildShapes.canonicalLeaf i x)
    (parameterPoint i x z).val =
      CompactDRCoordinates.realCoordinates n m (CompactDRCoordinates.dataEmbedding
        (projectDR (ForestChartConfigurations.compactificationInsertion (ExtractedForestChildShapes.shapeData i x)
          i (ForestChartOpenImage.toCorner i x (sourcePoint i x z hz))).val))
  rw [ForestChartConfigurations.compactificationInsertion_projectDR]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantRealization
