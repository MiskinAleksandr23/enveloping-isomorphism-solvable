import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantGraphForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveForwardCoordinates

/-! Literal equality with native original graph forms through the actual
parameter-dependent anchor normalization, including every derivative term. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveGraphForms

open Configuration ForestOrthantRealization ForestPositiveChartSmooth ForestOrthantGraphForms
open ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open scoped Classical Topology

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

def forestEdge (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source) : ForestGraphTopForms.Edge (n + 1) m where
  source := Equiv.swap 0 i e.source
  target := Sum.map (Equiv.swap 0 i) id e.target
  nonloop := by
    intro h
    apply he
    have hh : (Equiv.sumCongr (Equiv.swap 0 i) (Equiv.refl (Fin m))) e.target =
        (Equiv.sumCongr (Equiv.swap 0 i) (Equiv.refl (Fin m))) (Sum.inl e.source) := h
    exact (Equiv.sumCongr (Equiv.swap 0 i) (Equiv.refl (Fin m))).injective hh

theorem realizedEdge_eq (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source) :
    realizedEdge i x (forestEdge i e he) = leafEdgeMap i x e := by
  funext z
  change (ForestInsertionDifference.position (tree i x) (reflectedRealization i x z).val.1
      (reflectedRealization i x z).val.2 (canonicalLeaf i x (Sum.inl (Sum.inl (Equiv.swap 0 i e.source)))),
    ForestInsertionDifference.position (tree i x) (reflectedRealization i x z).val.1
      (reflectedRealization i x z).val.2 (canonicalLeaf i x (Sum.inl (Sum.map (Equiv.swap 0 i) id e.target)))) = _
  rw [reflectedRealization_val]
  rfl

theorem graphForm_eq_native {r : ℕ} (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (z : Ambient i x) (hz : ForestOrthantGraphForms.Regular i x z)
    (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x z).1)
    (hanchor : 0 < (anchorPoint i x z).im) :
    graphForm i x (fun j => forestEdge i (edges j) (hloop j)) z =
      (GraphForms.topForm edges (forwardCoordinates i x z)).compContinuousLinearMap
        (fderiv ℝ (forwardCoordinates i x) z) := by
  apply graphForm_eq_native_of_edgeMaps i x _ edges (forwardCoordinates i x)
    (normalizationScale i x) (normalizationShift i x) z
  · exact (contDiffAt_forwardCoordinates (ν := 1) i x z hanchor.ne').differentiableAt (by simp)
  · exact (contDiffAt_normalizationScale (ν := 1) i x z hanchor.ne').differentiableAt (by simp)
  · exact (contDiffAt_normalizationShift (ν := 1) i x z hanchor.ne').differentiableAt (by simp)
  · exact inv_pos.mpr hanchor
  · exact hz
  · exact hpos
  · intro j
    rw [realizedEdge_eq]
    exact edgeMap_forwardCoordinates_eventuallyEq i x (edges j) z hanchor.ne'

theorem anchor_pos_source (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source)
    (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x (includeOrthant i x z)).1) :
    0 < (anchorPoint i x (includeOrthant i x z)).im := by
  have hs : ForestChartConfigurations.OpenConditions (shapeData i x) (realization i x (includeOrthant i x z)) := by
    rw [realization_eq_model]
    exact parameterPoint_signs i x z hz
  exact ForestChartConfigurations.interior_pos (shapeData i x) _ hs hpos
    (radiusArray_reflection i x _) (shapeArray_constraints i x _).2.1 i

/-- Actual positive-chart equality, with positivity of the varying anchor
derived from the geometric chart source conditions. -/
theorem graphForm_eq_native_source {r : ℕ} (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (z : ForestOrthantCharts.Model i x) (hz : z ∈ (ForestOrthantCharts.chart i x).source)
    (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x (includeOrthant i x z)).1) :
    graphForm i x (fun j => forestEdge i (edges j) (hloop j)) (includeOrthant i x z) =
      (GraphForms.topForm edges (forwardCoordinates i x (includeOrthant i x z))).compContinuousLinearMap
        (fderiv ℝ (forwardCoordinates i x) (includeOrthant i x z)) :=
  graphForm_eq_native i x edges hloop _ (regular_source i x z hz) hpos (anchor_pos_source i x z hz hpos)

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveGraphForms
