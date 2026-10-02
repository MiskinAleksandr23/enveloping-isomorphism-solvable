import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceWeight

/-! Native two-point face integrals vanish outside actual contraction support. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceZeroIntegral
open KontsevichGraph.General KontsevichGraph.General.Graph
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open MeasureTheory
variable {n m : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
    (v : Fin (n + 1)) (H : Graph (vertexSplitArity q qLocal v) m)
    {i a b : Fin (n + 2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m) ≃
      KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))

include ha hb hba

theorem density_eq_zero_of_not_data (h : ¬ Data v H)
    (y : RealProductCoordinates i a b (cluster v) m)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) m) :
    realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y = 0 := by
  by_contra hn
  exact h (ofNonzero v H order ha hb hba y hy hn)

theorem normalizedIntegral_eq_zero_of_not_data (h : ¬ Data v H) :
    normalizedIntegral v H order = 0 := by
  unfold normalizedIntegral
  rw [setIntegral_eq_zero_of_forall_eq_zero
    (density_eq_zero_of_not_data v H ha hb hba order h), mul_zero, mul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceZeroIntegral
