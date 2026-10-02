import EnvelopingIsomorphism.Deformation.Kontsevich.ForestSingleZeroLinearDR
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestShapePositions
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceDRInverse

/-! Native strict fixed-orbit forest data is exactly the actual two-level
coarse/shape DR array. Pure, proper-real and infinity classes all use this. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSingleZeroDR
open Configuration ExtractedForestParameters ExtractedForestChildShapes
open ForestRadialFaceClassification RealForestCoarsePositions ForestSingleZeroLinearDR
open PairedForestCoarsePositions (parameters)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (z : ForestRadialFaceLocalization.source hdim x o)

def resolvedParameter : ForestDirectionRatioCoordinates.Domain (tree 0 x) (canonicalLeaf 0 x) :=
  ⟨parameters hdim x o z, PairedForestCoarsePositions.radius_nonneg hdim x o z,
    (PairedForestCoarsePositions.openConditions hdim x o z).1⟩

theorem data_eq_resolved :
    ForestRadialFaceDRInverse.data hdim x o z =
      ForestDirectionRatioCoordinates.resolvedCoordinates (tree 0 x) (canonicalLeaf 0 x)
        (resolvedParameter hdim x o z) := by
  unfold ForestRadialFaceDRInverse.data
  rw [ForestRadialFaceDRInverse.point_eq_forward]
  have h := ForestChartConfigurations.compactificationInsertion_projectDR (shapeData 0 x) 0
    (ForestChartOpenImage.toCorner 0 x (ForestRadialFaceDRInverse.parameter hdim x o z))
  change _ = ForestDirectionRatioCoordinates.resolvedCoordinates (tree 0 x) (canonicalLeaf 0 x)
    (ForestChartConfigurations.resolvedParameters (shapeData 0 x)
      (ForestChartOpenImage.toCorner 0 x (ForestRadialFaceDRInverse.parameter hdim x o z))) at h
  rw [ForestChartOpenImage.forward, h]
  congr 1
  apply Subtype.ext
  exact ForestRadialFaceDRInverse.parameter_eq_realization hdim x o z

include ho in
/-- Literal native full-DR correspondence, with no simple-chart assumption. -/
theorem data_eq_branchData :
    ForestRadialFaceDRInverse.data hdim x o z =
      linearData (PairedForestCoarsePositions.positions hdim x o z)
        (fun j ↦ if j ∈ (node x o).val then RealForestShapePositions.positions hdim x o z j else 0) := by
  rw [data_eq_resolved]
  have hc : (resolvedParameter hdim x o z).val.1 (node x o) = 0 :=
    (RealForestCoarsePositions.radius_zero_iff hdim x o ho z _).mpr rfl
  rw [resolvedCoordinates_eq_branchData (tree 0 x) (canonicalLeaf 0 x) (node x o)
    (resolvedParameter hdim x o z) hc (radius_pos_of_ne hdim x o ho z)]
  congr 1
  funext j
  simp only [branchVelocity, ExtractedForestChildShapes.le_canonicalLeaf_iff]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSingleZeroDR
