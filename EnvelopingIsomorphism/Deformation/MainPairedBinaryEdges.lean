import EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCommonRealDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceWeight

/-! The original main Stokes edge array is the source-major edge array
used in the genuine two-point curvature integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedBinaryEdges
open Kontsevich UniformBinaryGraphs UniformBinaryContraction MainScalarBoundaryAssembly
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
variable {n : ℕ} (v : Fin (n + 1)) (H : BinaryGraph (n + 2) 3)
    {a b : Fin (n + 2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v)
    (hba : b ≠ a) (hanchor : (0 : Fin (n + 2)) ∈ cluster v → a = 0)

theorem commonEdges_eq_sourceMajor :
    PairedForestCommonRealDensity.edges (main_dimension n) ha hb hba hanchor (mainEdges H) =
      TwoPointBinaryFaceAdmissibility.orderedEdges H
        (TwoPointBinaryFaceWeight.sourceMajorOrder v ha hb hba hanchor) := by
  funext j
  unfold PairedForestCommonRealDensity.edges mainEdges
    TwoPointBinaryFaceAdmissibility.orderedEdges TwoPointBinaryFaceWeight.sourceMajorOrder
    GeometricWeights.canonicalOrder UniformBinaryQuotientOrderSign.binaryOrder
  congr 1

theorem normalized_common_integral_eq_sourceMajor :
    GeometricWeights.outgoingFactor (fun _ : Fin (n + 2) ↦ 2) *
      (((2 * Real.pi) ^ (shapeDegree a b (cluster v) +
          coarseDegree (0 : Fin (n + 2)) a (cluster v) 3))⁻¹ *
        ∫ y in InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
          GeometricWeights.realDomain (coarseN (0 : Fin (n + 2)) a (cluster v)) 3,
          realFaceDensity
            (PairedForestCommonRealDensity.edges (main_dimension n) ha hb hba hanchor
              (mainEdges H)) y) =
      TwoPointBinaryFaceWeight.normalizedIntegral v H
        (TwoPointBinaryFaceWeight.sourceMajorOrder v ha hb hba hanchor) := by
  rw [commonEdges_eq_sourceMajor v H ha hb hba hanchor]
  rfl

end EnvelopingIsomorphism.Deformation.MainPairedBinaryEdges
