import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestValenceVanishing
import EnvelopingIsomorphism.Deformation.MainClassifiedFaceAssembly
import EnvelopingIsomorphism.Deformation.MixedPairedCoreData

/-! Wrong-valence proper-real orbits vanish in the original main and mixed
finite Stokes partitions; no chosen anchors or block nonemptiness is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealValenceVanishing
open Kontsevich Configuration ForestRadialFaceClassification RealForestSimpleCluster
open RealForestCoarsePositions MainScalarBoundaryAssembly MainClassifiedFaceAssembly
open scoped Classical

theorem main_orbitValue_eq_zero {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .properReal)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 2) :
    orbitValue P j o = 0 := by
  have hz := RealForestValenceVanishing.binary_properReal_contribution_eq_zero
    (main_dimension n) j.val o ho H
    (GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)))
    hblock (P.partition j) (P.localizer j) (P.localization j)
  change ForestRadialFaceClassification.contribution (main_dimension n) j.val
    (ForestGlobalGraphStokes.localForm (main_dimension n) j.val (P.partition j)
      (mainEdges H) (mainEdges_noLoops H) (P.localizer j)) o = 0 at hz
  unfold orbitValue
  rw [hz, mul_zero]

theorem mixed_orbitValue_eq_zero {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .properReal)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠
      if H.vertex ∈ labelsSet j.val o then 1 else 2) :
    MixedPairedCoreData.PairedData.orbitValue (MixedPairedCoreData.ofMixed P) j o = 0 := by
  have hz := RealForestValenceVanishing.mixed_properReal_contribution_eq_zero
    (MixedScalarBoundaryAssembly.mixed_dimension N) j.val o ho H.vertex H.graph
    (GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex))
    hblock (P.partition j) (P.localizer j) (P.localization j)
  change ForestRadialFaceClassification.contribution (MixedScalarBoundaryAssembly.mixed_dimension N) j.val
    (ForestGlobalGraphStokes.localForm (MixedScalarBoundaryAssembly.mixed_dimension N) j.val (P.partition j)
      (MixedScalarBoundaryAssembly.mixedEdges H) (MixedScalarBoundaryAssembly.mixedEdges_noLoops H)
      (P.localizer j)) o = 0 at hz
  unfold MixedPairedCoreData.PairedData.orbitValue
  dsimp only [MixedPairedCoreData.ofMixed]
  rw [hz, mul_zero]

end EnvelopingIsomorphism.Deformation.MainRealValenceVanishing
