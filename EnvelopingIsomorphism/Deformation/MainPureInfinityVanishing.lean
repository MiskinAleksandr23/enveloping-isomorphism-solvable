import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestDimensionVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestDimensionVanishing
import EnvelopingIsomorphism.Deformation.MainClassifiedFaceAssembly
import EnvelopingIsomorphism.Deformation.MixedPairedCoreData

/-! Original-partition vanishing of unsupported pure and nonempty infinity
blocks, specialized to both main binary and one-vector mixed graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPureInfinityVanishing
open Kontsevich Configuration ForestRadialFaceClassification RealForestSimpleCluster
open MainScalarBoundaryAssembly MainClassifiedFaceAssembly
open scoped Classical

theorem main_pure_orbitValue_eq_zero {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .pureBoundary)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 2) :
    orbitValue P j o = 0 := by
  have hz := PureForestDimensionVanishing.contribution_eq_zero (main_dimension n) j.val o ho hblock
    (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold orbitValue
  rw [hz,mul_zero]

theorem mixed_pure_orbitValue_eq_zero {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .pureBoundary)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 2) :
    MixedPairedCoreData.PairedData.orbitValue (MixedPairedCoreData.ofMixed P) j o = 0 := by
  have hz := PureForestDimensionVanishing.contribution_eq_zero
    (MixedScalarBoundaryAssembly.mixed_dimension N) j.val o ho hblock
    (P.partition j) (MixedScalarBoundaryAssembly.mixedEdges H)
    (MixedScalarBoundaryAssembly.mixedEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold MixedPairedCoreData.PairedData.orbitValue
  dsimp only [MixedPairedCoreData.ofMixed]
  rw [hz,mul_zero]

theorem main_infinity_nonempty_orbitValue_eq_zero {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .infinity)
    (hne : (boundaryClusterBlock (lower j.val o) (upper j.val o)).Nonempty)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 2) :
    orbitValue P j o = 0 := by
  have hz := InfinityForestDimensionVanishing.contribution_eq_zero (main_dimension n) j.val o ho hne hblock
    (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold orbitValue
  rw [hz,mul_zero]

theorem mixed_infinity_nonempty_orbitValue_eq_zero {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .infinity)
    (hne : (boundaryClusterBlock (lower j.val o) (upper j.val o)).Nonempty)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 1) :
    MixedPairedCoreData.PairedData.orbitValue (MixedPairedCoreData.ofMixed P) j o = 0 := by
  have hz := InfinityForestDimensionVanishing.contribution_eq_zero
    (MixedScalarBoundaryAssembly.mixed_dimension N) j.val o ho hne hblock
    (P.partition j) (MixedScalarBoundaryAssembly.mixedEdges H)
    (MixedScalarBoundaryAssembly.mixedEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold MixedPairedCoreData.PairedData.orbitValue
  dsimp only [MixedPairedCoreData.ofMixed]
  rw [hz,mul_zero]

end EnvelopingIsomorphism.Deformation.MainPureInfinityVanishing
