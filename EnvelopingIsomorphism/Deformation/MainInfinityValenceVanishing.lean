import EnvelopingIsomorphism.Deformation.MainPureInfinityVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceVanishing

/-! All unsupported infinity blocks vanish in the original graph integral,
including empty blocks at their actual recovered physical slot. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainInfinityValenceVanishing
open Kontsevich Configuration ForestRadialFaceClassification
open InfinityForestSimpleCluster (lower upper)
open MainScalarBoundaryAssembly MainClassifiedFaceAssembly
open scoped Classical

theorem contribution_eq_zero_of_block_card_ne {n m r : ℕ}
    (hdim : GraphForms.dimension n m = r+1)
    (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
    (ho : kind 0 x o = .infinity) (hm : 2 ≤ m)
    (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ m-1)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ) :
    contribution hdim x (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ) o = 0 := by
  by_cases hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty
  · exact InfinityForestDimensionVanishing.contribution_eq_zero hdim x o ho hne hblock
      ρ edges hloop κ hmatch
  · exact EmptyInfinityForestFaceVanishing.contribution_eq_zero_of_block_empty hdim x o ho hm
      (Finset.not_nonempty_iff_eq_empty.mp hne) ρ edges hloop κ hmatch

theorem main_orbitValue_eq_zero {n : ℕ} {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .infinity)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 2) :
    orbitValue P j o = 0 := by
  have hz := contribution_eq_zero_of_block_card_ne (main_dimension n) j.val o ho (by omega) hblock
    (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold orbitValue
  rw [hz,mul_zero]

theorem mixed_orbitValue_eq_zero {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .infinity)
    (hblock : (boundaryClusterBlock (lower j.val o) (upper j.val o)).card ≠ 1) :
    MixedPairedCoreData.PairedData.orbitValue (MixedPairedCoreData.ofMixed P) j o = 0 := by
  have hz := contribution_eq_zero_of_block_card_ne
    (MixedScalarBoundaryAssembly.mixed_dimension N) j.val o ho (by omega) hblock
    (P.partition j) (MixedScalarBoundaryAssembly.mixedEdges H)
    (MixedScalarBoundaryAssembly.mixedEdges_noLoops H) (P.localizer j) (P.localization j)
  unfold MixedPairedCoreData.PairedData.orbitValue
  dsimp only [MixedPairedCoreData.ofMixed]
  rw [hz,mul_zero]

end EnvelopingIsomorphism.Deformation.MainInfinityValenceVanishing
