import EnvelopingIsomorphism.Deformation.MixedScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.MainPairedSupportOrbit

/-! Graph-independent certificates needed for original paired-face integration.
The mixed Stokes partition supplies them without an additional premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedCoreData
open Kontsevich ForestRadialFaceClassification ForestRadialFaceLocalization ForestGlobalGraphStokes
open scoped Classical

structure PairedData {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
    (es : Fin r → GraphForms.Edge n m) where
  noLoops : ∀ j, (es j).target ≠ Sum.inl (es j).source
  charts : Finset (Compactification (0 : Fin (n+1)) m)
  partition : OriginalPartitionCancellation.Partition charts n m
  localizer : ∀ j : charts, ForestOrthantRealization.Ambient 0 j.val → ℝ
  orientation : charts → ℝ
  support : ∀ j : charts, tsupport (CompactDRAmbientPartition.cutoff 0 (partition j)) ⊆
    (ForestChartOrientation.smallChart 0 j.val).target
  regular : ∀ j : charts,
    ContDiff ℝ 1 (localForm hdim j.val (partition j) es noLoops (localizer j)) ∧
      HasCompactSupport (localForm hdim j.val (partition j) es noLoops (localizer j))
  localization : ∀ j : charts, LocalizationAgreement j.val (partition j) es noLoops (localizer j)
  orientation_jacobian : ∀ j : charts, ∀ z ∈ positiveRegion hdim j.val,
    orientation j * OrientedFormChangeVariables.jacobian (chart hdim j.val) z =
      |OrientedFormChangeVariables.jacobian (chart hdim j.val) z|

variable {n m r : ℕ} {hdim : GraphForms.dimension n m = r+1}
  {es : Fin r → GraphForms.Edge n m} (P : PairedData hdim es)

def PairedData.orbitValue (j : P.charts) (o : Orbit 0 j.val) : ℝ :=
  P.orientation j * contribution hdim j.val
    (localForm hdim j.val (P.partition j) es P.noLoops (P.localizer j)) o

theorem mem_chart_of_cutoff_ne_zero (j : P.charts) (q : Compactification (0 : Fin (n+1)) m)
    (hq : CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0) :
    q ∈ (ForestOrthantCharts.chart 0 j.val).target := by
  have hs := P.support j (subset_tsupport _ hq)
  exact hs.1

def ofMixed {N : ℕ} {H : MixedGraphProfileCarrier.VectorGraph N 2}
    (P : MixedScalarBoundaryAssembly.MixedPartition H) :
    PairedData (MixedScalarBoundaryAssembly.mixed_dimension N)
      (MixedScalarBoundaryAssembly.mixedEdges H) where
  noLoops := MixedScalarBoundaryAssembly.mixedEdges_noLoops H
  charts := P.charts
  partition := P.partition
  localizer := P.localizer
  orientation := P.orientation
  support := P.support
  regular := P.regular
  localization := P.localization
  orientation_jacobian := P.orientation_jacobian

end EnvelopingIsomorphism.Deformation.MixedPairedCoreData
