import EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairSums
import EnvelopingIsomorphism.Deformation.Kontsevich.NativePairedFaceIntegration

/-! Actual classified forest Stokes data for every one-vector graph. The
physical mixed boundary equality remains an explicit geometric obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedScalarBoundaryAssembly
open scoped Classical BigOperators
open MixedGraphProfileCarrier MixedGraphPhysicalPairSums Kontsevich
open ForestOrthantRealization ForestGlobalGraphStokes ForestRadialFaceClassification
open ForestRadialFaceLocalization MeasureTheory

theorem mixed_dimension (N : ℕ) :
    GraphForms.dimension N 2 = GraphForms.dimension N 1 + 1 := by
  simp [GraphForms.dimension]

def mixedEdges {N : ℕ} (H : VectorGraph N 2) :
    Fin (GraphForms.dimension N 1) → GraphForms.Edge N 2 := fun j ↦
  let e := GeometricWeights.canonicalOrder
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex) j
  ⟨e.1, H.graph.target e⟩

theorem mixedEdges_noLoops {N : ℕ} (H : VectorGraph N 2)
    (j : Fin (GraphForms.dimension N 1)) :
    (mixedEdges H j).target ≠ Sum.inl (mixedEdges H j).source :=
  H.graph.noLoops _ _

structure MixedPartition {N : ℕ} (H : VectorGraph N 2) where
  charts : Finset (Compactification (0 : Fin (N + 1)) 2)
  partition : OriginalPartitionCancellation.Partition charts N 2
  localizer : ∀ j : charts, Ambient 0 j.val → ℝ
  orientation : charts → ℝ
  cover : ∀ y : Compactification (0 : Fin (N + 1)) 2,
    ∃ j : charts, y ∈ (ForestChartOrientation.smallChart 0 j.val).target
  support : ∀ j : charts, tsupport (CompactDRAmbientPartition.cutoff 0 (partition j)) ⊆
    (ForestChartOrientation.smallChart 0 j.val).target
  regular : ∀ j : charts,
    ContDiff ℝ 1 (localForm (mixed_dimension N) j.val (partition j)
      (mixedEdges H) (mixedEdges_noLoops H) (localizer j)) ∧
    HasCompactSupport (localForm (mixed_dimension N) j.val (partition j)
      (mixedEdges H) (mixedEdges_noLoops H) (localizer j))
  localization : ∀ j : charts, LocalizationAgreement j.val (partition j)
    (mixedEdges H) (mixedEdges_noLoops H) (localizer j)
  orientation_sign : ∀ j : charts, orientation j = 1 ∨ orientation j = -1
  orientation_jacobian : ∀ j : charts, ∀ z ∈ positiveRegion (mixed_dimension N) j.val,
    orientation j * OrientedFormChangeVariables.jacobian (chart (mixed_dimension N) j.val) z =
      |OrientedFormChangeVariables.jacobian (chart (mixed_dimension N) j.val) z|
  cancellation : ∑ j : charts, orientation j * ∑ k : Kind,
    classifiedContribution (mixed_dimension N) j.val (partition j)
      (mixedEdges H) (mixedEdges_noLoops H) (localizer j) k = 0

theorem exists_mixedPartition {N : ℕ} (H : VectorGraph N 2) :
    Nonempty (MixedPartition H) := by
  obtain ⟨s, ρ, κ, ε, hc, hs, hr, hl, he, hj, hz⟩ :=
    exists_classified_boundary_cancellation (mixed_dimension N) (mixedEdges H) (mixedEdges_noLoops H)
  exact ⟨⟨s, ρ, κ, ε, hc, hs, hr, hl, he, hj, hz⟩⟩

def mixedPartition {N : ℕ} (H : VectorGraph N 2) : MixedPartition H :=
  Classical.choice (exists_mixedPartition H)

variable {N : ℕ} {H : VectorGraph N 2} (P : MixedPartition H)

def nativeKindBoundary (k : Kind) : ℝ :=
  ∑ j : P.charts, P.orientation j *
    classifiedContribution (mixed_dimension N) j.val (P.partition j)
      (mixedEdges H) (mixedEdges_noLoops H) (P.localizer j) k

def nativeBoundary : ℝ :=
  ∑ j : P.charts, P.orientation j * ∑ k : Kind,
    classifiedContribution (mixed_dimension N) j.val (P.partition j)
      (mixedEdges H) (mixedEdges_noLoops H) (P.localizer j) k

theorem nativeBoundary_eq_zero : nativeBoundary P = 0 := P.cancellation

theorem nativeBoundary_eq_sum_kind :
    nativeBoundary P = ∑ k : Kind, nativeKindBoundary P k := by
  simp only [nativeBoundary, nativeKindBoundary, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem integrableOn_nativeDensity (j : P.charts) (o : Orbit 0 j.val) :
    IntegrableOn (NativePairedFaceIntegration.nativeDensity (mixed_dimension N) j.val o
      (P.partition j) (mixedEdges H) (mixedEdges_noLoops H) (P.localizer j))
      (source (mixed_dimension N) j.val o) :=
  NativePairedFaceIntegration.integrableOn_nativeDensity (mixed_dimension N) j.val o
    (P.partition j) (mixedEdges H) (mixedEdges_noLoops H) (P.localizer j)
    (P.regular j).1 (P.regular j).2

def defect (H : VectorGraph N 2) : ℝ :=
  sourcePhysicalSum N H + correctionPhysicalSum N H - targetPhysicalSum N H

/-- This exact reduction does not claim the physical and native boundaries
have been matched. Both are genuine independently defined expressions. -/
theorem canonicalScalarMixedBoundaryRelation_iff_defect_zero :
    MixedGraphBoundaryProfiles.CanonicalScalarMixedBoundaryRelation (k := ℝ) ↔
      ∀ N (H : VectorGraph N 2), defect H = 0 := by
  rw [canonicalScalarMixedBoundaryRelation_iff_physical_endpoints]
  simp only [PhysicalMixedBoundaryEndpoints, defect, sub_eq_zero]

end EnvelopingIsomorphism.Deformation.MixedScalarBoundaryAssembly
