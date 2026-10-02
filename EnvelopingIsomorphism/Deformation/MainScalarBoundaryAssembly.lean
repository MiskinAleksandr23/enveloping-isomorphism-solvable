import EnvelopingIsomorphism.Deformation.GraphBinaryClusterSums
import EnvelopingIsomorphism.Deformation.GraphCurvaturePhysicalPairs
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

/-! Exact scalar bookkeeping for the main boundary relation and the actual
classified forest Stokes witnesses for each graph. The geometric identification
of those witnesses with the physical cluster and pair sums remains a separate
obligation; this file does not assume that identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
open scoped Classical BigOperators
open UniformBinaryGraphs GraphAssociatorProfiles GraphBinaryClusterSums
open GraphLabelledClusterCounting GraphCurvaturePhysicalPairs GraphCurvatureLabelCounting
open Kontsevich

/-- The actual outgoing-averaged physical real-face sum, including the two
nullary endpoints. All outgoing-slot signs remain explicit. -/
def realClusterSum {N : ℕ} (H : BinaryGraph N 3) : ℝ :=
  ((2 : ℝ)^N)⁻¹ *
    ∑ τ : Fin N → Equiv.Perm (Fin 2), BinaryGraphAveraging.outgoingSign (k := ℝ) τ *
      ∑ a : Fin (N+1), ∑ T : Clusters (innerBlock a (N-a)),
        (rawClusterCoefficient 0
            (castVertices (splitDegree N a).symm (H.permuteOutgoing (fun v ↦ (τ v).symm))) T -
          rawClusterCoefficient 1
            (castVertices (splitDegree N a).symm (H.permuteOutgoing (fun v ↦ (τ v).symm))) T)

/-- The literal physical-pair curvature side, including its proved 3/2
factor after outgoing-slot and quotient-label normalization. -/
def interiorPairSum {n : ℕ} (H : BinaryGraph (n+2) 3) : ℝ :=
  (3 / 2 : ℝ) * ∑ T : PhysicalPair n, physicalCoefficient H T

/-- A concrete finite expression for the remaining geometric boundary defect. -/
def defect {n : ℕ} (H : BinaryGraph (n+2) 3) : ℝ :=
  realClusterSum H - interiorPairSum H

theorem associator_eq_realClusterSum {N : ℕ} (H : BinaryGraph N 3) :
    BinaryGraphAveraging.boundaryAverage
      (associatorProfile N (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      (N.factorial : ℝ)⁻¹ * realClusterSum H := by
  rw [boundaryAverage_canonical_associator_eq_clusters]
  unfold realClusterSum
  ring

theorem curvature_eq_interiorPairSum {n : ℕ} (H : BinaryGraph (n+2) 3) :
    BinaryGraphAveraging.boundaryAverage
      (GraphCurvatureProfiles.curvatureProfile (GraphCurvatureProfiles.canonicalWeight (k := ℝ))) H =
      ((n+2).factorial : ℝ)⁻¹ * interiorPairSum H := by
  rw [boundaryAverage_curvature_eq_physicalPairs]
  unfold interiorPairSum
  ring

/-- The defect is exactly the scalar-profile difference with only the
common nonzero internal factorial removed. -/
theorem boundaryDifference_eq_defect {n : ℕ} (H : BinaryGraph (n+2) 3) :
    BinaryGraphAveraging.boundaryAverage
        (associatorProfile (n+2) (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H -
      BinaryGraphAveraging.boundaryAverage
        (GraphCurvatureProfiles.curvatureProfile (GraphCurvatureProfiles.canonicalWeight (k := ℝ))) H =
      ((n+2).factorial : ℝ)⁻¹ * defect H := by
  rw [associator_eq_realClusterSum, curvature_eq_interiorPairSum]
  simp only [defect, mul_sub]

/-- The common internal MC factorial is cancelled, without discarding any
outgoing average, physical subset, physical pair, or nullary endpoint. -/
theorem canonicalScalarBoundaryRelation_iff_defect_zero :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ) ↔
      ∀ n (H : BinaryGraph (n+2) 3), defect H = 0 := by
  change (∀ n, _ = _) ↔ _
  constructor
  · intro h n H
    have he := congrFun (h n) H
    rw [associator_eq_realClusterSum, curvature_eq_interiorPairSum] at he
    have hn : (((n+2).factorial : ℝ)⁻¹) ≠ 0 := by positivity
    exact sub_eq_zero.mpr (mul_left_cancel₀ hn he)
  · intro h n
    funext H
    rw [associator_eq_realClusterSum, curvature_eq_interiorPairSum]
    exact congrArg (fun x : ℝ ↦ ((n+2).factorial : ℝ)⁻¹ * x) (sub_eq_zero.mp (h n H))

/-- The edge count in the main Stokes problem: binary graphs have two edges
per vertex and three external vertices. -/
theorem main_dimension (n : ℕ) :
    GraphForms.dimension (n+1) 3 = GraphForms.dimension (n+1) 2 + 1 := by
  simp [GraphForms.dimension]

/-- Canonical vertex-major graph edges, used on the actual three-external
configuration compactification. The two-external dimension only counts edges. -/
def mainEdges {n : ℕ} (H : BinaryGraph (n+2) 3) :
    Fin (GraphForms.dimension (n+1) 2) → GraphForms.Edge (n+1) 3 := fun j ↦
  let e := GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)) j
  ⟨e.1, H.target e⟩

theorem mainEdges_noLoops {n : ℕ} (H : BinaryGraph (n+2) 3)
    (j : Fin (GraphForms.dimension (n+1) 2)) :
    (mainEdges H j).target ≠ Sum.inl (mainEdges H j).source :=
  H.noLoops _ _

open ForestOrthantRealization ForestGlobalGraphStokes ForestRadialFaceClassification
open ForestRadialFaceLocalization

/-- The actual partition, graph localizations and orientation furnished by
forest Stokes. Every geometric certificate is retained in the data. -/
structure MainPartition {n : ℕ} (H : BinaryGraph (n+2) 3) where
  charts : Finset (Compactification (0 : Fin (n+2)) 3)
  partition : OriginalPartitionCancellation.Partition charts (n+1) 3
  localizer : ∀ j : charts, Ambient 0 j.val → ℝ
  orientation : charts → ℝ
  cover : ∀ y : Compactification (0 : Fin (n+2)) 3,
    ∃ j : charts, y ∈ (ForestChartOrientation.smallChart 0 j.val).target
  support : ∀ j : charts, tsupport (CompactDRAmbientPartition.cutoff 0 (partition j)) ⊆
    (ForestChartOrientation.smallChart 0 j.val).target
  regular : ∀ j : charts,
    ContDiff ℝ 1 (localForm (main_dimension n) j.val (partition j)
      (mainEdges H) (mainEdges_noLoops H) (localizer j)) ∧
    HasCompactSupport (localForm (main_dimension n) j.val (partition j)
      (mainEdges H) (mainEdges_noLoops H) (localizer j))
  localization : ∀ j : charts, LocalizationAgreement j.val (partition j)
    (mainEdges H) (mainEdges_noLoops H) (localizer j)
  orientation_sign : ∀ j : charts, orientation j = 1 ∨ orientation j = -1
  orientation_jacobian : ∀ j : charts, ∀ z ∈ positiveRegion (main_dimension n) j.val,
    orientation j * OrientedFormChangeVariables.jacobian (chart (main_dimension n) j.val) z =
      |OrientedFormChangeVariables.jacobian (chart (main_dimension n) j.val) z|
  cancellation : ∑ j : charts, orientation j * ∑ k : Kind,
    classifiedContribution (main_dimension n) j.val (partition j)
      (mainEdges H) (mainEdges_noLoops H) (localizer j) k = 0

/-- No geometric matching assumption is needed to construct these original
native integral witnesses for every main graph. -/
theorem exists_mainPartition {n : ℕ} (H : BinaryGraph (n+2) 3) : Nonempty (MainPartition H) := by
  obtain ⟨s, ρ, κ, ε, hc, hs, hr, hl, he, hj, hz⟩ :=
    exists_classified_boundary_cancellation (main_dimension n) (mainEdges H) (mainEdges_noLoops H)
  exact ⟨⟨s, ρ, κ, ε, hc, hs, hr, hl, he, hj, hz⟩⟩

def mainPartition {n : ℕ} (H : BinaryGraph (n+2) 3) : MainPartition H :=
  Classical.choice (exists_mainPartition H)

/-- Literal finite chart sum of signed, localized native face integrals. -/
def nativeBoundary {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H) : ℝ :=
  ∑ j : P.charts, P.orientation j * ∑ k : Kind,
    classifiedContribution (main_dimension n) j.val (P.partition j)
      (mainEdges H) (mainEdges_noLoops H) (P.localizer j) k

/-- One geometric kind, still summed over every chart of the original
partition. In particular the paired kind is not assumed to vanish locally. -/
def nativeKindBoundary {n : ℕ} {H : BinaryGraph (n+2) 3}
    (P : MainPartition H) (k : Kind) : ℝ :=
  ∑ j : P.charts, P.orientation j *
    classifiedContribution (main_dimension n) j.val (P.partition j)
      (mainEdges H) (mainEdges_noLoops H) (P.localizer j) k

theorem nativeBoundary_eq_sum_kind {n : ℕ} {H : BinaryGraph (n+2) 3}
    (P : MainPartition H) : nativeBoundary P = ∑ k : Kind, nativeKindBoundary P k := by
  simp only [nativeBoundary, nativeKindBoundary, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem nativeBoundary_eq_zero {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H) :
    nativeBoundary P = 0 := P.cancellation

/-- Exact missing geometric endpoint, as an equivalence, not an assumed
boundary theorem. To prove the right side one must identify the actual native
integrals with the physical graph weights: reverse coverage, weighted change
of variables and reassembly, large interior vanishing after reassembly, and
both pure-boundary and infinity endpoints are still required. -/
theorem canonicalScalarBoundaryRelation_iff_native_matching :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ) ↔
      ∀ n (H : BinaryGraph (n+2) 3), defect H = nativeBoundary (mainPartition H) := by
  simp only [nativeBoundary_eq_zero]
  exact canonicalScalarBoundaryRelation_iff_defect_zero

end EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
