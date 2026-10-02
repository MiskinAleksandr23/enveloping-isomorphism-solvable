import EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestGraphFormOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceChangeVariables

/-! Assembly of actual transported face integrals. Local coordinate replacements
are proved; the remaining physical-weight matching inputs are explicit. No
reverse coverage or global simple-face reassembly is asserted here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainClassifiedFaceAssembly
open scoped Classical BigOperators
open UniformBinaryGraphs MainScalarBoundaryAssembly Kontsevich
open ForestRadialFaceClassification ForestRadialFaceLocalization ForestGlobalGraphStokes
open MeasureTheory BoxStokes Configuration
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)

/-- The original oriented orbit contribution of the original forest partition. -/
def orbitValue (j : P.charts) (o : Orbit 0 j.val) : ℝ :=
  P.orientation j * contribution (main_dimension n) j.val
    (localForm (main_dimension n) j.val (P.partition j) (mainEdges H)
      (mainEdges_noLoops H) (P.localizer j)) o

/-- L1 on the actual strict source is inherited from the compact local form,
so subsequent countable integration needs no supplied integrability premise. -/
theorem integrableOn_nativeDensity (j : P.charts) (o : Orbit 0 j.val) :
    IntegrableOn (NativePairedFaceIntegration.nativeDensity (main_dimension n) j.val o
      (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j))
      (source (main_dimension n) j.val o) :=
  NativePairedFaceIntegration.integrableOn_nativeDensity (main_dimension n) j.val o
    (P.partition j) (mainEdges H) (mainEdges_noLoops H) (P.localizer j)
    (P.regular j).1 (P.regular j).2

/-- Literal weighted graph integrals in the countable paired product charts. -/
def pairedValue (j : P.charts) (o : Orbit 0 j.val) (ho : kind 0 j.val o = .paired) : ℝ :=
  ∑' l : PairedForestCountableLocalization.Index (main_dimension n) j.val o ho,
    PairedForestOverlapJacobian.productFaceSign (main_dimension n) j.val o ho *
      PairedForestGraphFormOverlap.localizedGraphIntegral (main_dimension n) j.val o ho
        (P.partition j) (mainEdges H) l

theorem pairedValue_eq_orbitValue (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .paired) : pairedValue P j o ho = orbitValue P j o := by
  exact (PairedForestGraphFormOverlap.hasSum_localizedGraphIntegral
    (main_dimension n) j.val o ho (P.partition j) (mainEdges H) (mainEdges_noLoops H)
    (P.localizer j) (P.localization j) (P.support j) (P.orientation j)
    (P.orientation_jacobian j) (P.regular j).1 (P.regular j).2).tsum_eq

/-- Explicit local geometric data only. `native` retains a face for which no
surviving endpoint coordinates have yet been chosen. -/
inductive FaceCoordinates (j : P.charts) (o : Orbit 0 j.val)
  | native
  | paired (ho : kind 0 j.val o = .paired)
  | pure (a b : Fin 3) (ho : kind 0 j.val o = .pureBoundary)
      (hl : a.val = (PureForestSimpleCluster.lower j.val o).val)
      (hu : b.val + 1 = (PureForestSimpleCluster.upper j.val o).val) (hab : a < b)
      (hcard : (boundaryClusterBlock (PureForestSimpleCluster.lower j.val o)
        (PureForestSimpleCluster.upper j.val o)).card = 2)
  | infinity (q : Fin 3) (ho : kind 0 j.val o = .infinity)
      (hq : q ∉ boundaryClusterBlock (InfinityForestSimpleCluster.lower j.val o)
        (InfinityForestSimpleCluster.upper j.val o))
      (hne : (boundaryClusterBlock (InfinityForestSimpleCluster.lower j.val o)
        (InfinityForestSimpleCluster.upper j.val o)).Nonempty)
      (hall : ∀ t : Fin 3, t ≠ q → t ∈ boundaryClusterBlock
        (InfinityForestSimpleCluster.lower j.val o) (InfinityForestSimpleCluster.upper j.val o))

/-- The actual native or transported integral, with the original cutoff,
edge order, lower-face sign and chart orientation. -/
def transportedValue (j : P.charts) (o : Orbit 0 j.val) : FaceCoordinates P j o → ℝ
  | .native => orbitValue P j o
  | .paired ho => pairedValue P j o ho
  | .pure a b ho hl hu hab hcard =>
    P.orientation j * (-((-1 : ℝ) ^ (axis (main_dimension n) j.val o).val) •
      ∫ y in PureForestFaceChangeVariables.map (main_dimension n) j.val o a b ho hl hu hab hcard ''
        source (main_dimension n) j.val o,
        PureForestFaceChangeVariables.transportedDensity (main_dimension n) j.val o a b ho hl hu hab hcard
          (ForestFaceCutoffIntegrability.cutoff (main_dimension n) j.val o (P.partition j))
          (fun e ↦ ForestPositiveGraphForms.forestEdge 0 (mainEdges H e) (mainEdges_noLoops H e)) y)
  | .infinity q ho hq hne hall =>
    P.orientation j * (-((-1 : ℝ) ^ (axis (main_dimension n) j.val o).val) •
      ∫ y in InfinityForestFaceChangeVariables.map (main_dimension n) j.val o q ho hq hne hall ''
        source (main_dimension n) j.val o,
        InfinityForestFaceChangeVariables.transportedDensity (main_dimension n) j.val o q ho hq hne hall
          (ForestFaceCutoffIntegrability.cutoff (main_dimension n) j.val o (P.partition j))
          (fun e ↦ ForestPositiveGraphForms.forestEdge 0 (mainEdges H e) (mainEdges_noLoops H e)) y)

theorem transportedValue_eq_orbitValue (j : P.charts) (o : Orbit 0 j.val)
    (D : FaceCoordinates P j o) : transportedValue P j o D = orbitValue P j o := by
  cases D with
  | native => rfl
  | paired ho => exact pairedValue_eq_orbitValue P j o ho
  | pure a b ho hl hu hab hcard =>
    exact congrArg (P.orientation j * ·)
      (PureForestFaceChangeVariables.contribution_eq_transported_partition
        (main_dimension n) j.val o a b ho hl hu hab hcard (P.partition j)
        (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)).symm
  | infinity q ho hq hne hall =>
    exact congrArg (P.orientation j * ·)
      (InfinityForestFaceChangeVariables.contribution_eq_transported_partition
        (main_dimension n) j.val o q ho hq hne hall (P.partition j)
        (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)).symm

/-- Every paired face uses its proved graph integral series. Other cases
remain available for explicit pure/infinity geometry or native integration. -/
def defaultCoordinates (j : P.charts) (o : Orbit 0 j.val) : FaceCoordinates P j o :=
  if ho : kind 0 j.val o = .paired then .paired ho else .native

variable (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o)

/-- Classified transported sums over all charts and all native radial orbits. -/
def transportedKind (k : Kind) : ℝ :=
  ∑ j : P.charts, ∑ o : Orbit 0 j.val,
    if kind 0 j.val o = k then transportedValue P j o (D j o) else 0

theorem transportedKind_eq_nativeKind (k : Kind) :
    transportedKind P D k = nativeKindBoundary P k := by
  unfold transportedKind nativeKindBoundary classifiedContribution
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : kind 0 j.val o = k
  · simp only [if_pos ho]
    rw [transportedValue_eq_orbitValue, orbitValue,
      contribution_eq_integral_source (main_dimension n) j.val o (P.partition j)
        (mainEdges H) (mainEdges_noLoops H) (P.localizer j) (P.localization j)]
  · simp only [if_neg ho, mul_zero]

/-- Exact classified Stokes in transported graph integrals. Local face
coordinates suffice: no global reverse coverage input is needed for this sum. -/
theorem sum_transportedKind_eq_zero : (∑ k : Kind, transportedKind P D k) = 0 := by
  simp_rw [transportedKind_eq_nativeKind]
  rw [← nativeBoundary_eq_sum_kind, nativeBoundary_eq_zero]

/-- The real contribution retains proper-real, pure-boundary and infinity
classes. In particular neither omitted endpoint is discarded. -/
def realTransported : ℝ :=
  transportedKind P D .properReal + transportedKind P D .pureBoundary + transportedKind P D .infinity

theorem realTransported_add_paired_eq_zero :
    realTransported P D + transportedKind P D .paired = 0 := by
  have h := sum_transportedKind_eq_zero P D
  have hu : (Finset.univ : Finset Kind) = {.paired, .pureBoundary, .properReal, .infinity} := by decide
  rw [hu] at h
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    or_self, not_false_eq_true, Finset.sum_singleton] at h
  unfold realTransported
  linarith

/-- A conditional scalar endpoint with precisely the two remaining global
geometric identifications exposed. Their proofs must account for weighted
coverage/reassembly and physical graph weight matching; none is inferred from
local forward coordinate maps. The common scalar allows the actual graph
normalization without adding a nonzero premise. -/
theorem defect_eq_zero_of_geometric_matching (c : ℝ)
    (hreal : realClusterSum H = c * realTransported P D)
    (hpaired : interiorPairSum H = -(c * transportedKind P D .paired)) :
    defect H = 0 := by
  unfold defect
  rw [hreal, hpaired, sub_neg_eq_add, ← mul_add, realTransported_add_paired_eq_zero, mul_zero]

/-- The global scalar relation follows once the two explicit geometric
matching identities have been proved for every graph. This theorem does not
construct those matching proofs or assert reverse coverage. -/
theorem canonicalScalarBoundaryRelation_of_geometric_matching
    (hmatch : ∀ n (H : BinaryGraph (n+2) 3),
      ∃ (P : MainPartition H)
        (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o) (c : ℝ),
        realClusterSum H = c * realTransported P D ∧
        interiorPairSum H = -(c * transportedKind P D .paired)) :
    GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := ℝ) := by
  apply canonicalScalarBoundaryRelation_iff_defect_zero.mpr
  intro n H
  obtain ⟨P, D, c, hr, hp⟩ := hmatch n H
  exact defect_eq_zero_of_geometric_matching P D c hr hp

end EnvelopingIsomorphism.Deformation.MainClassifiedFaceAssembly
