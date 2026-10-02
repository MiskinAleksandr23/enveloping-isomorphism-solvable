import EnvelopingIsomorphism.Deformation.MainClassifiedFaceAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestIntrinsicReassembly
import EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions

/-! Intrinsic physical-label reassembly of the paired part of main Stokes.
Canonical-center reverse coverage is supplied by SingleInteriorExtractedPartitions.
Transfer to each chart of a given finite partition and integration over its
fixed-face image are separate from local native partition independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedClusterAssembly
open scoped Classical BigOperators
open UniformBinaryGraphs MainScalarBoundaryAssembly MainClassifiedFaceAssembly Kontsevich
open ForestRadialFaceClassification ForestRadialFaceLocalization MeasureTheory BoxStokes
open PairedForestProductChart PairedForestOverlapJacobian
open GraphCurvatureLabelCounting GraphCurvaturePhysicalPairs
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)

/-- Every countable measurable partition of the same native source gives the
same paired value. The displayed coverage hypothesis concerns only that native
source; it is not the outstanding reverse simple-face coverage assertion. -/
theorem pairedValue_eq_partition (j : P.charts) (o : Orbit 0 j.val)
    (ho : kind 0 j.val o = .paired)
    {J : Type*} [Countable J]
    (center : J → PairedForestSmoothProduct.Source (main_dimension n) j.val o)
    (s : J → Set (Coord (GraphForms.dimension (n+1) 2)))
    (hs : ∀ l, MeasurableSet (s l))
    (hdis : Pairwise (fun l k ↦ Disjoint (s l) (s k)))
    (hsub : ∀ l, s l ⊆ (localChart (main_dimension n) j.val o ho (center l)).source)
    (hcover : (⋃ l, s l) = PairedForestSmoothProduct.Source (main_dimension n) j.val o) :
    pairedValue P j o ho = ∑' l, productFaceSign (main_dimension n) j.val o ho *
      (∫ p in localChart (main_dimension n) j.val o ho (center l) '' s l,
        productCutoff j.val o ho (P.partition j) p *
          PairedForestProductGraphDensity.productDensity (main_dimension n) j.val o ho (mainEdges H) p) := by
  rw [pairedValue_eq_orbitValue]
  exact (PairedForestIntrinsicReassembly.hasSum_graphIntegral_partition
    (main_dimension n) j.val o ho (P.partition j) (mainEdges H) (mainEdges_noLoops H)
    (P.localizer j) (P.localization j) (P.support j) (P.orientation j)
    (P.orientation_jacobian j) (P.regular j).1 (P.regular j).2
    center s hs hdis hsub hcover).tsum_eq.symm

/-- All original chart/orbit contributions with one fixed physical cluster.
This is a native finite fibre sum of convergent graph-integral series. -/
def clusterValue (S : Finset (Fin (n+2))) : ℝ :=
  ∑ j : P.charts, ∑ o : Orbit 0 j.val,
    if ho : kind 0 j.val o = .paired then
      if PairedForestSimpleCluster.S j.val o ho = S then pairedValue P j o ho else 0
    else 0

/-- Finite reindexing by intrinsic labels, with every multiplicity retained. -/
theorem sum_clusterValue_eq_paired
    (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o) :
    (∑ S : Finset (Fin (n+2)), clusterValue P S) = transportedKind P D .paired := by
  unfold clusterValue transportedKind
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : kind 0 j.val o = .paired
  · simp only [dif_pos ho, if_pos ho]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rw [pairedValue_eq_orbitValue, transportedValue_eq_orbitValue]
  · simp only [dif_neg ho, if_neg ho, Finset.sum_const_zero]

/-- Empty and singleton physical clusters do not occur in the paired tree. -/
theorem clusterValue_eq_zero_of_card_lt_two (S : Finset (Fin (n+2))) (hS : S.card < 2) :
    clusterValue P S = 0 := by
  unfold clusterValue
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro o _
  split_ifs with ho he
  · have h := ForestRadialClusterLabels.upperNode_card 0 j.val o ho
    change 1 < (PairedForestSimpleCluster.S j.val o ho).card at h
    rw [he] at h
    omega
  · rfl
  · rfl

/-- The physical scalar target for each paired cluster: an actual pair gets
its extracted coefficient, and larger clusters have the angular-zero target.
Equality to a native cluster sum is NOT proved by this definition. -/
def clusterTarget (S : Finset (Fin (n+2))) : ℝ :=
  if hS : S.card = 2 then -(3 / 2 : ℝ) * physicalCoefficient H ⟨S,hS⟩ else 0

/-- Pure finite bookkeeping from the two-element physical subsets to the
already proved physical-pair curvature coefficient. -/
theorem sum_clusterTarget :
    (∑ S : Finset (Fin (n+2)), clusterTarget (H := H) S) = -interiorPairSum H := by
  have hp : ∀ T : PhysicalPair n, clusterTarget (H := H) T.val =
      -(3 / 2 : ℝ) * physicalCoefficient H T := by
    intro T
    simp only [clusterTarget, dif_pos T.property]
  have hn : ∀ T : {S : Finset (Fin (n+2)) // ¬ S.card = 2},
      clusterTarget (H := H) T.val = 0 := by
    intro T
    simp only [clusterTarget, dif_neg T.property]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun S : Finset (Fin (n+2)) ↦ S.card = 2)]
  simp_rw [hp, hn]
  simp only [Finset.sum_const_zero, add_zero, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum, interiorPairSum]

/-- The paired matching hypothesis is needed only for actual physical pairs
and fully reassembled clusters of size at least three. The latter is a sum
over all original chart pieces, not a vanishing assertion for weighted pieces. -/
theorem cluster_matching_of_pairs_and_large (c : ℝ)
    (hpairs : ∀ T : PhysicalPair n, c * clusterValue P T.val =
      -(3 / 2 : ℝ) * physicalCoefficient H T)
    (hlarge : ∀ S : Finset (Fin (n+2)), 3 ≤ S.card → c * clusterValue P S = 0)
    (S : Finset (Fin (n+2))) :
    c * clusterValue P S = clusterTarget (H := H) S := by
  by_cases hS : S.card = 2
  · simpa only [clusterTarget, dif_pos hS] using hpairs ⟨S,hS⟩
  · rw [clusterTarget, dif_neg hS]
    by_cases hlargeS : 3 ≤ S.card
    · exact hlarge S hlargeS
    · rw [clusterValue_eq_zero_of_card_lt_two P S (by omega), mul_zero]

/-- Intrinsic per-cluster matching implies the single paired equality used by
classified Stokes. No representative chart, angular branch or subordinate
partition remains in the scalar target. -/
theorem paired_matching_of_cluster_matching
    (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o) (c : ℝ)
    (hcluster : ∀ S : Finset (Fin (n+2)), c * clusterValue P S = clusterTarget (H := H) S) :
    interiorPairSum H = -(c * transportedKind P D .paired) := by
  have h : c * transportedKind P D .paired = -interiorPairSum H := by
    rw [← sum_clusterValue_eq_paired P D, Finset.mul_sum]
    simp_rw [hcluster]
    exact sum_clusterTarget
  linarith

/-- Exact conditional endpoint after removing small impossible clusters and
all branch/partition choices from the paired matching obligations. The real
matching and global paired reassembly inputs remain explicitly visible. -/
theorem defect_eq_zero_of_intrinsic_matching
    (D : ∀ j : P.charts, ∀ o : Orbit 0 j.val, FaceCoordinates P j o) (c : ℝ)
    (hreal : realClusterSum H = c * realTransported P D)
    (hpairs : ∀ T : PhysicalPair n, c * clusterValue P T.val =
      -(3 / 2 : ℝ) * physicalCoefficient H T)
    (hlarge : ∀ S : Finset (Fin (n+2)), 3 ≤ S.card → c * clusterValue P S = 0) :
    defect H = 0 :=
  defect_eq_zero_of_geometric_matching P D c hreal
    (paired_matching_of_cluster_matching P D c (cluster_matching_of_pairs_and_large P c hpairs hlarge))

end EnvelopingIsomorphism.Deformation.MainPairedClusterAssembly
