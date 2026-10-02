import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestInternalCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularChart

/-! Exact overlap of an actual strict paired forest face with the constructed
normalized simple-cluster slice. Full doubled directions and ratios agree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleOverlap
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization
open BoxStokes PairedForestCoarsePositions PairedForestSimpleCluster
open PairedForestResolvedCoordinates PairedForestInternalCoordinates ForestDirectionRatioCoordinates
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)
  (z : ForestRadialFaceLocalization.source hdim x o)

def nativeDomain : Domain (tree 0 x) (canonicalLeaf 0 x) :=
  ⟨PairedForestCoarsePositions.parameters hdim x o z,
    radius_nonneg hdim x o z, (openConditions hdim x o z).1⟩

def facePoint : Compactification (0 : Fin (n + 1)) m :=
  ForestOrthantCharts.chart 0 x (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val))

theorem facePoint_eq_forward : facePoint hdim x o z =
    ForestChartOpenImage.forward 0 x (PairedForestCoarsePositions.sourcePoint hdim x o z) :=
  chart_eq_forward 0 x _ z.property.2

theorem facePoint_projectDR : projectDR (facePoint hdim x o z).val =
    resolvedCoordinates (tree 0 x) (canonicalLeaf 0 x) (nativeDomain hdim x o z) := by
  rw [facePoint_eq_forward, ForestChartOpenImage.forward,
    ForestChartConfigurations.compactificationInsertion_projectDR]
  apply Prod.ext
  · funext e
    change direction (tree 0 x) (canonicalLeaf 0 x)
      (PairedForestCoarsePositions.sourcePoint hdim x o z).val.val e = _
    rw [sourcePoint_parameters]
    rfl
  · funext q
    apply Subtype.ext
    change ratioValue (tree 0 x) (canonicalLeaf 0 x)
      (PairedForestCoarsePositions.sourcePoint hdim x o z).val.val q = _
    rw [sourcePoint_parameters]
    rfl

/-- The full doubled DR array agrees, including external and mirror terms. -/
theorem slice_projectDR : projectDR (slice hdim x o ho z).insertion.val =
    projectDR (facePoint hdim x o z).val := by
  rw [facePoint_projectDR]
  apply Prod.ext
  · funext e
    change (if (datum hdim x o ho z).toInteriorCollisionData.pairBase e = 0 then
      complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity e)
      else complexPhase ((datum hdim x o ho z).toInteriorCollisionData.pairBase e +
        (0 : ℂ) * (datum hdim x o ho z).toInteriorCollisionData.pairVelocity e)) =
      direction (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) e
    simp only [(datum hdim x o ho z).pairBase_eq_zero_iff_clusterPairCollapses, zero_mul, add_zero]
    by_cases he : clusterPairCollapses (S x o ho) e
    · rw [if_pos he]
      exact (direction_internal hdim x o ho z e he).symm
    · rw [if_neg he]
      exact (direction_external hdim x o ho z e he).symm
  · funext q
    apply Subtype.ext
    change (if (datum hdim x o ho z).toInteriorCollisionData.pairBase (firstPair q) = 0 ∧
        (datum hdim x o ho z).toInteriorCollisionData.pairBase (secondPair q) = 0 then
      normalizedNormRatio ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (firstPair q))
        ((datum hdim x o ho z).toInteriorCollisionData.pairVelocity (secondPair q))
      else normalizedNormRatio
        ((datum hdim x o ho z).toInteriorCollisionData.pairBase (firstPair q) +
          (0 : ℂ) * (datum hdim x o ho z).toInteriorCollisionData.pairVelocity (firstPair q))
        ((datum hdim x o ho z).toInteriorCollisionData.pairBase (secondPair q) +
          (0 : ℂ) * (datum hdim x o ho z).toInteriorCollisionData.pairVelocity (secondPair q)) : Set.Icc (0 : ℝ) 1).val =
      ratioValue (tree 0 x) (canonicalLeaf 0 x) (PairedForestCoarsePositions.parameters hdim x o z) q
    simp only [(datum hdim x o ho z).pairBase_eq_zero_iff_clusterPairCollapses, zero_mul, add_zero]
    by_cases hq : clusterPairCollapses (S x o ho) (firstPair q) ∧
        clusterPairCollapses (S x o ho) (secondPair q)
    · rw [if_pos hq]
      exact (ratio_internal hdim x o ho z q hq).symm
    · rw [if_neg hq]
      exact (ratio_external hdim x o ho z q hq).symm

/-- Actual equality in the compactification, not an overlap predicate. -/
theorem slice_insertion : (slice hdim x o ho z).insertion = facePoint hdim x o z :=
  projectDR_injective_on_compactification 0 (slice_projectDR hdim x o ho z)

/-- Every actual strict paired face point lies in a genuine simple angular
chart with the constructed original labels and the correct global anchor. -/
theorem exists_angular_chart :
    ∃ y : ClusterAngularDomain (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m,
      ∃ e : OpenPartialHomeomorph
        (ClusterAngularDomain (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m)
        (Compactification (0 : Fin (n + 1)) m),
        y ∈ e.source ∧ e y = facePoint hdim x o z ∧
          ClusterAngularDomain.toCompactification (anchor_mem x o ho) (reference_mem x o ho)
            (reference_ne_anchor x o ho) (anchor_global x o ho) = e := by
  obtain ⟨y, e, hy, he, hmap⟩ := ClusterAngularDomain.exists_chart_for_slice_face
    (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho)
    (anchor_global x o ho) (slice hdim x o ho z) (slice_scale hdim x o ho z)
  exact ⟨y, e, hy, he.trans (slice_insertion hdim x o ho z), hmap⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleOverlap
