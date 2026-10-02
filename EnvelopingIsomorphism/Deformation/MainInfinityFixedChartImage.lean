import EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityEmbedding

/-! Exact infinity-face image of a specified original forest chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainInfinityFixedChartImage
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open InfinityForestSimpleCluster (lower upper)
open InfinityForestSimpleCoordinates InfinityForestResolvedCoordinates
open MainFixedSimpleChartTransfer
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)

include ho in
theorem collisionMask_eq : collisionMask (n := n) Finset.univ (lower x o) (upper x o) =
    (representative 0 x o).val.val := by
  have he : RealForestCoarsePositions.labelsSet x o = Finset.univ :=
    infinity_interiorLabels 0 x (RealForestCoarsePositions.node x o)
      ((kind_representative 0 x o).trans ho)
  ext v
  simpa only [he] using (mem_collisionMask
    (RealForestCoarsePositions.labelsSet x o) (lower x o) (upper x o) v).trans
      ((fixed_label_mask 0 x (RealForestCoarsePositions.node x o)
        (RealForestCoarsePositions.infinity_isFixed x o ho) v).symm)

include ho hq hne in
theorem coordinates_eq_of_facePoint
    (y : BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) m q)
    (hy : (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o))
    (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z =
      (BoundaryAnchoredInfinityFreeCoordinates.faceDomain y hy).toDomain.insertion) :
    coordinates hdim x o q z.val = y := by
  let p := BoundaryAnchoredInfinityFreeCoordinates.faceDomain y hy
  have hi : (InfinityForestSimpleCluster.domain hdim x o ho q hq hne z).insertion = p.toDomain.insertion := by
    rw [insertion_eq_native]
    exact hz
  have hd := BoundaryAnchoredInfinityDomain.insertion_injective hi
  have hf := congrArg BoundaryAnchoredInfinityDomain.toFreeDomain hd
  change InfinityForestSimpleCluster.freeDomain hdim x o ho q hq hne z = p.toDomain.toFreeDomain at hf
  rw [BoundaryAnchoredInfinityFreeDomain.toFreeDomain_toDomain] at hf
  have he := congrArg Subtype.val hf
  rw [← coordinates_eq_freeDomain] at he
  change BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val) =
    BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding y at he
  exact Prod.ext (congrArg (fun p ↦ p.1) he) (congrArg (fun p ↦ p.2.1) he)

include ho hq hne in
theorem exists_source_coordinates
    (y : BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) m q)
    (hy : (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o))
    (ht : (BoundaryAnchoredInfinityFreeCoordinates.faceDomain y hy).toDomain.insertion ∈
      (ForestOrthantCharts.chart 0 x).target) :
    ∃ z : ForestRadialFaceLocalization.source hdim x o, coordinates hdim x o q z.val = y := by
  let p := BoundaryAnchoredInfinityFreeCoordinates.faceDomain y hy
  obtain ⟨v,z,hv,hm,hz⟩ := infinity_source hdim x p.datum ht
  have he : v = o := MainRealSupportOrbit.orbit_eq_of_representative_mask x v o
    (hm.trans (collisionMask_eq x o ho))
  subst v
  exact ⟨z,coordinates_eq_of_facePoint hdim x o q ho hq hne y hy z hz⟩

include ho hq hne in
theorem facePoint_coordinates (z : ForestRadialFaceLocalization.source hdim x o) :
    (BoundaryAnchoredInfinityFreeCoordinates.faceDomain (coordinates hdim x o q z.val)
      (coordinates_mem_source hdim x o q ho hq hne z)).toDomain.insertion =
      PairedForestSimpleOverlap.facePoint hdim x o z := by
  have hp : BoundaryAnchoredInfinityFreeCoordinates.faceDomain (coordinates hdim x o q z.val)
      (coordinates_mem_source hdim x o q ho hq hne z) =
      InfinityForestSimpleCluster.freeDomain hdim x o ho q hq hne z :=
    Subtype.ext (coordinates_eq_freeDomain hdim x o q ho hq hne z)
  rw [hp]
  simp only [InfinityForestSimpleCluster.freeDomain, BoundaryAnchoredInfinityFreeDomain.toDomain_toFreeDomain]
  exact insertion_eq_native hdim x o ho q hq hne z

include ho hq hne in
theorem image_coordinates_source :
    coordinates hdim x o q '' ForestRadialFaceLocalization.source hdim x o =
      {y | ∃ hy : (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o),
        (BoundaryAnchoredInfinityFreeCoordinates.faceDomain y hy).toDomain.insertion ∈
          (ForestOrthantCharts.chart 0 x).target} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨coordinates_mem_source hdim x o q ho hq hne ⟨z,hz⟩,?_⟩
    rw [facePoint_coordinates hdim x o q ho hq hne ⟨z,hz⟩]
    exact (ForestOrthantCharts.chart 0 x).map_source hz.2
  · rintro ⟨hy,ht⟩
    obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o q ho hq hne y hy ht
    exact ⟨z.val,z.property,hz⟩

end EnvelopingIsomorphism.Deformation.MainInfinityFixedChartImage
