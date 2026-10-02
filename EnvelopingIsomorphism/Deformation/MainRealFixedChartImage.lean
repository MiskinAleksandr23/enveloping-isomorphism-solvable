import EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceChangeVariables

/-! Reverse coverage of the actual proper-real simple-coordinate map of one
specified original forest chart. No local coordinate matching is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealFixedChartImage
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestSimpleCoordinates RealForestResolvedCoordinates
open MainFixedSimpleChartTransfer
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (a b : Fin (n+1)) (ho : kind 0 x o = .properReal)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)

include ho in
theorem collisionMask_eq : collisionMask (labelsSet x o) (lower x o) (upper x o) =
    (representative 0 x o).val.val := by
  ext v
  exact (mem_collisionMask _ _ _ _).trans
    ((fixed_label_mask 0 x (node x o) (RealForestCoarsePositions.properReal_isFixed x o ho) v).symm)

include ho ha hb hne in
theorem coordinates_eq_of_facePoint
    (y : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o))
    (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z =
      anchorHomeomorph b 0 (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) y hy).datum.boundaryPoint) :
    coordinates hdim x o a b z.val = y := by
  let p := BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) y hy
  have hpoint : (RealForestSimpleCluster.domain hdim x o
      (RealForestCoarsePositions.properReal_isFixed x o ho) a b ha hb hne z).insertion = p.toDomain.insertion := by
    rw [insertion_eq_anchorHomeomorph]
    change anchorHomeomorph 0 b (PairedForestSimpleOverlap.facePoint hdim x o z) = p.datum.boundaryPoint
    rw [hz, ← anchorHomeomorph_symm b 0]
    exact (anchorHomeomorph b 0).symm_apply_apply _
  have hd := BoundaryClusterDomain.insertion_injective hpoint
  have hf := congrArg BoundaryClusterDomain.toFreeDomain hd
  change RealForestSimpleCluster.freeDomain hdim x o
    (RealForestCoarsePositions.properReal_isFixed x o ho) a b ha hb hne z = p.toDomain.toFreeDomain at hf
  rw [BoundaryClusterFreeDomain.toFreeDomain_toDomain] at hf
  have he := congrArg Subtype.val hf
  rw [← coordinates_eq_freeDomain] at he
  change BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val) =
    BoundaryClusterFreeCoordinates.faceEmbedding y at he
  exact Prod.ext (congrArg (fun p => p.1) he)
    (Prod.ext (congrArg (fun p => p.2.1) he)
      (Prod.ext (congrArg (fun p => p.2.2.1) he) (congrArg (fun p => p.2.2.2.1) he)))

include ho ha hb hne in
/-- Every actual physical simple point lying in this original chart target
is attained by this chart's unique orbit map, with its exact coordinates. -/
theorem exists_source_coordinates
    (y : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o))
    (hq : anchorHomeomorph b 0 (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) y hy).datum.boundaryPoint ∈
      (ForestOrthantCharts.chart 0 x).target) :
    ∃ z : ForestRadialFaceLocalization.source hdim x o, coordinates hdim x o a b z.val = y := by
  obtain ⟨p,z,hp,hm,hz⟩ := properReal_source_changeAnchor hdim x
    (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) y hy).datum hq
  have he : p = o := MainRealSupportOrbit.orbit_eq_of_representative_mask x p o
    (hm.trans (collisionMask_eq x o ho))
  subst p
  exact ⟨z,coordinates_eq_of_facePoint hdim x o a b ho ha hb hne y hy z hz⟩

include ho ha hb hne in
theorem facePoint_coordinates (z : ForestRadialFaceLocalization.source hdim x o) :
    anchorHomeomorph b 0
      (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) (coordinates hdim x o a b z.val)
        (coordinates_mem_source hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne z)).datum.boundaryPoint =
      PairedForestSimpleOverlap.facePoint hdim x o z := by
  have hp : BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) (coordinates hdim x o a b z.val)
      (coordinates_mem_source hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne z) =
      RealForestSimpleCluster.freeDomain hdim x o (RealForestCoarsePositions.properReal_isFixed x o ho) a b ha hb hne z :=
    Subtype.ext (coordinates_eq_freeDomain hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne z)
  have hi := congrArg (fun p : BoundaryClusterFreeDomain b a (labelsSet x o) m (lower x o) (upper x o) =>
    p.toDomain.insertion) hp
  change (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) (coordinates hdim x o a b z.val)
      (coordinates_mem_source hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne z)).datum.boundaryPoint = _ at hi
  simp only [RealForestSimpleCluster.freeDomain, BoundaryClusterFreeDomain.toDomain_toFreeDomain] at hi
  rw [hi, insertion_eq_anchorHomeomorph, ← anchorHomeomorph_symm 0 b]
  exact (anchorHomeomorph 0 b).symm_apply_apply _

include ho ha hb hne in
/-- Exact image of the complete native strict source. The right side uses
actual membership in the specified original chart, without a cover premise. -/
theorem image_coordinates_source :
    coordinates hdim x o a b '' ForestRadialFaceLocalization.source hdim x o =
      {y | ∃ hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions (lower x o) (upper x o),
        anchorHomeomorph b 0 (BoundaryClusterFaceDR.sourcePoint (lower x o) (upper x o) y hy).datum.boundaryPoint ∈
          (ForestOrthantCharts.chart 0 x).target} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨coordinates_mem_source hdim x o a b (RealForestCoarsePositions.properReal_isFixed x o ho) ha hb hne ⟨z,hz⟩,?_⟩
    rw [facePoint_coordinates hdim x o a b ho ha hb hne ⟨z,hz⟩]
    exact (ForestOrthantCharts.chart 0 x).map_source hz.2
  · rintro ⟨hy,hq⟩
    obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o a b ho ha hb hne y hy hq
    exact ⟨z.val,z.property,hz⟩

end EnvelopingIsomorphism.Deformation.MainRealFixedChartImage
