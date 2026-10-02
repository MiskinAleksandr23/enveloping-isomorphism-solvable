import EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceChangeVariables

/-! The complete pure-face image in a specified original forest chart,
with primitive physical collision data and exact coordinate identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPureFixedChartImage
open Kontsevich Configuration ForestRadialFaceClassification ForestRadialClusterLabels
open PureForestSimpleCluster (lower upper)
open PureForestSimpleCoordinates PureForestResolvedCoordinates
open MainFixedSimpleChartTransfer
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
    (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
    (a b : Fin m) (ho : kind 0 x o = .pureBoundary)
    (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)

include ho in
theorem collisionMask_eq : collisionMask (n := n) ∅ (lower x o) (upper x o) =
    (representative 0 x o).val.val := by
  have he : RealForestCoarsePositions.labelsSet x o = ∅ :=
    pureBoundary_interiorLabels 0 x (RealForestCoarsePositions.node x o)
      ((kind_representative 0 x o).trans ho)
  ext v
  simpa only [he] using (mem_collisionMask
    (RealForestCoarsePositions.labelsSet x o) (lower x o) (upper x o) v).trans
      ((fixed_label_mask 0 x (RealForestCoarsePositions.node x o)
        (RealForestCoarsePositions.pureBoundary_isFixed x o ho) v).symm)

include ho hl hu hab in
theorem coordinates_eq_of_facePoint
    (D : PureBoundaryClusterData (0 : Fin (n+1)) m (lower x o) (upper x o) a b)
    (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z = D.boundaryPoint) :
    coordinates hdim x o a b z.val =
      (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) := by
  have hi : (PureForestSimpleCluster.domain hdim x o ho a b hl hu hab z).insertion =
      (PureBoundaryClusterDomain.zeroParameter D).insertion := by
    rw [insertion_eq_native, PureBoundaryClusterDomain.insertion_zeroParameter]
    exact hz
  have hd := congrArg PureBoundaryClusterDomain.datum (PureBoundaryClusterDomain.insertion_injective hi)
  change PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z = D at hd
  rw [coordinates_eq_datum hdim x o a b ho hl hu hab z, hd]

include ho hl hu hab in
theorem exists_source_coordinates
    (D : PureBoundaryClusterData (0 : Fin (n+1)) m (lower x o) (upper x o) a b)
    (hq : D.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ z : ForestRadialFaceLocalization.source hdim x o,
      coordinates hdim x o a b z.val =
        (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) := by
  obtain ⟨p,z,hp,hm,hz⟩ := pureBoundary_source hdim x D hq
  have he : p = o := MainRealSupportOrbit.orbit_eq_of_representative_mask x p o
    (hm.trans (collisionMask_eq x o ho))
  subst p
  exact ⟨z,coordinates_eq_of_facePoint hdim x o a b ho hl hu hab D z hz⟩

include ho hl hu hab in
theorem image_coordinates_source :
    coordinates hdim x o a b '' ForestRadialFaceLocalization.source hdim x o =
      {y | ∃ D : PureBoundaryClusterData (0 : Fin (n+1)) m (lower x o) (upper x o) a b,
        (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) = y ∧
          D.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target} := by
  ext y
  constructor
  · rintro ⟨w,hw,rfl⟩
    let z : ForestRadialFaceLocalization.source hdim x o := ⟨w,hw⟩
    refine ⟨PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z,
      (coordinates_eq_datum hdim x o a b ho hl hu hab z).symm, ?_⟩
    have hi := insertion_eq_native hdim x o ho a b hl hu hab z
    change (PureForestSimpleCluster.datum hdim x o ho a b hl hu hab z).boundaryPoint =
      PairedForestSimpleOverlap.facePoint hdim x o z at hi
    rw [hi]
    exact (ForestOrthantCharts.chart 0 x).map_source hw.2
  · rintro ⟨D,rfl,hq⟩
    obtain ⟨z,hz⟩ := exists_source_coordinates hdim x o a b ho hl hu hab D hq
    exact ⟨z.val,z.property,hz⟩

end EnvelopingIsomorphism.Deformation.MainPureFixedChartImage
