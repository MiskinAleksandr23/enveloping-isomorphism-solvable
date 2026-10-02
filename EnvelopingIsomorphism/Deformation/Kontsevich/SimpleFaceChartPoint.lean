import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalProductCoverage

/-! A translated real native chart represents the identical original
compactification point on its full source, retaining physical labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceChartPoint
open Configuration InteriorGraphFaceCoordinates PairedForestSimpleCluster
open PairedForestSmoothProduct PairedForestProductChart PairedForestCanonicalMarks
open SimpleProductPhaseIdentification SimpleFaceNativeAtlas
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
variable {a b : Fin (n+1)} {T : Finset (Fin (n+1))}

theorem toFree_shift (k : ℤ) (p : ProductCoordinates (0 : Fin (n+1)) a b T m) :
    (toAngular (shift k p)).toFree = (toAngular p).toFree :=
  PairedForestCanonicalProductCoverage.toFree_turn k p

theorem boundaryPoint_shift (ha : a ∈ T) (hb : b ∈ T) (hg : (0 : Fin (n+1)) ∈ T → a = 0)
    (k : ℤ) (p : ProductCoordinates (0 : Fin (n+1)) a b T m)
    (hp : (toAngular p).toFree.OpenConditions)
    (hp' : (toAngular (shift k p)).toFree.OpenConditions) :
    (InteriorFaceDRCoordinates.datum ha hb hg (shift k p) hp').toInteriorCollisionData.boundaryPoint =
      (InteriorFaceDRCoordinates.datum ha hb hg p hp).toInteriorCollisionData.boundaryPoint := by
  have hf : InteriorFaceDRCoordinates.freeDomain (shift k p) hp' = InteriorFaceDRCoordinates.freeDomain p hp :=
    Subtype.ext (toFree_shift k p)
  simp only [InteriorFaceDRCoordinates.datum,hf]

/-- The real chart's target map is exactly its native product map followed
by the stored integer turn and canonical mark identification. -/
theorem realChart_toProduct (c : ChartIndex hdim a b T) (w : BoxStokes.Coord r) :
    InteriorGraphFaceCoordinates.toProduct (realChart hdim c w) =
      shift c.turn (nativeEquiv hdim c (localChart hdim c.center c.orbit c.paired c.point w)) := by
  change InteriorGraphFaceCoordinates.toProduct (InteriorGraphFaceCoordinates.toProduct.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem realChart_openConditions (c : ChartIndex hdim a b T) {w : BoxStokes.Coord r}
    (hw : w ∈ (realChart hdim c).source) :
    (toAngular (InteriorGraphFaceCoordinates.toProduct (realChart hdim c w))).toFree.OpenConditions := by
  rw [realChart_toProduct,toFree_shift]
  apply (nativeEquiv_openConditions hdim c _).mpr
  exact PairedForestProductOverlap.toProduct_openConditions hdim c.center c.orbit c.paired
    (phase hdim c.center c.orbit c.paired c.point)
    ⟨w,localChart_source_subset hdim c.center c.orbit c.paired c.point ((realChart_source hdim c) ▸ hw)⟩

/-- Equality of the physical boundary points is proved for every chart source
point, so half-open product injectivity can compare different chart images. -/
theorem realChart_boundaryPoint (c : ChartIndex hdim a b T)
    (ha : a ∈ T) (hb : b ∈ T) (hg : (0 : Fin (n+1)) ∈ T → a = 0)
    {w : BoxStokes.Coord r} (hw : w ∈ (realChart hdim c).source) :
    (InteriorFaceDRCoordinates.datum ha hb hg
      (InteriorGraphFaceCoordinates.toProduct (realChart hdim c w))
      (realChart_openConditions hdim c hw)).toInteriorCollisionData.boundaryPoint =
      PairedForestSimpleOverlap.facePoint hdim c.center c.orbit
        ⟨w,localChart_source_subset hdim c.center c.orbit c.paired c.point ((realChart_source hdim c) ▸ hw)⟩ := by
  let z : Source hdim c.center c.orbit :=
    ⟨w,localChart_source_subset hdim c.center c.orbit c.paired c.point ((realChart_source hdim c) ▸ hw)⟩
  have hp := PairedForestProductOverlap.toProduct_openConditions hdim c.center c.orbit c.paired
    (phase hdim c.center c.orbit c.paired c.point) z
  change (toAngular (localChart hdim c.center c.orbit c.paired c.point w)).toFree.OpenConditions at hp
  have hc := (nativeEquiv_openConditions hdim c _).mpr hp
  have hd : ∀ (p q : ProductCoordinates 0 a b T m)
      (hp : (toAngular p).toFree.OpenConditions) (hq : (toAngular q).toFree.OpenConditions),
      p = q → (InteriorFaceDRCoordinates.datum ha hb hg p hp).toInteriorCollisionData.boundaryPoint =
        (InteriorFaceDRCoordinates.datum ha hb hg q hq).toInteriorCollisionData.boundaryPoint := by
    intro p q hp hq h; subst q; rfl
  have hsc : (toAngular (shift c.turn (nativeEquiv hdim c (localChart hdim c.center c.orbit c.paired c.point w)))).toFree.OpenConditions := by
    rwa [toFree_shift]
  refine (hd _ _ (realChart_openConditions hdim c hw) hsc (realChart_toProduct hdim c w)).trans ?_
  rw [boundaryPoint_shift ha hb hg c.turn _ hc,
    nativeEquiv_boundaryPoint hdim c ha hb hg _ hp]
  exact (congrArg (fun D : SingleInteriorCluster 0 m (S c.center c.orbit c.paired) ↦ D.toInteriorCollisionData.boundaryPoint)
    (PairedForestProductOverlap.datum_toProduct hdim c.center c.orbit c.paired
      (phase hdim c.center c.orbit c.paired c.point) z)).trans
    (PairedForestSimpleOverlap.slice_insertion hdim c.center c.orbit c.paired z)

/-- A source point mapping to a prescribed full simple-face parameter
represents exactly that simple point. This form avoids dependent rewrite of
admissibility certificates in downstream image reassembly. -/
theorem realChart_point_eq (c : ChartIndex hdim a b T)
    (ha : a ∈ T) (hb : b ∈ T) (hba : b ≠ a) (hg : (0 : Fin (n+1)) ∈ T → a = 0)
    {w : BoxStokes.Coord r} (hw : w ∈ (realChart hdim c).source)
    (y : InteriorFacePartitionReassembly.FaceRegion (0 : Fin (n+1)) a b T m)
    (he : realChart hdim c w = y.val) :
    PairedForestSimpleOverlap.facePoint hdim c.center c.orbit
      ⟨w,localChart_source_subset hdim c.center c.orbit c.paired c.point ((realChart_source hdim c) ▸ hw)⟩ =
      InteriorFacePartitionReassembly.facePoint ha hb hba hg y := by
  have hp := realChart_boundaryPoint hdim c ha hb hg hw
  refine hp.symm.trans ?_
  have hy := openConditions_toAngular ha hba (InteriorGraphFaceCoordinates.toProduct y.val) y.property.1.2 y.property.2
  have hd : ∀ (p q : ProductCoordinates 0 a b T m)
      (hp : (toAngular p).toFree.OpenConditions) (hq : (toAngular q).toFree.OpenConditions),
      p = q → (InteriorFaceDRCoordinates.datum ha hb hg p hp).toInteriorCollisionData.boundaryPoint =
        (InteriorFaceDRCoordinates.datum ha hb hg q hq).toInteriorCollisionData.boundaryPoint := by
    intro p q hp hq h; subst q; rfl
  exact hd _ _ _ hy (congrArg InteriorGraphFaceCoordinates.toProduct he)

end EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceChartPoint
