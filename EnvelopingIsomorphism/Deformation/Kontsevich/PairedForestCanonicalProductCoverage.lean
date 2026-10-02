import EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestGraphFormOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalMarks
import Mathlib.Topology.Compactness.Lindelof

/-! Every genuine simple interior product point has a native strict source
and an actual inverse-function product chart at its compactification point.
The resulting image has exactly the original full DR data and cutoffs. The
real angular representative may differ; this theorem makes no assertion that
an unreduced real angle equals the preferred branch of a native chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalProductCoverage
open Configuration ForestRadialFaceClassification PairedForestSimpleCluster
open PairedForestProductChart PairedForestSmoothProduct
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  {S : Finset (Fin (n+1))} {a b : Fin (n+1)}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : (0 : Fin (n+1)) ∈ S → a = 0)
  (y : InteriorFaceDRCoordinates.Product (i := 0) (a := a) (b := b) (S := S) (m := m))
  (hy : (InteriorGraphFaceCoordinates.toAngular y).toFree.OpenConditions)

include hba in
/-- Actual IFT-chart coverage of each simple face point, retaining its original
cluster mask, identical compactification point, and full DR encoding. -/
theorem exists_native_product_chart :
    let q := (InteriorFaceDRCoordinates.datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint
    ∃ (o : Orbit 0 q) (ho : kind 0 q o = .paired) (z : Source hdim q o),
      PairedForestSimpleCluster.S q o ho = S ∧
      PairedForestSimpleOverlap.facePoint hdim q o z = q ∧
      z.val ∈ (localChart hdim q o ho z).source ∧
      localChart hdim q o ho z z.val ∈ (localChart hdim q o ho z).target ∧
      InteriorFaceDRCoordinates.ambient (localChart hdim q o ho z z.val) =
        InteriorFaceDRCoordinates.ambient y := by
  dsimp only
  obtain ⟨o, ho, z, hS, hz⟩ :=
    SingleInteriorExtractedPartitions.canonicalDatum_exists_source_with_mask hdim ha hb hba hanchor y hy
  refine ⟨o, ho, z, hS, hz, self_mem_localChart_source hdim _ o ho z,
    (localChart hdim _ o ho z).map_source (self_mem_localChart_source hdim _ o ho z), ?_⟩
  rw [localChart_apply, map, PairedForestProductOverlap.ambient_toProduct,
    ForestRadialFaceImmersion.forward_data,
    InteriorFaceDRCoordinates.ambient_eq_boundaryPoint ha hb hanchor y hy]
  change CompactDRCoordinates.dataEmbedding
    (projectDR (PairedForestSimpleOverlap.facePoint hdim _ o z).val) = _
  rw [hz]

include hba in
/-- The coverage preserves any original ambient partition cutoff, not only
its support or its value up to an unknown factor. -/
theorem exists_native_product_chart_cutoff
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) :
    let q := (InteriorFaceDRCoordinates.datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint
    ∃ (o : Orbit 0 q) (ho : kind 0 q o = .paired) (z : Source hdim q o),
      PairedForestSimpleCluster.S q o ho = S ∧
      localChart hdim q o ho z z.val ∈ (localChart hdim q o ho z).target ∧
      InteriorFaceDRCoordinates.ambient (localChart hdim q o ho z z.val) =
        InteriorFaceDRCoordinates.ambient y ∧
      PairedForestOverlapJacobian.productCutoff q o ho ρ (localChart hdim q o ho z z.val) =
        ρ (CompactDRCoordinates.realCoordinates (n+1) m (InteriorFaceDRCoordinates.ambient y)) := by
  obtain ⟨o, ho, z, hS, _, _, hp, hDR⟩ := exists_native_product_chart hdim ha hb hba hanchor y hy
  exact ⟨o, ho, z, hS, hp, hDR, congrArg (fun v ↦ ρ (CompactDRCoordinates.realCoordinates (n+1) m v)) hDR⟩

open InteriorGraphFaceCoordinates

include hba in
/-- On one fixed marked face, equality of the physical compactification point
recovers all shape/coarse coordinates. The only ambiguity is an integral turn
of the real angle, proved from injectivity of normalized slice insertion. -/
theorem coordinates_eq_mod_turn
    (y' : InteriorFaceDRCoordinates.Product (i := 0) (a := a) (b := b) (S := S) (m := m))
    (hy' : (toAngular y').toFree.OpenConditions)
    (hq : (InteriorFaceDRCoordinates.datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint =
      (InteriorFaceDRCoordinates.datum ha hb hanchor y' hy').toInteriorCollisionData.boundaryPoint) :
    y.1.2 = y'.1.2 ∧ y.2 = y'.2 ∧ ∃ k : ℤ, y.1.1 = y'.1.1 + k * (2 * Real.pi) := by
  have hs : ClusterFreeDomain.toSlice ha hb hba hanchor (InteriorFaceDRCoordinates.freeDomain y hy) =
      ClusterFreeDomain.toSlice ha hb hba hanchor (InteriorFaceDRCoordinates.freeDomain y' hy') :=
    NormalizedInteriorClusterSlice.insertion_injective ha hb hba hq
  have hf := (clusterFreeHomeomorph ha hb hba hanchor).injective hs
  have hfree : (toAngular y).toFree = (toAngular y').toFree := congrArg Subtype.val hf
  have he : Circle.exp y.1.1 = Circle.exp y'.1.1 := congrArg (fun q ↦ q.2.2.2.1) hfree
  have hu : circleParameter y.1.1 = circleParameter y'.1.1 := by
    simpa only [circleParameter_eq] using congrArg Subtype.val he
  refine ⟨?_, ?_, Circle.exp_eq_exp.mp he⟩
  · funext j
    have hj := congrFun (congrArg (fun q ↦ q.2.1) hfree) (shapeEnum.symm j)
    change circleParameter y.1.1 * y.1.2 (shapeEnum (shapeEnum.symm j)) =
      circleParameter y'.1.1 * y'.1.2 (shapeEnum (shapeEnum.symm j)) at hj
    simp only [Equiv.apply_symm_apply, hu] at hj
    exact mul_left_cancel₀ (by simpa only [circleParameter_eq] using (Circle.exp y'.1.1).coe_ne_zero) hj
  · apply Prod.ext
    · funext j
      have hj := congrFun (congrArg Prod.fst hfree) (coarseEnum.symm j)
      simpa only [toAngular, ClusterAngularCoordinates.toFree, Equiv.apply_symm_apply] using hj
    · exact congrArg (fun q ↦ q.2.2.1) hfree

include ha hb hba hanchor hy in
theorem coordinates_eq_mod_turn_of_ambient_eq
    (y' : InteriorFaceDRCoordinates.Product (i := 0) (a := a) (b := b) (S := S) (m := m))
    (hy' : (toAngular y').toFree.OpenConditions)
    (hDR : InteriorFaceDRCoordinates.ambient y = InteriorFaceDRCoordinates.ambient y') :
    y.1.2 = y'.1.2 ∧ y.2 = y'.2 ∧ ∃ k : ℤ, y.1.1 = y'.1.1 + k * (2 * Real.pi) := by
  apply coordinates_eq_mod_turn ha hb hba hanchor y hy y' hy'
  apply projectDR_injective_on_compactification 0
  apply CompactDRCoordinates.dataEmbedding_injective (n+1) m
  simpa only [← InteriorFaceDRCoordinates.ambient_eq_boundaryPoint ha hb hanchor y hy,
    ← InteriorFaceDRCoordinates.ambient_eq_boundaryPoint ha hb hanchor y' hy'] using hDR

/-- Canonical label equalities induce a literal linear coordinate transport. -/
def productCast {i a₁ b₁ a₂ b₂ : Fin (n+1)} {S₁ S₂ : Finset (Fin (n+1))}
    (ha' : a₁ = a₂) (hb' : b₁ = b₂) (hS' : S₁ = S₂) :
    ProductCoordinates i a₁ b₁ S₁ m ≃L[ℝ] ProductCoordinates i a₂ b₂ S₂ m := by
  subst a₂ b₂ S₂
  exact ContinuousLinearEquiv.refl ℝ _

theorem ambient_productCast {i a₁ b₁ a₂ b₂ : Fin (n+1)} {S₁ S₂ : Finset (Fin (n+1))}
    (ha' : a₁ = a₂) (hb' : b₁ = b₂) (hS' : S₁ = S₂)
    (p : ProductCoordinates i a₁ b₁ S₁ m) :
    InteriorFaceDRCoordinates.ambient (productCast (m := m) ha' hb' hS' p) =
      InteriorFaceDRCoordinates.ambient p := by
  subst a₂ b₂ S₂
  rfl

theorem openConditions_productCast {i a₁ b₁ a₂ b₂ : Fin (n+1)} {S₁ S₂ : Finset (Fin (n+1))}
    (ha' : a₁ = a₂) (hb' : b₁ = b₂) (hS' : S₁ = S₂)
    (p : ProductCoordinates i a₁ b₁ S₁ m)
    (hp : (toAngular p).toFree.OpenConditions) :
    (toAngular (productCast (m := m) ha' hb' hS' p)).toFree.OpenConditions := by
  subst a₂ b₂ S₂
  exact hp

/-- Change only the real angular representative by an integral full turn. -/
def turn (k : ℤ) : ProductCoordinates (0 : Fin (n+1)) a b S m ≃ₜ
    ProductCoordinates (0 : Fin (n+1)) a b S m :=
  ((Homeomorph.addRight (k * (2 * Real.pi))).prodCongr
    (Homeomorph.refl (InteriorFiberAngleSplit.Shape (shapeN a b S)))).prodCongr (Homeomorph.refl _)

include hba in
/-- Exact Euclidean product target coverage after canonical mark transport and
an explicit integral angular turn. The chart is obtained from the actual native
IFT chart by a linear identification and a translation, not an assumed map. -/
theorem exists_product_chart
    (haMark : a = PairedForestCanonicalMarks.canonicalAnchor S)
    (hbMark : b = PairedForestCanonicalMarks.canonicalReference S) :
    let q := (InteriorFaceDRCoordinates.datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint
    ∃ (o : Orbit 0 q) (ho : kind 0 q o = .paired) (z : Source hdim q o)
      (ha' : anchor q o ho = a) (hb' : reference q o ho = b)
      (hS' : PairedForestSimpleCluster.S q o ho = S) (k : ℤ),
      let e := (localChart hdim q o ho z).transHomeomorph
        ((productCast (m := m) ha' hb' hS').toHomeomorph.trans (turn (m := m) (a := a) (b := b) (S := S) k))
      z.val ∈ e.source ∧ e z.val = y ∧ y ∈ e.target := by
  dsimp only
  generalize hqdef : (InteriorFaceDRCoordinates.datum ha hb hanchor y hy).toInteriorCollisionData.boundaryPoint = q
  have hcov := exists_native_product_chart hdim ha hb hba hanchor y hy
  dsimp only at hcov
  rw [hqdef] at hcov
  obtain ⟨o, ho, z, hS', hq, hzs, hpt, hDR⟩ := hcov
  have ha' : anchor _ o ho = a := by
    rw [PairedForestCanonicalMarks.anchor_eq_canonical, hS', ← haMark]
  have hb' : reference _ o ho = b := by
    rw [PairedForestCanonicalMarks.reference_eq_canonical, hS', ← hbMark]
  let p := localChart hdim _ o ho z z.val
  let C := productCast (i := (0 : Fin (n+1))) (m := m) ha' hb' hS'
  have hp : (toAngular p).toFree.OpenConditions :=
    PairedForestProductOverlap.toProduct_openConditions hdim _ o ho (phase hdim _ o ho z) z
  have hc : (toAngular (C p)).toFree.OpenConditions := openConditions_productCast ha' hb' hS' p hp
  have hDc : InteriorFaceDRCoordinates.ambient y = InteriorFaceDRCoordinates.ambient (C p) :=
    hDR.symm.trans (ambient_productCast ha' hb' hS' p).symm
  obtain ⟨hshape, hcoarse, k, hangle⟩ :=
    coordinates_eq_mod_turn_of_ambient_eq ha hb hba hanchor y hy (C p) hc hDc
  refine ⟨o, ho, z, ha', hb', hS', k, ?_⟩
  let e := (localChart hdim _ o ho z).transHomeomorph
    (C.toHomeomorph.trans (turn (m := m) (a := a) (b := b) (S := S) k))
  have he : e z.val = y := by
    change (((C p).1.1 + k * (2 * Real.pi), (C p).1.2), (C p).2) = y
    exact Prod.ext (Prod.ext hangle.symm hshape.symm) hcoarse.symm
  exact ⟨hzs, he, he ▸ e.map_source hzs⟩

/-- Full turns preserve the genuine free coordinates, including the Circle
coordinate, rather than just the numerical graph integral. -/
theorem toFree_turn (k : ℤ)
    (p : ProductCoordinates (0 : Fin (n+1)) a b S m) :
    (toAngular (turn (m := m) (a := a) (b := b) (S := S) k p)).toFree = (toAngular p).toFree := by
  have he : Circle.exp (p.1.1 + k * (2 * Real.pi)) = Circle.exp p.1.1 :=
    Circle.exp_eq_exp.mpr ⟨k,rfl⟩
  have hu : circleParameter (p.1.1 + k * (2 * Real.pi)) = circleParameter p.1.1 := by
    simpa only [circleParameter_eq] using congrArg Subtype.val he
  change (toAngular ((p.1.1 + k * (2 * Real.pi), p.1.2), p.2)).toFree = _
  simp only [toAngular, ClusterAngularCoordinates.toFree, he, hu]

include ha hb hanchor in
/-- Integer angle changes preserve the full physical DR point wherever the
simple face is admissible. -/
theorem ambient_turn (k : ℤ)
    (p : ProductCoordinates (0 : Fin (n+1)) a b S m)
    (hp : (toAngular p).toFree.OpenConditions) :
    InteriorFaceDRCoordinates.ambient (turn (m := m) (a := a) (b := b) (S := S) k p) =
      InteriorFaceDRCoordinates.ambient p := by
  have hp' : (toAngular (turn (m := m) (a := a) (b := b) (S := S) k p)).toFree.OpenConditions := by
    rwa [toFree_turn]
  rw [InteriorFaceDRCoordinates.ambient_eq_boundaryPoint ha hb hanchor _ hp',
    InteriorFaceDRCoordinates.ambient_eq_boundaryPoint ha hb hanchor _ hp]
  have hf : InteriorFaceDRCoordinates.freeDomain (turn (m := m) (a := a) (b := b) (S := S) k p) hp' =
      InteriorFaceDRCoordinates.freeDomain p hp := Subtype.ext (toFree_turn k p)
  simp only [InteriorFaceDRCoordinates.datum, hf]

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalProductCoverage
