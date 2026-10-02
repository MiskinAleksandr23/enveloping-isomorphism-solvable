import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestIntrinsicReassembly
import EnvelopingIsomorphism.Deformation.Kontsevich.SingleInteriorExtractedPartitions
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly

/-! Exact identification of genuine simple product parameters from their compact
boundary point. The only ambiguity is an integer full turn of the angle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.SimpleProductPhaseIdentification
open Configuration InteriorGraphFaceCoordinates
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def shift (k : ℤ) (p : ProductCoordinates i a b S m) : ProductCoordinates i a b S m :=
  ((p.1.1 + k * (2 * Real.pi), p.1.2), p.2)

/-- Full free-coordinate identification uses injectivity of the actual normalized
slice insertion, including its scale-zero boundary. -/
theorem free_eq_of_boundaryPoint_eq
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (p q : ProductCoordinates i a b S m)
    (hp : (toAngular p).toFree.OpenConditions) (hq : (toAngular q).toFree.OpenConditions)
    (h : (InteriorFaceDRCoordinates.datum ha hb hanchor p hp).toInteriorCollisionData.boundaryPoint =
      (InteriorFaceDRCoordinates.datum ha hb hanchor q hq).toInteriorCollisionData.boundaryPoint) :
    (toAngular p).toFree = (toAngular q).toFree := by
  let ps := ClusterFreeDomain.toSlice ha hb hba hanchor (InteriorFaceDRCoordinates.freeDomain p hp)
  let qs := ClusterFreeDomain.toSlice ha hb hba hanchor (InteriorFaceDRCoordinates.freeDomain q hq)
  have hi : ps.insertion = qs.insertion := h
  have hs := NormalizedInteriorClusterSlice.insertion_injective ha hb hba hi
  have he := congrArg NormalizedInteriorClusterSlice.freeCoordinates hs
  simpa only [ps, qs, ClusterFreeDomain.freeCoordinates_toSlice, InteriorFaceDRCoordinates.freeDomain] using he

/-- Coarse coordinates and normalized shapes are unique; angle ambiguity is
exactly the integer period of the circle exponential. -/
theorem eq_shift_of_free_eq (p q : ProductCoordinates i a b S m)
    (h : (toAngular p).toFree = (toAngular q).toFree) : ∃ k : ℤ, p = shift k q := by
  have he : Circle.exp p.1.1 = Circle.exp q.1.1 :=
    congrArg (fun z : ClusterFreeCoordinates i a b S m ↦ z.2.2.2.1) h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
  refine ⟨k, ?_⟩
  apply Prod.ext
  · apply Prod.ext hk
    funext j
    have hj := congrArg (fun z : ClusterFreeCoordinates i a b S m ↦ z.2.1 (shapeEnum.symm j)) h
    change circleParameter p.1.1 * p.1.2 (shapeEnum (shapeEnum.symm j)) =
      circleParameter q.1.1 * q.1.2 (shapeEnum (shapeEnum.symm j)) at hj
    simp only [Equiv.apply_symm_apply, circleParameter_eq, he] at hj
    exact mul_left_cancel₀ (Circle.exp q.1.1).coe_ne_zero hj
  · apply Prod.ext
    · funext j
      have hj := congrArg (fun z : ClusterFreeCoordinates i a b S m ↦ z.1 (coarseEnum.symm j)) h
      simpa only [toAngular, ClusterAngularCoordinates.toFree, Equiv.apply_symm_apply, shift] using hj
    · exact congrArg (fun z : ClusterFreeCoordinates i a b S m ↦ z.2.2.1) h

/-- No extra inverse/compatibility hypothesis is needed: equality of actual
compactification points recovers the simple product modulo angle period. -/
theorem eq_shift_of_boundaryPoint_eq
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (p q : ProductCoordinates i a b S m)
    (hp : (toAngular p).toFree.OpenConditions) (hq : (toAngular q).toFree.OpenConditions)
    (h : (InteriorFaceDRCoordinates.datum ha hb hanchor p hp).toInteriorCollisionData.boundaryPoint =
      (InteriorFaceDRCoordinates.datum ha hb hanchor q hq).toInteriorCollisionData.boundaryPoint) :
    ∃ k : ℤ, p = shift k q :=
  eq_shift_of_free_eq p q (free_eq_of_boundaryPoint_eq ha hb hba hanchor p q hp hq h)

open PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductChart
variable {N r : ℕ} (hdim : GraphForms.dimension N m = r + 1)
  (x : Compactification (0 : Fin (N + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

/-- Any simple product representing a given strict native point lies in an
integer translate of the image of that native point's actual local chart. -/
theorem mem_shift_localChart_target (p : Product x o ho)
    (hp : (toAngular p).toFree.OpenConditions) (z : Source hdim x o)
    (h : (InteriorFaceDRCoordinates.datum (anchor_mem x o ho) (reference_mem x o ho)
      (anchor_global x o ho) p hp).toInteriorCollisionData.boundaryPoint =
        PairedForestSimpleOverlap.facePoint hdim x o z) :
    ∃ k : ℤ, p ∈ shift k '' (localChart hdim x o ho z).target := by
  have hq := PairedForestProductOverlap.toProduct_openConditions hdim x o ho (phase hdim x o ho z) z
  have he : (InteriorFaceDRCoordinates.datum (anchor_mem x o ho) (reference_mem x o ho)
      (anchor_global x o ho) (localChart hdim x o ho z z.val) hq).toInteriorCollisionData.boundaryPoint =
        PairedForestSimpleOverlap.facePoint hdim x o z := by
    exact (congrArg (fun D : SingleInteriorCluster 0 m (S x o ho) ↦ D.toInteriorCollisionData.boundaryPoint)
      (PairedForestProductOverlap.datum_toProduct hdim x o ho (phase hdim x o ho z) z)).trans
        (PairedForestSimpleOverlap.slice_insertion hdim x o ho z)
  obtain ⟨k, hk⟩ := eq_shift_of_boundaryPoint_eq (anchor_mem x o ho) (reference_mem x o ho)
    (reference_ne_anchor x o ho) (anchor_global x o ho) p
      (localChart hdim x o ho z z.val) hp hq (h.trans he.symm)
  exact ⟨k, localChart hdim x o ho z z.val,
    (localChart hdim x o ho z).map_source (self_mem_localChart_source hdim x o ho z), hk.symm⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.SimpleProductPhaseIdentification
