import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSmoothProduct
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleOverlap

/-! Exact actual native face to coarse/planar product overlap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductOverlap
open Configuration PairedForestSimpleCluster PairedForestSmoothProduct InteriorGraphFaceCoordinates
open ForestRadialFaceClassification BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)
  (u : Circle) (z : Source hdim x o)

theorem toFree_eq_slice : (toAngular (toProduct hdim x o ho u z.val)).toFree =
    (slice hdim x o ho z).freeCoordinates := by
  apply Prod.ext
  · funext j
    change rawBase hdim x o (coarseEnum.symm (coarseEnum j)).val (facePoint hdim x o z) = _
    rw [Equiv.symm_apply_apply]
    exact rawBase_eq hdim x o ho z j.val
  · apply Prod.ext
    · funext j
      change circleParameter (angle hdim x o ho u (facePoint hdim x o z)) *
        (rawVelocity hdim x o ho (shapeEnum.symm (shapeEnum j)).val (facePoint hdim x o z) /
          rawVelocity hdim x o ho (reference x o ho) (facePoint hdim x o z)) = _
      rw [Equiv.symm_apply_apply, circleParameter_angle]
      have hn : rawVelocity hdim x o ho (reference x o ho) (facePoint hdim x o z) ≠ 0 :=
        (phase hdim x o ho z).coe_ne_zero
      exact (mul_div_cancel₀ _ hn).trans (rawVelocity_eq hdim x o ho z j.val)
    · apply Prod.ext
      · funext j
        exact rawBoundary_eq hdim x o ho z j
      · apply Prod.ext
        · apply Circle.ext
          change (Circle.exp (angle hdim x o ho u (facePoint hdim x o z)) : ℂ) = _
          rw [← circleParameter_eq, circleParameter_angle]
          exact rawVelocity_eq hdim x o ho z (reference x o ho)
        · rfl

theorem toProduct_openConditions : (toAngular (toProduct hdim x o ho u z.val)).toFree.OpenConditions := by
  rw [toFree_eq_slice]
  exact (slice hdim x o ho z).freeCoordinates_openConditions (anchor_mem x o ho)

theorem datum_toProduct : InteriorFaceDRCoordinates.datum
    (anchor_mem x o ho) (reference_mem x o ho) (anchor_global x o ho)
    (toProduct hdim x o ho u z.val) (toProduct_openConditions hdim x o ho u z) =
      PairedForestSimpleCluster.datum hdim x o ho z := by
  apply SingleInteriorCluster.isEmbedding_parameterCoordinates.injective
  rw [InteriorFaceDRCoordinates.datum, ClusterFreeDomain.datum_parameters]
  change (toAngular (toProduct hdim x o ho u z.val)).toFree.parameters = _
  rw [toFree_eq_slice, NormalizedInteriorClusterSlice.freeCoordinates_parameters _ (anchor_mem x o ho)]
  rfl

/-- Equality of the actual ambient DR maps on the whole strict native source. -/
theorem ambient_toProduct : InteriorFaceDRCoordinates.ambient (toProduct hdim x o ho u z.val) =
    ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [InteriorFaceDRCoordinates.ambient_eq_boundaryPoint
    (anchor_mem x o ho) (reference_mem x o ho) (anchor_global x o ho)
    _ (toProduct_openConditions hdim x o ho u z), datum_toProduct]
  have he := PairedForestSimpleOverlap.slice_insertion hdim x o ho z
  change (PairedForestSimpleCluster.datum hdim x o ho z).toInteriorCollisionData.boundaryPoint = _ at he
  rw [he, ForestRadialFaceImmersion.forward_data]
  rfl

/-- An explicit inverse built from the actual native finite scalar DR decoder. -/
def inverse (p : Product x o ho) : Coord r :=
  ForestRadialFaceImmersion.inverse hdim x o (InteriorFaceDRCoordinates.ambient p)

theorem inverse_toProduct : inverse hdim x o ho (toProduct hdim x o ho u z.val) = z.val := by
  rw [inverse, ambient_toProduct]
  exact ForestRadialFaceImmersion.inverse_forward hdim x o z

theorem contDiffAt_inverse : ContDiffAt ℝ ⊤ (inverse hdim x o ho) (toProduct hdim x o ho u z.val) := by
  have hi := ForestRadialFaceImmersion.contDiffAt_inverse hdim x o z
  rw [← ambient_toProduct hdim x o ho u z] at hi
  exact hi.comp _ (InteriorFaceDRCoordinates.contDiffAt_ambient
    (anchor_mem x o ho) (reference_mem x o ho) (anchor_global x o ho)
    _ (toProduct_openConditions hdim x o ho u z))

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductOverlap
