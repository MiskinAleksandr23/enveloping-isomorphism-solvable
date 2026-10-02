import EnvelopingIsomorphism.Deformation.Kontsevich.StaticCollisionFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinitySmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityChart

/-! Smooth actual full-DR embedding of a scale-zero all-interior infinity
face, with the static collision mask and genuine primitive data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceDR
open Configuration ComplexConjugate BoundaryAnchoredInfinityFreeCoordinates
open scoped Classical
variable {n m : ℕ} {a : Fin n} {o : Fin m} (l u : Fin (m+1))

def base (y : FaceCoordinates a m o) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inr j) => (faceEmbedding y).boundaryBase l u j
  | _ => 0

def velocity (y : FaceCoordinates a m o) : DoubledLabel n m → ℂ
  | Sum.inl (Sum.inl j) => (faceEmbedding y).shape j
  | Sum.inl (Sum.inr j) => (faceEmbedding y).boundaryVelocity l u j
  | Sum.inr j => conj ((faceEmbedding y).shape j)

def pairBase (p : DoubledPair n m) (y : FaceCoordinates a m o) : ℂ := base l u y p.val.2 - base l u y p.val.1
def pairVelocity (p : DoubledPair n m) (y : FaceCoordinates a m o) : ℂ := velocity l u y p.val.2 - velocity l u y p.val.1

theorem contDiff_base (j : DoubledLabel n m) : ContDiff ℝ ⊤ (fun y : FaceCoordinates a m o ↦ base l u y j) := by
  rcases j with (j | j) | j
  · exact contDiff_const
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_boundaryBase l u j).comp faceEmbedding.contDiff)
  · exact contDiff_const

theorem contDiff_velocity (j : DoubledLabel n m) : ContDiff ℝ ⊤ (fun y : FaceCoordinates a m o ↦ velocity l u y j) := by
  rcases j with (j | j) | j
  · exact (contDiff_shape j).comp faceEmbedding.contDiff
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_boundaryVelocity l u j).comp faceEmbedding.contDiff)
  · exact Complex.conjCLE.contDiff.comp ((contDiff_shape j).comp faceEmbedding.contDiff)

def ambient : FaceCoordinates a m o → CompactDRCoordinates.Ambient n m :=
  StaticCollisionFaceDR.ambient (boundaryAnchoredInfinityPairCollapses l u) (pairBase l u) (pairVelocity l u)

variable (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u)

theorem datum_pairBase (p : DoubledPair n m) : (faceDomain y hy).datum.pairBase p = pairBase l u p y := by
  have h (j : DoubledLabel n m) : (faceDomain y hy).datum.doubledBase j = base l u y j := by
    rcases j with (j | j) | j
    · rfl
    · exact congrArg Complex.ofReal ((faceDomain y hy).datum_boundaryBase j)
    · rfl
  exact congrArg₂ (· - ·) (h p.val.2) (h p.val.1)

theorem datum_pairVelocity (p : DoubledPair n m) : (faceDomain y hy).datum.pairVelocity p = pairVelocity l u p y := by
  have h (j : DoubledLabel n m) : (faceDomain y hy).datum.doubledVelocity j = velocity l u y j := by
    rcases j with (j | j) | j
    · exact (faceDomain y hy).datum_shape j
    · exact congrArg Complex.ofReal ((faceDomain y hy).datum_boundaryVelocity j)
    · exact congrArg conj ((faceDomain y hy).datum_shape j)
  exact congrArg₂ (· - ·) (h p.val.2) (h p.val.1)

include hy in
theorem contDiffAt_ambient : ContDiffAt ℝ ⊤ (ambient (a := a) (o := o) l u) y := by
  apply StaticCollisionFaceDR.contDiffAt_ambient
  · intro p
    rw [← datum_pairBase l u y hy]
    exact (faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p
  · intro p hp
    rw [← datum_pairVelocity l u y hy]
    exact (faceDomain y hy).datum.pairVelocity_ne_zero_of_pairBase_eq_zero p
      (((faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p).mpr hp)
  · intro p
    exact ((contDiff_base l u p.val.2).sub (contDiff_base l u p.val.1)).contDiffAt
  · intro p
    exact ((contDiff_velocity l u p.val.2).sub (contDiff_velocity l u p.val.1)).contDiffAt

theorem ambient_eq_data : ambient l u y =
    CompactDRCoordinates.dataEmbedding (projectDR (faceDomain y hy).toDomain.insertion.val) := by
  rw [ambient, StaticCollisionFaceDR.ambient_eq_limits]
  · change _ = CompactDRCoordinates.dataEmbedding
      (projectDR (((faceDomain y hy).datum).compactInsertion _).val)
    rw [BoundaryAnchoredInfinityData.compactInsertion_projectDR]
    change _ = CompactDRCoordinates.dataEmbedding ((faceDomain y hy).datum.resolvedDR 0)
    rw [BoundaryAnchoredInfinityData.resolvedDR_zero]
    apply Prod.ext
    · funext p
      simp only [← datum_pairBase l u y hy, ← datum_pairVelocity l u y hy]
      rfl
    · funext t
      simp only [← datum_pairBase l u y hy, ← datum_pairVelocity l u y hy]
      rfl
  · intro p
    rw [← datum_pairBase l u y hy]
    exact (faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p
  · intro p hp
    rw [← datum_pairVelocity l u y hy]
    exact (faceDomain y hy).datum.pairVelocity_ne_zero_of_pairBase_eq_zero p
      (((faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p).mpr hp)

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceDR
