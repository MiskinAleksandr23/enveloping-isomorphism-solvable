import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularPhasePullback

/-! Actual extended infinity edge forms are differences of angular forms of
the two retained full-DR pairs; outside targets give identical pair units. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceEdgeForms
open Configuration ComplexConjugate BoundaryAnchoredInfinityFreeCoordinates InfinityBoundaryFaceDR
open scoped Classical
variable {n m : ℕ} {a : Fin n} {o : Fin m} (l u : Fin (m+1))

def resolvedPair (p : DoubledPair n m) : FaceCoordinates a m o → ℂ :=
  StaticCollisionFaceDR.unit (boundaryAnchoredInfinityPairCollapses l u) (pairBase l u) (pairVelocity l u) p

theorem contDiff_resolvedPair (p : DoubledPair n m) : ContDiff ℝ ⊤ (resolvedPair (a := a) (o := o) l u p) := by
  unfold resolvedPair StaticCollisionFaceDR.unit
  split_ifs
  · exact (contDiff_velocity l u p.val.2).sub (contDiff_velocity l u p.val.1)
  · exact (contDiff_base l u p.val.2).sub (contDiff_base l u p.val.1)

theorem resolvedPair_ne_zero (p : DoubledPair n m) (y : FaceCoordinates a m o)
    (hy : (faceEmbedding y).OpenConditions l u) : resolvedPair l u p y ≠ 0 := by
  apply StaticCollisionFaceDR.unit_ne_zero
  · intro p
    rw [← datum_pairBase l u y hy]
    exact (faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p
  · intro p hp
    rw [← datum_pairVelocity l u y hy]
    exact (faceDomain y hy).datum.pairVelocity_ne_zero_of_pairBase_eq_zero p
      (((faceDomain y hy).datum.pairBase_eq_zero_iff_pairCollapses p).mpr hp)

def pairForm (p : DoubledPair n m) (y : FaceCoordinates a m o) := angularPullback (resolvedPair l u p) y

def edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (y : FaceCoordinates a m o) :=
  pairForm l u (harmonicNumeratorPair j v hv) y - pairForm l u (harmonicDenominatorPair j v) y

@[simp] theorem numerator_mask (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    boundaryAnchoredInfinityPairCollapses l u (harmonicNumeratorPair j v hv) ↔
      boundaryAnchoredInfinityCollapses l u (Sum.inl v) := by
  simp [boundaryAnchoredInfinityPairCollapses, boundaryAnchoredInfinityCollapses, harmonicNumeratorPair]

@[simp] theorem denominator_mask (j : Fin n) (v : Fin n ⊕ Fin m) :
    boundaryAnchoredInfinityPairCollapses l u (harmonicDenominatorPair j v) ↔
      boundaryAnchoredInfinityCollapses l u (Sum.inl v) := by
  simp [boundaryAnchoredInfinityPairCollapses, boundaryAnchoredInfinityCollapses, harmonicDenominatorPair]

theorem resolvedRatio_internal (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : boundaryAnchoredInfinityCollapses l u (Sum.inl v)) :
    (fun y : FaceCoordinates a m o ↦ resolvedPair l u (harmonicNumeratorPair j v hv) y /
      resolvedPair l u (harmonicDenominatorPair j v) y) =
      (fun q : ℂ × ℂ ↦ harmonicRatio q.1 q.2) ∘ shapeFacePair l u j v := by
  funext y
  simp only [resolvedPair, StaticCollisionFaceDR.unit, numerator_mask, denominator_mask, if_pos hc]
  cases v <;> rfl

theorem resolvedPair_outside (j : Fin n) (k : Fin m) (hk : k ∉ boundaryClusterBlock l u) :
    resolvedPair (a := a) (o := o) l u (harmonicNumeratorPair j (Sum.inr k) (by simp)) =
      resolvedPair l u (harmonicDenominatorPair j (Sum.inr k)) := by
  funext y
  simp only [resolvedPair, StaticCollisionFaceDR.unit, numerator_mask, denominator_mask]
  change (if k ∈ boundaryClusterBlock l u then _ else _) = (if k ∈ boundaryClusterBlock l u then _ else _)
  rw [if_neg hk, if_neg hk]
  rfl

theorem edgeForm_eq_extended_face (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    edgeForm l u j v hv y =
      (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding := by
  by_cases hc : boundaryAnchoredInfinityCollapses l u (Sum.inl v)
  · unfold edgeForm pairForm
    rw [← angularPullback_div _ _ y ((contDiff_resolvedPair l u _).contDiffAt.differentiableAt (by simp))
      ((contDiff_resolvedPair l u _).contDiffAt.differentiableAt (by simp))
      (resolvedPair_ne_zero l u _ y hy) (resolvedPair_ne_zero l u _ y hy),
      resolvedRatio_internal l u j v hv hc, extendedEdgeForm_face_internal y hy j v hc]
    exact (harmonicAngleForm_pullback _ y
      (((contDiff_shapePair l u j v).comp faceEmbedding.contDiff).contDiffAt.differentiableAt (by simp))
      ((faceDomain y hy).shape_denominator_ne_zero j v)).symm
  · cases v with
    | inl k => exact (hc trivial).elim
    | inr k =>
      rw [extendedEdgeForm_face_outside y hy j k hc]
      unfold edgeForm pairForm
      rw [resolvedPair_outside l u j k hc, sub_self]

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceEdgeForms
