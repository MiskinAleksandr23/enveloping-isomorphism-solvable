import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceDR
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularPhasePullback

/-! The actual simple real-face edge form is the difference of the angular
forms of its two retained doubled-pair directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceEdgeForms
open Configuration ComplexConjugate BoundaryClusterFaceDR BoundaryClusterFreeCoordinates
open scoped Classical
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} (l u : Fin (m+1))

def resolvedPair (p : DoubledPair n m) (y : FaceCoordinates i a S m) : ℂ :=
  if boundaryClusterPairCollapses S l u p then pairVelocity l u p y else pairBase l u p y

theorem contDiff_resolvedPair (p : DoubledPair n m) :
    ContDiff ℝ ⊤ (resolvedPair (i := i) (a := a) (S := S) l u p) := by
  unfold resolvedPair
  split_ifs
  · exact contDiff_pairVelocity l u p
  · exact contDiff_pairBase l u p

theorem resolvedPair_ne_zero (p : DoubledPair n m) (y : FaceCoordinates i a S m)
    (hy : (faceEmbedding y).OpenConditions l u) : resolvedPair l u p y ≠ 0 := by
  unfold resolvedPair
  split_ifs with hp
  · exact pairVelocity_ne_zero l u y hy p hp
  · exact mt (pairBase_eq_zero_iff l u y hy p).mp hp

theorem direction_eq_phase (p : DoubledPair n m) (y : FaceCoordinates i a S m) :
    BoundaryClusterFaceDR.direction l u p y = (complexPhase (resolvedPair l u p y) : ℂ) := by
  unfold BoundaryClusterFaceDR.direction resolvedPair
  split_ifs <;> rfl

def pairForm (p : DoubledPair n m) (y : FaceCoordinates i a S m) :
    FaceCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ := angularPullback (resolvedPair l u p) y

def edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (y : FaceCoordinates i a S m) :
    FaceCoordinates i a S m [⋀^Fin 1]→L[ℝ] ℝ :=
  pairForm l u (harmonicNumeratorPair j v hv) y - pairForm l u (harmonicDenominatorPair j v) y

@[simp] theorem numerator_mask (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    boundaryClusterPairCollapses S l u (harmonicNumeratorPair j v hv) ↔
      j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v) := Iff.rfl

@[simp] theorem denominator_mask (j : Fin n) (v : Fin n ⊕ Fin m) :
    boundaryClusterPairCollapses S l u (harmonicDenominatorPair j v) ↔
      j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v) := Iff.rfl

theorem resolvedRatio_internal (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)) :
    (fun y : FaceCoordinates i a S m ↦ resolvedPair l u (harmonicNumeratorPair j v hv) y /
      resolvedPair l u (harmonicDenominatorPair j v) y) =
      (fun q : ℂ × ℂ ↦ harmonicRatio q.1 q.2) ∘ shapeFacePair l u j v := by
  funext y
  simp only [resolvedPair, numerator_mask, denominator_mask, if_pos hc]
  cases v <;> rfl

theorem resolvedRatio_external (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (hc : ¬(j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v))) :
    (fun y : FaceCoordinates i a S m ↦ resolvedPair l u (harmonicNumeratorPair j v hv) y /
      resolvedPair l u (harmonicDenominatorPair j v) y) =
      (fun q : ℂ × ℂ ↦ harmonicRatio q.1 q.2) ∘ coarseFacePair l u j v := by
  funext y
  simp only [resolvedPair, numerator_mask, denominator_mask, if_neg hc]
  cases v <;> rfl

/-- All numerator, reflected denominator, and normalization derivatives are
retained in the actual restricted extended graph form. -/
theorem edgeForm_eq_extended_face (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (y : FaceCoordinates i a S m) (hy : (faceEmbedding y).OpenConditions l u) :
    edgeForm l u j v hv y =
      (extendedEdgeForm l u j v (faceEmbedding y)).compContinuousLinearMap faceEmbedding := by
  unfold edgeForm pairForm
  rw [← angularPullback_div _ _ y ((contDiff_resolvedPair l u _).contDiffAt.differentiableAt (by simp))
    ((contDiff_resolvedPair l u _).contDiffAt.differentiableAt (by simp))
    (resolvedPair_ne_zero l u _ y hy) (resolvedPair_ne_zero l u _ y hy)]
  by_cases hc : j ∈ S ∧ boundaryClusterCollapses S l u (Sum.inl v)
  · rw [resolvedRatio_internal l u j v hv hc, extendedEdgeForm_face_internal y hy j v hc.1 hc.2]
    exact (harmonicAngleForm_pullback _ y ((contDiff_shapeFacePair l u j v).contDiffAt.differentiableAt (by simp))
      ((faceDomain y hy).shape_denominator_ne_zero j v hc.1)).symm
  · rw [resolvedRatio_external l u j v hv hc, extendedEdgeForm_face_external y hy j v hv hc]
    exact (harmonicAngleForm_pullback _ y ((contDiff_coarseFacePair l u j v).contDiffAt.differentiableAt (by simp))
      ((faceDomain y hy).external_denominator_ne_zero j v hv hc)).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceEdgeForms
