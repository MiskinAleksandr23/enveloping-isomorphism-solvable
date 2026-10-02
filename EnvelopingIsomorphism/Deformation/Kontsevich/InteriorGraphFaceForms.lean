import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates

/-! Each actual simple interior-face edge factors through its genuine planar
or contracted coarse coordinate map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ClusterAngularCoordinates ContinuousAlternatingMap
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

private theorem form_comp_assoc {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ω : E [⋀^Fin 1]→L[ℝ] ℝ) (L : F →L[ℝ] E) (M : G →L[ℝ] F) :
    (ω.compContinuousLinearMap L).compContinuousLinearMap M =
      ω.compContinuousLinearMap (L.comp M) := rfl

/-- Every external edge has exactly the contracted harmonic coarse factor.
The result allows incoming and outgoing edges and arbitrary cluster size. -/
theorem actualEdgeForm_product (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (e : Edge n m) :
    (actualEdgeForm e.1 e.2 (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) =
      (GraphForms.edgeForm (coarseEdge e) x.2).compContinuousLinearMap
        (ContinuousLinearMap.snd ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)) := by
  rw [actualEdgeForm_eq_pullback _ hx (by simp) _ _, form_comp_assoc]
  have hcomp : actualPair (i := i) (a := a) (b := b) (S := S) e.1 e.2 ∘ toAngular =
      GraphForms.edgeMap (coarseEdge e) ∘ Prod.snd := funext (fun y ↦ actualPair_toAngular y e)
  rw [← fderiv_comp x ((contDiff_actualPair e.1 e.2).differentiable (by simp)).differentiableAt
    (contDiff_toAngular.differentiable (by simp)).differentiableAt, hcomp]
  have hd := ((GraphForms.hasFDerivAt_edgeMap (coarseEdge e) x.2).comp x
    (ContinuousLinearMap.snd ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)).hasFDerivAt).fderiv
  rw [hd, actualPair_toAngular]
  rfl

def internalFaceMap (j k : Fin n) (x : ProductCoordinates i a b S m) : VariableClusterFace :=
  ((toAngular x).toFree.base j, ((toAngular x).toFree.velocity j, (toAngular x).toFree.velocity k))

theorem contDiff_internalFaceMap (j k : Fin n) :
    ContDiff ℝ ⊤ (internalFaceMap (i := i) (a := a) (b := b) (S := S) (m := m) j k) :=
  ((contDiff_base j).comp contDiff_toAngular).prodMk
    (((contDiff_velocity j).comp contDiff_toAngular).prodMk ((contDiff_velocity k).comp contDiff_toAngular))

theorem internalParameters_toAngular (j k : Fin n) :
    internalParameters (i := i) (a := a) (b := b) (S := S) (m := m) j k ∘ toAngular =
      variableClusterFaceEmbedding ∘ internalFaceMap j k := rfl

/-- The internal edge is the exact planar angular factor, independent of coarse coordinates. -/
theorem internalEdgeForm_product (hba : b ≠ a) (x : ProductCoordinates i a b S m)
    (hx : (toAngular x).toFree.OpenConditions) (j k : Fin n)
    (hj : j ∈ S) (hk : k ∈ S) (hkj : k ≠ j) :
    (internalEdgeForm j k (toAngular x)).compContinuousLinearMap (fderiv ℝ toAngular x) =
      (rotatedEdgeForm (shapeLabel j hj) (shapeLabel k hk) x.1).compContinuousLinearMap
        (ContinuousLinearMap.fst ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)) := by
  have hD := internalDenominator_face_ne_zero (toAngular x) hx (radius_toAngular x) j k
  have hC := ((contDiffAt_variableInternalClusterRegularizedRatio _ hD).differentiableAt (by simp))
  rw [internalEdgeForm, internalRatio,
    angularPullback_comp_differentiable _ _ _ hC
      ((contDiff_internalParameters j k).differentiable (by simp)).differentiableAt,
    form_comp_assoc]
  rw [← fderiv_comp x ((contDiff_internalParameters j k).differentiable (by simp)).differentiableAt
    (contDiff_toAngular.differentiable (by simp)).differentiableAt,
    internalParameters_toAngular]
  have hDF := (variableClusterFaceEmbedding.hasFDerivAt.comp x
    ((contDiff_internalFaceMap j k).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  rw [hDF]
  change ((variableInternalClusterExtendedForm
      (variableClusterFaceEmbedding (internalFaceMap j k x))).compContinuousLinearMap
        (variableClusterFaceEmbedding.comp (fderiv ℝ (internalFaceMap j k) x))) = _
  rw [← form_comp_assoc,
    variableInternalClusterExtendedForm_face _ (hx.1.2.1 j)
      (velocityDifference_ne_zero (toAngular x) hx j k hj hk hkj), form_comp_assoc]
  have hdiff : variableClusterDifference ∘ internalFaceMap (i := i) (a := a) (b := b) (m := m) j k =
      rotatedDifference (shapeLabel j hj) (shapeLabel k hk) ∘ Prod.fst := by
    funext y
    change (toAngular y).toFree.velocity k - (toAngular y).toFree.velocity j = _
    rw [velocity_toAngular hba y k hk, velocity_toAngular hba y j hj]
    rfl
  have hdif := (variableClusterDifference.hasFDerivAt.comp x
    ((contDiff_internalFaceMap j k).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  rw [← hdif, hdiff]
  have hdrot := ((hasFDerivAt_rotatedDifference (shapeLabel j hj) (shapeLabel k hk) x.1).comp x
    (ContinuousLinearMap.fst ℝ (ShapeCoordinates a b S) (CoarseCoordinates i a S m)).hasFDerivAt).fderiv
  rw [hdrot]
  have hv : (internalFaceMap j k x).2.2 - (internalFaceMap j k x).2.1 =
      rotatedDifference (shapeLabel j hj) (shapeLabel k hk) x.1 := congrFun hdiff x
  rw [hv]
  unfold rotatedEdgeForm
  rw [fderiv_rotatedDifference]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
