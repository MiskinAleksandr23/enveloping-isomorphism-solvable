import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.FixedAnchorPermutation

/-! The infinity extraction is a boundary-axis permutation followed by an
even permutation of complex coordinate pairs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
open Configuration ForestRadialFaceClassification BoxStokes
open InfinityForestSimpleCluster (lower upper)
open BoundaryGraphOrderedCoordinates BoundaryGraphFaceFactorization
open scoped Classical
variable {n m r : ℕ}

private theorem shape_count (n : ℕ) : InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1)) = n := by
  simp [InfinityBoundaryGraphFactorization.shapeN, card_boundaryAnchoredInfinityFreeInterior]

private def freeInteriorEquiv (n : ℕ) : BoundaryAnchoredInfinityFreeInterior (0 : Fin (n+1)) ≃ Fin n where
  toFun j := j.val.pred j.property
  invFun j := ⟨j.succ, Fin.succ_ne_zero j⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv j := by simp

private def interiorPermutation (n : ℕ) : Equiv.Perm (Fin n) :=
  (finCongr (shape_count n).symm).trans
    ((InfinityBoundaryGraphFactorization.interiorEnum (a := (0 : Fin (n+1)))).symm.trans (freeInteriorEquiv n))

private theorem interiorPermutation_apply
    (j : Fin (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1)))) :
    interiorPermutation n (finCongr (shape_count n) j) =
      ((InfinityBoundaryGraphFactorization.interiorEnum (a := (0 : Fin (n+1)))).symm j).val.pred
        ((InfinityBoundaryGraphFactorization.interiorEnum (a := (0 : Fin (n+1)))).symm j).property := by
  simp [interiorPermutation, freeInteriorEquiv]

variable (hdim : GraphForms.dimension n m = r+1)

def boundaryAxis (q : Fin m) : Fin (r+1) := finCongr hdim (GraphForms.externalBasisIndex n q)

@[simp] theorem boundaryAxis_val (q : Fin m) : (boundaryAxis hdim q).val = n*2+q.val := by
  simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv]

private def sourcePermutation : Equiv.Perm (Fin (r+1)) :=
  (finCongr hdim).permCongr (GraphForms.fixedAnchorCoordinatePerm (m := m) (interiorPermutation n))

private theorem sourcePermutation_sign : (sourcePermutation hdim).sign = 1 := by
  rw [sourcePermutation, Equiv.Perm.sign_permCongr, GraphForms.sign_fixedAnchorCoordinatePerm]

private def reorder : Coord (r+1) ≃L[ℝ] Coord (r+1) where
  toFun y := fun j ↦ y (sourcePermutation hdim j)
  invFun y := fun j ↦ y ((sourcePermutation hdim).symm j)
  left_inv y := by funext j; simp
  right_inv y := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_apply _

private theorem reorder_det : (reorder hdim).toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (reorder hdim).toLinearMap =
      (1 : Matrix (Fin (r+1)) (Fin (r+1)) ℝ).submatrix (sourcePermutation hdim) id := by
    ext i j
    simp [reorder, LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hm, Matrix.det_permute, sourcePermutation_sign]
  simp

private theorem native_coordinate (y : Coord (r+1)) (j : Fin (GraphForms.dimension n m)) :
    GraphForms.realCoordinates n m ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y) j = y (finCongr hdim j) := by
  have h := ForestGlobalGraphStokes.coordinateCast_apply hdim
    (GraphForms.realCoordinates n m ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y)) j
  change ForestGlobalGraphStokes.nativeCoordinates hdim
    ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y) (finCongr hdim j) = _ at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

private theorem reorder_internal (y : Coord (r+1)) (i : Fin n) (k : Fin 2) :
    reorder hdim y (finCongr hdim (GraphForms.coordinateIndexEquiv n m (Sum.inl (i,k)))) =
      y (finCongr hdim (GraphForms.coordinateIndexEquiv n m (Sum.inl (interiorPermutation n i,k)))) := by
  simp [reorder, sourcePermutation, GraphForms.fixedAnchorCoordinatePerm, Equiv.permCongr_def]

private theorem reorder_external (y : Coord (r+1)) (j : Fin m) :
    reorder hdim y (boundaryAxis hdim j) = y (boundaryAxis hdim j) := by
  simp [reorder, sourcePermutation, boundaryAxis, GraphForms.externalBasisIndex,
    GraphForms.fixedAnchorCoordinatePerm, Equiv.permCongr_def]

private def slotExtraction (Q : Fin (r+1)) : Coord (r+1) →L[ℝ] Coord (r+1) :=
  ContinuousLinearMap.pi fun j ↦ Fin.cases (ContinuousLinearMap.proj Q)
    (fun k ↦ ContinuousLinearMap.proj (Q.succAbove k)) j

private theorem slotExtraction_det (Q : Fin (r+1)) : (slotExtraction Q).det = (-1 : ℝ)^Q.val := by
  have hn (v : Coord (r+1)) : slotExtraction Q v 0 = 1 * v Q := by simp [slotExtraction]
  rw [RadialFaceJacobian.det_eq_normal_mul_face Q 0 _ 1 hn]
  have he : RadialFaceJacobian.faceDerivative Q 0 (slotExtraction Q) = ContinuousLinearMap.id ℝ (Coord r) := by
    ext v j
    simp [RadialFaceJacobian.faceDerivative, ForestRadialFaceImmersion.faceProjection,
      slotExtraction, faceTangent, Fin.succAbove_zero, faceEmbedding]
  rw [he]
  simp only [Fin.val_zero, Nat.zero_add, mul_one]
  change _ * LinearMap.det (LinearMap.id : Coord r →ₗ[ℝ] Coord r) = _
  rw [LinearMap.det_id, mul_one]

variable (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

include hq hall in
private theorem block_shape_count : shapeM (lower x o) (upper x o) = m-1 := by
  have he : boundaryClusterBlock (lower x o) (upper x o) = Finset.univ.erase q := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun hj he ↦ hq (he ▸ hj), hall j⟩
  simp [shapeM, he]

include hq hall in
private theorem orderedBoundary_val (j : Fin (shapeM (lower x o) (upper x o))) :
    ((shapeOrderedEnum (lower x o) (upper x o)).symm j).val.val =
      if j.val < q.val then j.val else j.val+1 := by
  let hlu := ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)
  rw [shapeOrderedEnum_symm_val hlu]
  have hc := block_shape_count x o q hq hall
  rw [shapeM_eq_sub hlu] at hc
  change (upper x o).val - (lower x o).val = m-1 at hc
  change (lower x o).val + j.val = if j.val < q.val then j.val else j.val+1
  have hj : j.val < m-1 := by simpa only [block_shape_count x o q hq hall] using j.isLt
  have hu := (upper x o).isLt
  have hqv := q.isLt
  have hn := hq
  simp only [mem_boundaryClusterBlock] at hn
  have hlu' : (lower x o).val ≤ (upper x o).val := hlu
  split_ifs <;> omega

private theorem face_coordinate (p : GraphForms.Coordinates n m)
    (j : Fin (InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) (lower x o) (upper x o))) :
    InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall (physicalFace x o q p)
      (finCongr (InfinityForestFaceChangeVariables.dimension_eq hdim x o q ho hq hne hall) j) =
    GraphForms.realCoordinates (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1))) (shapeM (lower x o) (upper x o))
      ((fun k ↦ p.1 (((InfinityBoundaryGraphFactorization.interiorEnum (a := (0 : Fin (n+1)))).symm k).val.pred
        ((InfinityBoundaryGraphFactorization.interiorEnum (a := (0 : Fin (n+1)))).symm k).property)),
       fun k ↦ p.2 ((shapeOrderedEnum (lower x o) (upper x o)).symm k).val) j := by
  unfold InfinityForestFaceChangeVariables.simpleCoordinates
  rw [ContinuousLinearEquiv.trans_apply, ForestGlobalGraphStokes.coordinateCast_apply]
  rfl

include ho hq hne hall in
theorem linearExtraction_zero (y : Coord (r+1)) :
    linearExtraction hdim x o q ho hq hne hall y 0 = reorder hdim y (boundaryAxis hdim q) := by
  rw [reorder_external]
  change ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 q = _
  rw [← GraphForms.realCoordinates_external _ q, native_coordinate]
  rfl

include ho hq hne hall in
theorem linearExtraction_succ (y : Coord (r+1)) (j : Fin r) :
    linearExtraction hdim x o q ho hq hne hall y j.succ = reorder hdim y ((boundaryAxis hdim q).succAbove j) := by
  let hd := InfinityForestFaceChangeVariables.dimension_eq hdim x o q ho hq hne hall
  obtain ⟨j,rfl⟩ := (finCongr hd).surjective j
  change InfinityForestFaceChangeVariables.simpleCoordinates hdim x o q ho hq hne hall
    (physicalFace x o q ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y)) (finCongr hd j) = _
  rw [face_coordinate hdim x o q ho hq hne hall]
  obtain ⟨j,rfl⟩ := (GraphForms.coordinateIndexEquiv
    (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1))) (shapeM (lower x o) (upper x o))).surjective j
  rcases j with ⟨i,k⟩ | j
  · rw [GraphForms.realCoordinates_internal]
    have hi : (boundaryAxis hdim q).succAbove
        (finCongr hd (GraphForms.coordinateIndexEquiv
          (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1))) (shapeM (lower x o) (upper x o)) (Sum.inl (i,k)))) =
      finCongr hdim (GraphForms.coordinateIndexEquiv n m (Sum.inl (finCongr (shape_count n) i,k))) := by
      apply Fin.ext
      have hi : i.val < n := by simpa only [shape_count n] using i.isLt
      have hk := k.isLt
      simp only [Fin.succAbove]
      simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv, finProdFinEquiv]
      split_ifs <;> simp_all only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ] <;> omega
    rw [hi, reorder_internal, interiorPermutation_apply, ← native_coordinate hdim y _,
      GraphForms.realCoordinates_internal]
  · change GraphForms.realCoordinates _ _ _ (GraphForms.externalBasisIndex _ j) = _
    rw [GraphForms.realCoordinates_external]
    have hv := orderedBoundary_val x o q hq hall j
    have hi : (boundaryAxis hdim q).succAbove
        (finCongr hd (GraphForms.coordinateIndexEquiv
          (InfinityBoundaryGraphFactorization.shapeN (0 : Fin (n+1))) (shapeM (lower x o) (upper x o)) (Sum.inr j))) =
      boundaryAxis hdim ((shapeOrderedEnum (lower x o) (upper x o)).symm j).val := by
      apply Fin.ext
      simp only [Fin.succAbove]
      simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv]
      rw [hv]
      split_ifs <;> simp_all only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ, shape_count] <;> omega
    rw [hi, reorder_external]
    change _ = y (finCongr hdim (GraphForms.externalBasisIndex n _))
    rw [← native_coordinate hdim y (GraphForms.externalBasisIndex n _), GraphForms.realCoordinates_external]

include ho hq hne hall in
/-- Moving the single outside boundary label to radius slot zero gives its
ordinary coordinate sign; all complex block permutations are even. -/
theorem linearExtraction_det : (linearExtraction hdim x o q ho hq hne hall).det = (-1 : ℝ)^q.val := by
  have he : linearExtraction hdim x o q ho hq hne hall =
      (slotExtraction (boundaryAxis hdim q)).comp (reorder hdim).toContinuousLinearMap := by
    ext y j
    cases j using Fin.cases with
    | zero => exact linearExtraction_zero hdim x o q ho hq hne hall y
    | succ j => exact linearExtraction_succ hdim x o q ho hq hne hall y j
  rw [he]
  change LinearMap.det ((slotExtraction (boundaryAxis hdim q)).toLinearMap.comp (reorder hdim).toLinearMap) = _
  rw [LinearMap.det_comp, reorder_det, mul_one]
  change (slotExtraction (boundaryAxis hdim q)).det = _
  rw [slotExtraction_det, boundaryAxis_val, pow_add]
  have hn : (-1 : ℝ)^(n*2) = 1 := by rw [mul_comm n 2, pow_mul]; norm_num
  rw [hn, one_mul]

include ho hq hne hall in
theorem linearExtraction_sign : (SignType.sign (linearExtraction hdim x o q ho hq hne hall).det : ℝ) = (-1 : ℝ)^q.val := by
  rw [linearExtraction_det hdim x o q ho hq hne hall]
  rcases neg_one_pow_eq_or (ℝ) q.val with h | h <;> rw [h] <;> norm_num

include ho hq hne hall in
theorem native_face_orientation_slot (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ)^(axis hdim x o).val)) *
      InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val =
      (BoundaryAnchoredInfinityData.referenceSign (lower x o) q * (-1 : ℝ)^q.val) *
        |InfinityForestFaceChangeVariables.jacobian hdim x o q ho hq hne hall z.val| :=
  (native_face_orientation_slot_iff hdim x o q ho hq hne hall z hz ε hε).mpr
    (linearExtraction_sign hdim x o q ho hq hne hall)

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestPhysicalExtraction
