import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestCoorientation

/-! Evaluation of the remaining explicit pure physical extraction determinant.
The ordered quotient deletes exactly the right endpoint boundary coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestCoorientation
open Configuration ForestRadialFaceClassification BoxStokes
open PureForestSimpleCluster (lower upper)
open BoundaryGraphOrderedCoordinates BoundaryGraphFaceFactorization
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin m)
  (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)

def boundaryAxis (j : Fin m) : Fin (r+1) :=
  finCongr hdim (GraphForms.externalBasisIndex n j)

@[simp] theorem boundaryAxis_val (j : Fin m) : (boundaryAxis hdim j).val = n*2 + j.val := by
  simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv]

private theorem native_coordinate (y : Coord (r+1)) (j : Fin (GraphForms.dimension n m)) :
    GraphForms.realCoordinates n m ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y) j =
      y (finCongr hdim j) := by
  have h := ForestGlobalGraphStokes.coordinateCast_apply hdim
    (GraphForms.realCoordinates n m ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y)) j
  change ForestGlobalGraphStokes.nativeCoordinates hdim
    ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y) (finCongr hdim j) = _ at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

include hcard in
private theorem block_length : (upper x o).val - (lower x o).val = 2 := by
  have h := shapeM_eq_sub (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o))
  have hc : shapeM (lower x o) (upper x o) = 2 := by
    simpa only [shapeM, Fintype.card_coe] using hcard
  rw [hc] at h
  exact h.symm

private theorem face_coordinate (p : GraphForms.Coordinates n m)
    (j : Fin (PureBoundaryGraphIntegral.Degree (n := n) (l := lower x o) (u := upper x o))) :
    PureForestFaceChangeVariables.simpleCoordinates hdim x o a b ho hl hu hab hcard (physicalFace x o a b p)
      (finCongr (PureForestFaceChangeVariables.dimension_eq hdim x o a b ho hl hu hab hcard) j) =
    GraphForms.realCoordinates n (outsideM (lower x o) (upper x o) + 1)
      (PureBoundaryGraphQuotient.orderedCoarseCoordinates
        (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o))
          (p.1, p.2 a, fun k ↦ p.2 k.val)) j := by
  unfold PureForestFaceChangeVariables.simpleCoordinates
  rw [ContinuousLinearEquiv.trans_apply, ForestGlobalGraphStokes.coordinateCast_apply]
  rfl

include ho hl hu hab hcard in
theorem extraction_zero (y : Coord (r+1)) :
    extraction hdim x o a b ho hl hu hab hcard y 0 = y (boundaryAxis hdim b) - y (boundaryAxis hdim a) := by
  change ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 b -
    ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 a = _
  rw [← GraphForms.realCoordinates_external _ b, ← GraphForms.realCoordinates_external _ a,
    native_coordinate, native_coordinate]
  rfl

include ho hl hu hab hcard in
theorem extraction_succ (y : Coord (r+1)) (j : Fin r) :
    extraction hdim x o a b ho hl hu hab hcard y j.succ = y ((boundaryAxis hdim b).succAbove j) := by
  let hd := PureForestFaceChangeVariables.dimension_eq hdim x o a b ho hl hu hab hcard
  obtain ⟨j,rfl⟩ := (finCongr hd).surjective j
  change PureForestFaceChangeVariables.simpleCoordinates hdim x o a b ho hl hu hab hcard
    (physicalFace x o a b ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y)) (finCongr hd j) = _
  rw [face_coordinate hdim x o a b ho hl hu hab hcard]
  obtain ⟨j,rfl⟩ := (GraphForms.coordinateIndexEquiv n (outsideM (lower x o) (upper x o)+1)).surjective j
  rcases j with ⟨i,k⟩ | j
  · rw [GraphForms.realCoordinates_internal]
    have hi : (boundaryAxis hdim b).succAbove
        (finCongr hd (GraphForms.coordinateIndexEquiv n (outsideM (lower x o) (upper x o)+1) (Sum.inl (i,k)))) =
      finCongr hdim (GraphForms.coordinateIndexEquiv n m (Sum.inl (i,k))) := by
      apply Fin.ext
      have hi := i.isLt
      have hk := k.isLt
      simp only [Fin.succAbove]
      simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv, hd, finProdFinEquiv]
      split_ifs <;> simp_all only [Fin.lt_def, Fin.val_cast, Fin.val_natAdd, Fin.val_castSucc, Fin.val_succ, centerSlot_val, ite_false, ite_true, lower, upper] <;> omega
    rw [hi, ← native_coordinate hdim y (GraphForms.coordinateIndexEquiv n m (Sum.inl (i,k))), GraphForms.realCoordinates_internal]
    rfl
  · change GraphForms.realCoordinates _ _ _ (GraphForms.externalBasisIndex n j) = _
    rw [GraphForms.realCoordinates_external]
    let hlu := ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)
    cases j using (centerSlot hlu).succAboveCases with
    | x =>
      rw [PureBoundaryGraphDomain.orderedCoarseCoordinates_center]
      have hi : (boundaryAxis hdim b).succAbove
          (finCongr hd (GraphForms.coordinateIndexEquiv n (outsideM (lower x o) (upper x o)+1) (Sum.inr (centerSlot hlu)))) =
        boundaryAxis hdim a := by
        apply Fin.ext
        have hab' : a.val < b.val := hab
        simp only [Fin.succAbove]
        simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv, hd, centerSlot_val, hlu]
        split_ifs <;> simp_all only [Fin.lt_def, Fin.val_cast, Fin.val_natAdd, Fin.val_castSucc, Fin.val_succ, centerSlot_val, ite_false, ite_true, lower, upper]
        all_goals
          have hsame : (lower x o).val = (ForestRadialClusterLabels.blockLower 0 x (RealForestCoarsePositions.node x o)).val := rfl
          first | contradiction | omega
      rw [hi]
      change ((ForestGlobalGraphStokes.nativeCoordinates hdim).symm y).2 a = y (finCongr hdim (GraphForms.externalBasisIndex n a))
      rw [← native_coordinate hdim y (GraphForms.externalBasisIndex n a), GraphForms.realCoordinates_external]
    | p j =>
      rw [PureBoundaryGraphDomain.orderedCoarseCoordinates_outside]
      have hj := outsideOrderedEnum_symm_val hlu j
      have hg := block_length x o hcard
      have hb : b.val = a.val + 1 := by
        have hlu' : (lower x o).val ≤ (upper x o).val := hlu
        omega
      have hi : (boundaryAxis hdim b).succAbove
          (finCongr hd (GraphForms.coordinateIndexEquiv n (outsideM (lower x o) (upper x o)+1)
            (Sum.inr ((centerSlot hlu).succAbove j)))) =
        boundaryAxis hdim ((outsideOrderedEnum (lower x o) (upper x o)).symm j).val := by
        apply Fin.ext
        simp only [Fin.succAbove]
        simp [boundaryAxis, GraphForms.externalBasisIndex, GraphForms.coordinateIndexEquiv, hd, centerSlot_val, hlu]
        rw [hj]
        split_ifs <;> simp_all only [Fin.lt_def, Fin.val_cast, Fin.val_natAdd, Fin.val_castSucc, Fin.val_succ, centerSlot_val, ite_false, ite_true, lower, upper]
        all_goals
          have hsame : (lower x o).val = (ForestRadialClusterLabels.blockLower 0 x (RealForestCoarsePositions.node x o)).val := rfl
          first | contradiction | omega
      rw [hi]
      change _ = y (finCongr hdim (GraphForms.externalBasisIndex n _))
      rw [← native_coordinate hdim y (GraphForms.externalBasisIndex n _), GraphForms.realCoordinates_external]

private theorem det_slotDifference {r : ℕ} (D : Coord (r+1) →L[ℝ] Coord (r+1))
    (A B : Fin (r+1)) (hAB : A ≠ B)
    (hzero : ∀ y, D y 0 = y B - y A)
    (hsucc : ∀ y j, D y j.succ = y (B.succAbove j)) :
    D.det = (-1 : ℝ)^B.val := by
  let M := LinearMap.toMatrix' D.toLinearMap
  have hM : M.det = D.det := LinearMap.det_toMatrix' _
  have hzero' : M 0 B = 1 := by
    change D (Pi.single B 1) 0 = 1
    rw [hzero]
    simp [Pi.single_apply, hAB, Ne.symm hAB]
  have hsucc' (j : Fin r) : M j.succ B = 0 := by
    change D (Pi.single B 1) j.succ = 0
    rw [hsucc]
    simp [Pi.single_apply, Fin.succAbove_ne]
  have hminor : M.submatrix (0 : Fin (r+1)).succAbove B.succAbove = 1 := by
    ext i j
    change D (Pi.single (B.succAbove j) 1) ((0 : Fin (r+1)).succAbove i) = _
    rw [Fin.succAbove_zero, hsucc]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [← hM, Matrix.det_succ_column M B, Finset.sum_eq_single 0]
  · rw [hzero', hminor]
    simp
  · intro i hi hni
    cases i using Fin.cases with
    | zero => exact (hni rfl).elim
    | succ j => rw [hsucc']; simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

include ho hl hu hab hcard in
/-- The concrete physical extraction has precisely the boundary-endpoint
permutation sign; its shear contributes determinant one. -/
theorem extraction_det : (extraction hdim x o a b ho hl hu hab hcard).det = (-1 : ℝ)^b.val := by
  have hab' : boundaryAxis hdim a ≠ boundaryAxis hdim b := by
    intro he
    have he' := congrArg Fin.val he
    simp only [boundaryAxis_val] at he'
    exact hab.ne (Fin.ext (by omega))
  rw [det_slotDifference _ (boundaryAxis hdim a) (boundaryAxis hdim b) hab'
    (extraction_zero hdim x o a b ho hl hu hab hcard)
    (extraction_succ hdim x o a b ho hl hu hab hcard), boundaryAxis_val, pow_add]
  have hn : (-1 : ℝ)^(n*2) = 1 := by rw [mul_comm n 2, pow_mul]; norm_num
  rw [hn, one_mul]

include ho hl hu hab hcard in
/-- The original chart certificate now gives the literal scalar slot sign,
with no determinant or new orientation hypothesis left over. -/
theorem native_face_orientation_slot (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |OrientedFormChangeVariables.jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val =
      (-1 : ℝ)^a.val * |PureForestFaceChangeVariables.jacobian hdim x o a b ho hl hu hab hcard z.val| := by
  have h := native_face_orientation hdim x o a b ho hl hu hab hcard z hz ε hε
  rw [extraction_det hdim x o a b ho hl hu hab hcard] at h
  have hg := block_length x o hcard
  have hlu := ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)
  have hb : b.val = a.val + 1 := by omega
  simpa only [abs_pow, abs_neg, abs_one, one_pow, div_one, hb, pow_succ, mul_neg_one,
    neg_neg] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestCoorientation
