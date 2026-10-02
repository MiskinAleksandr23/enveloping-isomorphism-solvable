import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestOrderedSlotSign

/-! Actual mixed-real boundary frame orientation for two boundary labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedRealForestOrderedSlotSign
open ClusterCoordinateOrder BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphNativeTransport
open scoped Classical
section Values
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m+1)}

def actualIndex (hlu : l ≤ u) : NativeFaceIndex i a S m ≃ Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  nativeIndexToBlock.trans (blockBoundaryPermutation hlu)

theorem block_apply (hlu : l ≤ u) (j : Fin (shapeDegree a S l u) ⊕ Fin (coarseDegree i S l u)) :
    blockBoundaryPermutation hlu (finSumFinEquiv j) = finSumFinEquiv
      (Equiv.sumCongr (boundaryTangentPermutation (shapeN a S) (shapePermutation l u))
        (boundaryTangentPermutation (coarseN i S) (coarsePermutation hlu)) j) := by
  change finSumFinEquiv ((Equiv.sumCongr
    (boundaryTangentPermutation (shapeN a S) (shapePermutation l u))
    (boundaryTangentPermutation (coarseN i S) (coarsePermutation hlu)))
    (finSumFinEquiv.symm (finSumFinEquiv j))) = _
  rw [Equiv.symm_apply_apply]

theorem actual_coarse_val (hlu : l ≤ u) (c : BoundaryClusterCoarseIndex i S) (k : Fin 2) :
    (actualIndex (a := a) hlu (.inl ⟨c,k⟩)).val = shapeDegree a S l u + (coarseEnum c).val * 2 + k.val := by
  change (blockBoundaryPermutation hlu (finSumFinEquiv (.inr
    (GraphForms.coordinateIndexEquiv _ _ (.inl (coarseEnum c,k)))))).val = _
  rw [block_apply]
  change (finSumFinEquiv (.inr (boundaryTangentPermutation _ _
    (GraphForms.coordinateIndexEquiv _ _ (.inl (coarseEnum c,k)))))).val = _
  rw [boundaryTangentPermutation_index]
  simp [GraphForms.coordinateIndexEquiv,finProdFinEquiv,shapeDegree,shapeM]
  omega

theorem actual_shape_val (hlu : l ≤ u) (h : BoundaryClusterShapeIndex a S) (k : Fin 2) :
    (actualIndex (i := i) hlu (.inr (.inl ⟨h,k⟩))).val = (shapeEnum h).val * 2 + k.val := by
  change (blockBoundaryPermutation hlu (finSumFinEquiv (.inl
    (GraphForms.coordinateIndexEquiv _ _ (.inl (shapeEnum h,k)))))).val = _
  rw [block_apply]
  change (finSumFinEquiv (.inl (boundaryTangentPermutation _ _
    (GraphForms.coordinateIndexEquiv _ _ (.inl (shapeEnum h,k)))))).val = _
  rw [boundaryTangentPermutation_index]
  simp [GraphForms.coordinateIndexEquiv,finProdFinEquiv]
  omega

theorem actual_inside_val (hlu : l ≤ u) (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) :
    (actualIndex (i := i) (a := a) (S := S) hlu (.inr (.inr (.inl j)))).val =
      shapeN a S * 2 + (j.val-l.val) := by
  have hs : nativeIndexSplit (i := i) (a := a) (S := S) (l := l) (u := u)
      (.inr (.inr (.inl j))) = .inl (.inr (shapeBoundaryEnum ⟨j,hj⟩)) := by
    change dite _ _ _ = _
    rw [dif_pos hj]
  change (blockBoundaryPermutation hlu (finSumFinEquiv
    (Equiv.sumCongr _ _ (nativeIndexSplit (.inr (.inr (.inl j))))))).val = _
  rw [hs, block_apply]
  change (finSumFinEquiv (.inl (boundaryTangentPermutation _ _
    (GraphForms.coordinateIndexEquiv _ _ (.inr (shapeBoundaryEnum ⟨j,hj⟩)))))).val = _
  rw [boundaryTangentPermutation_index]
  change (finSumFinEquiv (.inl (GraphForms.coordinateIndexEquiv _ _
    (.inr (shapePermutation l u (shapeBoundaryEnum ⟨j,hj⟩)))))).val = _
  rw [shapePermutation_native]
  simp [GraphForms.coordinateIndexEquiv,shapeOrderedEnum_val hlu]

theorem actual_outside_val (hlu : l ≤ u) (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) :
    (actualIndex (i := i) (a := a) (S := S) hlu (.inr (.inr (.inl j)))).val =
      shapeDegree a S l u + coarseN i S * 2 +
        ((centerSlot hlu).succAbove (outsideOrderedEnum l u ⟨j,hj⟩)).val := by
  have hs : nativeIndexSplit (i := i) (a := a) (S := S) (l := l) (u := u)
      (.inr (.inr (.inl j))) = .inr (.inr (Fin.succ (outsideBoundaryEnum ⟨j,hj⟩))) := by
    change dite _ _ _ = _
    rw [dif_neg hj]
  change (blockBoundaryPermutation hlu (finSumFinEquiv
    (Equiv.sumCongr _ _ (nativeIndexSplit (.inr (.inr (.inl j))))))).val = _
  rw [hs, block_apply]
  change (finSumFinEquiv (.inr (boundaryTangentPermutation _ _
    (GraphForms.coordinateIndexEquiv _ _ (.inr (Fin.succ (outsideBoundaryEnum ⟨j,hj⟩))))))).val = _
  rw [boundaryTangentPermutation_index]
  change (finSumFinEquiv (.inr (GraphForms.coordinateIndexEquiv _ _
    (.inr (coarsePermutation hlu (Fin.succ (outsideBoundaryEnum ⟨j,hj⟩))))))).val = _
  rw [coarsePermutation_outside]
  simp [GraphForms.coordinateIndexEquiv,shapeDegree,shapeM]
  omega

theorem actual_center_val (hlu : l ≤ u) :
    (actualIndex (i := i) (a := a) (S := S) hlu (.inr (.inr (.inr ())))).val =
      shapeDegree a S l u + coarseN i S * 2 + l.val := by
  change (blockBoundaryPermutation hlu (finSumFinEquiv (.inr
    (GraphForms.coordinateIndexEquiv _ _ (.inr 0))))).val = _
  rw [block_apply]
  change (finSumFinEquiv (.inr (boundaryTangentPermutation _ _
    (GraphForms.coordinateIndexEquiv _ _ (.inr 0))))).val = _
  rw [boundaryTangentPermutation_index]
  change (finSumFinEquiv (.inr (GraphForms.coordinateIndexEquiv _ _
    (.inr (coarsePermutation hlu 0))))).val = _
  rw [coarsePermutation_center]
  simp [GraphForms.coordinateIndexEquiv,shapeDegree,shapeM]
  omega

end Values

section Generic
variable (C H : Type*) [Fintype C] [Fintype H]

def scalarEnum : Fin 2 ⊕ Unit ≃ Fin 3 :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Unit)).trans finSumFinEquiv

@[simp] theorem scalarEnum_zero : scalarEnum (.inl 0) = 0 := rfl
@[simp] theorem scalarEnum_one : scalarEnum (.inl 1) = 1 := rfl
@[simp] theorem scalarEnum_center : scalarEnum (.inr ()) = 2 := by
  apply Fin.ext
  change 2 + ((Fintype.equivFin Unit) ()).val = 2
  have h := ((Fintype.equivFin Unit) ()).isLt
  simp only [Fintype.card_unique] at h
  omega

@[simp] theorem scalarEnum_symm_zero : scalarEnum.symm 0 = .inl 0 := by
  rw [← scalarEnum_zero, Equiv.symm_apply_apply]
@[simp] theorem scalarEnum_symm_one : scalarEnum.symm 1 = .inl 1 := by
  rw [← scalarEnum_one, Equiv.symm_apply_apply]
@[simp] theorem scalarEnum_symm_center : scalarEnum.symm 2 = .inr () := by
  rw [← scalarEnum_center, Equiv.symm_apply_apply]

def scalarAction (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (FaceIndex C H 2) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (scalarEnum.symm.permCongr σ))

theorem sign_scalarAction (σ : Equiv.Perm (Fin 3)) :
    (scalarAction C H σ).sign = σ.sign := by
  simp [scalarAction, Equiv.Perm.sign_sumCongr]

def tailSplit (c k : ℕ) (hk : k ≤ 3) : Fin (c*2+3) ≃ Fin (c*2+k) ⊕ Fin (3-k) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

def tailShift (c k : ℕ) (hk : k ≤ 3) : Equiv.Perm (Fin (c*2+3)) :=
  (tailSplit c k hk).symm.permCongr
    (Equiv.sumCongr ((finRotate (c*2+k))^k) (Equiv.refl _))

theorem sign_tailShift_one (c : ℕ) : (tailShift c 1 (by omega)).sign = 1 := by
  simp [tailShift, Equiv.Perm.sign_sumCongr, sign_finRotate, pow_mul]

theorem sign_tailShift_two (c : ℕ) : (tailShift c 2 (by omega)).sign = 1 := by
  simp [tailShift, Equiv.Perm.sign_sumCongr, map_pow, pow_two, Int.units_mul_self]

def prefixSplit : Fin (faceDimension H C 2) ≃
    Fin (Fintype.card H * 2) ⊕ Fin (Fintype.card C * 2 + 3) :=
  (finCongr (by dsimp [faceDimension])).trans finSumFinEquiv.symm

def insertScalars (k : ℕ) (hk : k ≤ 3) : Equiv.Perm (Fin (faceDimension H C 2)) :=
  (prefixSplit C H).symm.permCongr
    (Equiv.sumCongr (Equiv.refl _) (tailShift (Fintype.card C) k hk))

theorem sign_insertScalars (k : ℕ) (hk : k ≤ 3) (h : k = 1 ∨ k = 2) :
    (insertScalars C H k hk).sign = 1 := by
  simp only [insertScalars, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_refl, one_mul]
  rcases h with rfl | rfl
  · exact sign_tailShift_one _
  · exact sign_tailShift_two _

def orderedEnum (k : ℕ) (hk : k ≤ 3) : FaceIndex C H 2 ≃ Fin (faceDimension H C 2) :=
  (ClusterFaceBasisSign.faceSwap C H 2).trans
    ((faceEnum H C 2).trans (insertScalars C H k hk))

theorem sign_orderedEnum (k : ℕ) (hk : k ≤ 3) (h : k = 1 ∨ k = 2)
    (σ : Equiv.Perm (Fin 3)) :
    Equiv.Perm.sign (((faceEnum C H 2).trans (finCongr (ClusterFaceBasisSign.faceDimension_swap C H 2))).symm.trans
      ((scalarAction C H σ).trans (orderedEnum C H k hk))) = σ.sign := by
  let f := (faceEnum C H 2).trans (finCongr (ClusterFaceBasisSign.faceDimension_swap C H 2))
  let g := (ClusterFaceBasisSign.faceSwap C H 2).trans (faceEnum H C 2)
  have hs : Equiv.Perm.sign (f.symm.trans g) = 1 := by
    have he : f.symm.trans g = f.permCongr (ClusterFaceBasisSign.faceSwapPermutation C H 2).symm := by
      ext j
      simp [f, g, ClusterFaceBasisSign.faceSwapPermutation, Equiv.permCongr_def]
    rw [he, Equiv.Perm.sign_permCongr]
    change Equiv.Perm.sign ((ClusterFaceBasisSign.faceSwapPermutation C H 2)⁻¹) = 1
    rw [map_inv, ClusterFaceBasisSign.sign_face_swap_blocks, inv_one]
  have he : f.symm.trans ((scalarAction C H σ).trans (orderedEnum C H k hk)) =
      (f.permCongr (scalarAction C H σ)).trans ((f.symm.trans g).trans (insertScalars C H k hk)) := by
    ext j
    simp [f, g, orderedEnum, Equiv.permCongr_def]
  change Equiv.Perm.sign (f.symm.trans _) = _
  rw [he, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr,
    sign_scalarAction, hs, sign_insertScalars C H k hk h]
  simp

end Generic

theorem tailShift_val (c k : ℕ) (hk : k ≤ 3) (j : Fin (c*2+3)) :
    (tailShift c k hk j).val = if h : j.val < c*2+k then
      (((finRotate (c*2+k))^k) ⟨j.val,h⟩).val else j.val := by
  split_ifs with h
  · have he : j = (tailSplit c k hk).symm (.inl ⟨j.val,h⟩) := by
      apply Fin.ext
      simp [tailSplit]
    conv_lhs => rw [he]
    simp only [tailShift, Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl]
    simp [tailSplit]
  · have he : j = (tailSplit c k hk).symm (.inr ⟨j.val-(c*2+k),by omega⟩) := by
      apply Fin.ext
      simp [tailSplit]
      omega
    conv_lhs => rw [he]
    simp only [tailShift, Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]
    simp [tailSplit]
    omega

theorem tailShift_one_val (c : ℕ) (j : Fin (c*2+3)) :
    (tailShift c 1 (by omega) j).val =
      if j.val < c*2 then j.val+1 else if j.val = c*2 then 0 else j.val := by
  rw [tailShift_val]
  simp only [pow_one, coe_finRotate, Fin.ext_iff, Fin.val_last]
  split_ifs <;> omega

theorem tailShift_two_val (c : ℕ) (j : Fin (c*2+3)) :
    (tailShift c 2 (by omega) j).val =
      if j.val < c*2 then j.val+2 else if j.val < c*2+2 then j.val-c*2 else j.val := by
  rw [tailShift_val]
  by_cases h : j.val < c*2+2
  · rw [dif_pos h]
    rw [ClusterFaceBasisSign.rotate_two_val]
    simp only [Fin.val_mk]
    split_ifs <;> omega
  · rw [dif_neg h]
    split_ifs <;> omega

section GenericValues
variable (C H : Type*) [Fintype C] [Fintype H]

theorem insertScalars_prefix (k : ℕ) (hk : k ≤ 3) (j : Fin (faceDimension H C 2))
    (hj : j.val < Fintype.card H * 2) : (insertScalars C H k hk j).val = j.val := by
  have he : j = (prefixSplit C H).symm (.inl ⟨j.val,hj⟩) := by
    apply Fin.ext
    simp [prefixSplit]
  conv_lhs => rw [he]
  simp only [insertScalars, Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
  simp [prefixSplit]

theorem insertScalars_tail (k : ℕ) (hk : k ≤ 3) (j : Fin (faceDimension H C 2))
    (t : Fin (Fintype.card C*2+3)) (hj : j.val = Fintype.card H*2+t.val) :
    (insertScalars C H k hk j).val = Fintype.card H*2+(tailShift (Fintype.card C) k hk t).val := by
  have he : j = (prefixSplit C H).symm (.inr t) := by
    apply Fin.ext
    simpa [prefixSplit] using hj
  rw [he]
  simp [insertScalars, Equiv.permCongr_def, prefixSplit]

theorem orderedEnum_shape_val (k : ℕ) (hk : k ≤ 3) (h : H) (j : Fin 2) :
    (orderedEnum C H k hk (.inr (.inl ⟨h,j⟩))).val = (Fintype.equivFin H h).val*2+j.val := by
  change (insertScalars C H k hk (faceEnum H C 2 (.inl ⟨h,j⟩))).val = _
  rw [insertScalars_prefix]
  · simp [faceEnum, complexIndexEnum, finProdFinEquiv]
    omega
  · have hh := (Fintype.equivFin H h).isLt
    have hj := j.isLt
    simp [faceEnum, complexIndexEnum, finProdFinEquiv]
    omega

theorem orderedEnum_coarse_val (k : ℕ) (hk : k ≤ 3) (hk' : k = 1 ∨ k = 2) (c : C) (j : Fin 2) :
    (orderedEnum C H k hk (.inl ⟨c,j⟩)).val = Fintype.card H*2+k+(Fintype.equivFin C c).val*2+j.val := by
  have hc := (Fintype.equivFin C c).isLt
  have hj := j.isLt
  change (insertScalars C H k hk (faceEnum H C 2 (.inr (.inl ⟨c,j⟩)))).val = _
  rw [insertScalars_tail C H k hk _ ⟨(Fintype.equivFin C c).val*2+j.val,by omega⟩
    (by simp [faceEnum, complexIndexEnum, finProdFinEquiv]; omega)]
  rcases hk' with rfl | rfl
  · rw [tailShift_one_val]
    simp only [Fin.val_mk, if_pos (show (Fintype.equivFin C c).val*2+j.val < Fintype.card C*2 by omega)]
    omega
  · rw [tailShift_two_val]
    simp only [Fin.val_mk, if_pos (show (Fintype.equivFin C c).val*2+j.val < Fintype.card C*2 by omega)]
    omega

theorem orderedEnum_scalar_val (k : ℕ) (hk : k ≤ 3) (j : Fin 2 ⊕ Unit) :
    (orderedEnum C H k hk (.inr (.inr j))).val = Fintype.card H*2+
      (tailShift (Fintype.card C) k hk ⟨Fintype.card C*2+(scalarEnum j).val,by have := (scalarEnum j).isLt; omega⟩).val := by
  change (insertScalars C H k hk (faceEnum H C 2 (.inr (.inr j)))).val = _
  apply insertScalars_tail
  rcases j with j | u
  · simp [faceEnum, scalarEnum]
  · cases u
    simp [faceEnum, scalarEnum]

end GenericValues

section Actual
variable {n : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin 3}

theorem nativeDimension : D (i := i) (a := a) (S := S) (l := l) (u := u) =
    faceDimension (BoundaryClusterShapeIndex a S) (BoundaryClusterCoarseIndex i S) 2 := by
  have hb := boundary_card_sum (l := l) (u := u)
  dsimp [D, shapeDegree, coarseDegree, GraphForms.dimension, faceDimension, coarseN, shapeN] at *
  omega

theorem nativeIndexEnum_cast :
    (nativeIndexEnum (i := i) (a := a) (S := S) (l := l) (u := u)).trans (finCongr nativeDimension) =
      (faceEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) 2).trans
        (finCongr (ClusterFaceBasisSign.faceDimension_swap _ _ 2)) := by
  ext j
  rfl

theorem nativeOrderedPermutation_sign_of_actual (hlu : l ≤ u) (k : ℕ) (hk : k ≤ 3)
    (hk' : k = 1 ∨ k = 2) (σ : Equiv.Perm (Fin 3))
    (he : (actualIndex (i := i) (a := a) (S := S) hlu).trans (finCongr nativeDimension) =
      (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) σ).trans
        (orderedEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) k hk)) :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) hlu).sign = σ.sign := by
  let e := finCongr (nativeDimension (i := i) (a := a) (S := S) (l := l) (u := u))
  have hd : e.permCongr (nativeOrderedPermutation hlu) =
      ((faceEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) 2).trans
        (finCongr (ClusterFaceBasisSign.faceDimension_swap _ _ 2))).symm.trans
        ((scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) σ).trans
          (orderedEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) k hk)) := by
    rw [← he, ← nativeIndexEnum_cast (l := l) (u := u)]
    ext j
    rfl
  have hs := congrArg Equiv.Perm.sign hd
  rw [Equiv.Perm.sign_permCongr, sign_orderedEnum _ _ k hk hk' σ] at hs
  exact hs

theorem actual_slotZero :
    (actualIndex (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 1) (by decide)).trans
      (finCongr nativeDimension) =
    (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) (Equiv.swap 1 2)).trans
      (orderedEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) 1 (by decide)) := by
  ext j
  change (actualIndex (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 1) (by decide) j).val = _
  rcases j with ⟨c,j⟩ | ⟨h,j⟩ | j | u
  · rw [actual_coarse_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_coarse_val _ _ 1 _ (Or.inl rfl)]
    simp [shapeDegree, GraphForms.dimension, shapeN, coarseEnum, shapeM_eq_sub (show (0 : Fin 3) ≤ 1 by decide)]
  · rw [actual_shape_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_shape_val]
  · fin_cases j
    · rw [actual_inside_val _ _ (by decide)]
      simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
      rw [orderedEnum_scalar_val, tailShift_one_val]
      simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN]
    · rw [actual_outside_val _ _ (by decide)]
      simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
      rw [orderedEnum_scalar_val, tailShift_one_val]
      simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN, coarseN,
        shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 3) ≤ 1 by decide),
        Fin.succAbove, outsideOrderedEnum_val (show (0 : Fin 3) ≤ 1 by decide), centerSlot]
      omega
  · cases u
    rw [actual_center_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
    rw [orderedEnum_scalar_val, tailShift_one_val]
    simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN, coarseN,
      shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 3) ≤ 1 by decide)]
    omega

theorem actual_slotOne :
    (actualIndex (i := i) (a := a) (S := S) (l := (1 : Fin 3)) (u := 2) (by decide)).trans
      (finCongr nativeDimension) =
    (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) (Equiv.swap 0 1)).trans
      (orderedEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) 1 (by decide)) := by
  ext j
  change (actualIndex (i := i) (a := a) (S := S) (l := (1 : Fin 3)) (u := 2) (by decide) j).val = _
  rcases j with ⟨c,j⟩ | ⟨h,j⟩ | j | u
  · rw [actual_coarse_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_coarse_val _ _ 1 _ (Or.inl rfl)]
    simp [shapeDegree, GraphForms.dimension, shapeN, coarseEnum, shapeM_eq_sub (show (1 : Fin 3) ≤ 2 by decide)]
  · rw [actual_shape_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_shape_val]
  · fin_cases j
    · rw [actual_outside_val _ _ (by decide)]
      have ho : outsideOrderedEnum (1 : Fin 3) 2 ⟨(0 : Fin 2), by decide⟩ =
          ⟨0, by rw [outsideM_eq_sub (show (1 : Fin 3) ≤ 2 by decide)]; decide⟩ := by
        apply Fin.ext
        simpa using outsideOrderedEnum_val (show (1 : Fin 3) ≤ 2 by decide) ⟨(0 : Fin 2), by decide⟩
      simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
      rw [orderedEnum_scalar_val, tailShift_one_val]
      simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN, coarseN,
        shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (1 : Fin 3) ≤ 2 by decide),
        Fin.succAbove, ho, centerSlot]
      omega
    · rw [actual_inside_val _ _ (by decide)]
      simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
      rw [orderedEnum_scalar_val, tailShift_one_val]
      simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN]
  · cases u
    rw [actual_center_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
    rw [orderedEnum_scalar_val, tailShift_one_val]
    simp [Equiv.permCongr_def, Equiv.swap_apply_def, shapeN, coarseN,
      shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (1 : Fin 3) ≤ 2 by decide)]
    omega

theorem actual_fullBlock :
    (actualIndex (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 2) (by decide)).trans
      (finCongr nativeDimension) =
    (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) (Equiv.refl _)).trans
      (orderedEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) 2 (by decide)) := by
  ext j
  change (actualIndex (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 2) (by decide) j).val = _
  rcases j with ⟨c,j⟩ | ⟨h,j⟩ | j | u
  · rw [actual_coarse_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_coarse_val _ _ 2 _ (Or.inr rfl)]
    simp [shapeDegree, GraphForms.dimension, shapeN, coarseEnum, shapeM_eq_sub (show (0 : Fin 3) ≤ 2 by decide)]
  · rw [actual_shape_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Equiv.refl_apply]
    rw [orderedEnum_shape_val]
  · fin_cases j <;> rw [actual_inside_val _ _ (by decide)] <;>
      simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr] <;>
      rw [orderedEnum_scalar_val, tailShift_two_val] <;>
      simp [Equiv.permCongr_def, shapeN]
  · cases u
    rw [actual_center_val]
    simp only [Equiv.trans_apply, scalarAction, Equiv.sumCongr_apply, Sum.map_inr]
    rw [orderedEnum_scalar_val, tailShift_two_val]
    simp [Equiv.permCongr_def, shapeN, coarseN,
      shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 3) ≤ 2 by decide)]
    omega

/-- Vector inside the first single-boundary block: swap b1 and center. -/
theorem nativeOrderedPermutation_slotZero :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 1) (by decide)).sign = -1 := by
  rw [nativeOrderedPermutation_sign_of_actual _ 1 _ (Or.inl rfl) (Equiv.swap 1 2) actual_slotZero]
  decide

/-- Vector inside the second single-boundary block: swap b0 and b1. -/
theorem nativeOrderedPermutation_slotOne :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) (l := (1 : Fin 3)) (u := 2) (by decide)).sign = -1 := by
  rw [nativeOrderedPermutation_sign_of_actual _ 1 _ (Or.inl rfl) (Equiv.swap 0 1) actual_slotOne]
  decide

/-- Vector outside the full two-boundary block: the scalar order is unchanged. -/
theorem nativeOrderedPermutation_fullBlock :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) (l := (0 : Fin 3)) (u := 2) (by decide)).sign = 1 := by
  rw [nativeOrderedPermutation_sign_of_actual _ 2 _ (Or.inr rfl) (Equiv.refl _) actual_fullBlock]
  rfl

end Actual
end EnvelopingIsomorphism.Deformation.Kontsevich.MixedRealForestOrderedSlotSign
