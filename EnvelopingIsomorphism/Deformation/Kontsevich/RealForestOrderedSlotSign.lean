import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceSwapSign
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeTransport
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomains

/-! The two actual scalar chamber signs for proper real faces with three
ordered boundary labels. Every complex coordinate moves in an even block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestOrderedSlotSign
open ClusterCoordinateOrder
open scoped Classical
section Generic
variable (C H : Type*) [Fintype C] [Fintype H]
abbrev PairLabels := C ⊕ H ⊕ Fin 2
abbrev N := Fintype.card C + (Fintype.card H + 2)
def scalarEnum : Fin 3 ⊕ Unit ≃ Fin 4 :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Unit)).trans finSumFinEquiv

@[simp] theorem scalarEnum_zero : scalarEnum (.inl 0) = 0 := rfl
@[simp] theorem scalarEnum_one : scalarEnum (.inl 1) = 1 := rfl
@[simp] theorem scalarEnum_two : scalarEnum (.inl 2) = 2 := rfl
@[simp] theorem scalarEnum_center : scalarEnum (.inr ()) = 3 := by
  apply Fin.ext
  change 3 + ((Fintype.equivFin Unit) ()).val = 3
  have h := ((Fintype.equivFin Unit) ()).isLt
  simp only [Fintype.card_unique] at h
  omega
@[simp] theorem scalarEnum_symm_zero : scalarEnum.symm 0 = .inl 0 := by
  rw [← scalarEnum_zero, Equiv.symm_apply_apply]
@[simp] theorem scalarEnum_symm_one : scalarEnum.symm 1 = .inl 1 := by
  rw [← scalarEnum_one, Equiv.symm_apply_apply]
@[simp] theorem scalarEnum_symm_two : scalarEnum.symm 2 = .inl 2 := by
  rw [← scalarEnum_two, Equiv.symm_apply_apply]
@[simp] theorem scalarEnum_symm_center : scalarEnum.symm 3 = .inr () := by
  rw [← scalarEnum_center, Equiv.symm_apply_apply]

def pairIndex : FaceIndex C H 3 ≃ PairLabels C H × Fin 2 where
  toFun
    | .inl ⟨c,k⟩ => (.inl c,k)
    | .inr (.inl ⟨h,k⟩) => (.inr (.inl h),k)
    | .inr (.inr j) => let p := finProdFinEquiv.symm (scalarEnum j); (.inr (.inr p.1),p.2)
  invFun
    | (.inl c,k) => .inl ⟨c,k⟩
    | (.inr (.inl h),k) => .inr (.inl ⟨h,k⟩)
    | (.inr (.inr j),k) => .inr (.inr (scalarEnum.symm (finProdFinEquiv (j,k))))
  left_inv j := by rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j <;> simp
  right_inv j := by rcases j with ⟨c|h|j,k⟩ <;> simp

def sourceLabels : PairLabels C H ≃ Fin (N C H) :=
  (Equiv.sumCongr (Fintype.equivFin C)
    ((Equiv.sumCongr (Fintype.equivFin H) (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

def splitLabels : PairLabels C H ≃ (H ⊕ Unit) ⊕ (C ⊕ Unit) where
  toFun
    | .inl c => .inr (.inl c)
    | .inr (.inl h) => .inl (.inl h)
    | .inr (.inr j) => if j=0 then .inl (.inr ()) else .inr (.inr ())
  invFun
    | .inl (.inl h) => .inr (.inl h)
    | .inr (.inl c) => .inl c
    | .inl (.inr _) => .inr (.inr 0)
    | .inr (.inr _) => .inr (.inr 1)
  left_inv j := by rcases j with c | h | j; rfl; rfl; fin_cases j <;> rfl
  right_inv j := by rcases j with (h|u) | (c|u) <;> simp

def targetLabels : PairLabels C H ≃ Fin (N C H) :=
  (splitLabels C H).trans
    (((Equiv.sumCongr
      ((Equiv.sumCongr (Fintype.equivFin H) (Fintype.equivFin Unit)).trans finSumFinEquiv)
      ((Equiv.sumCongr (Fintype.equivFin C) (Fintype.equivFin Unit)).trans finSumFinEquiv)).trans finSumFinEquiv).trans
      (finCongr (by simp [N]; omega)))

def pairEnum : FaceIndex C H 3 ≃ Fin (N C H * 2) :=
  (pairIndex C H).trans ((Equiv.prodCongr (sourceLabels C H) (Equiv.refl _)).trans finProdFinEquiv)
def orderedPairEnum : FaceIndex C H 3 ≃ Fin (N C H * 2) :=
  (pairIndex C H).trans ((Equiv.prodCongr (targetLabels C H) (Equiv.refl _)).trans finProdFinEquiv)

theorem sign_pair_order : Equiv.Perm.sign ((pairEnum C H).symm.trans (orderedPairEnum C H)) = 1 := by
  let p := (sourceLabels C H).symm.trans (targetLabels C H)
  have he : (pairEnum C H).symm.trans (orderedPairEnum C H) =
      finProdFinEquiv.permCongr (Equiv.prodCongr p (Equiv.refl (Fin 2))) := by
    ext j
    simp [pairEnum,orderedPairEnum,p,Equiv.permCongr_def]
  rw [he,Equiv.Perm.sign_permCongr]
  have hp : Equiv.prodCongr p (Equiv.refl (Fin 2)) = Equiv.prodCongrLeft (fun _ : Fin 2 => p) := by ext j <;> rfl
  rw [hp,Equiv.Perm.sign_prodCongrLeft,Fin.prod_univ_two]
  exact Int.units_mul_self _

theorem pairEnum_eq_faceEnum : pairEnum C H =
    (faceEnum C H 3).trans (finCongr (by dsimp [faceDimension,N]; omega)) := by
  ext j
  rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u
  · simp [pairEnum,pairIndex,sourceLabels,faceEnum,complexIndexEnum,finProdFinEquiv]
  · simp [pairEnum,pairIndex,sourceLabels,faceEnum,complexIndexEnum,finProdFinEquiv]
    omega
  · fin_cases j <;> simp [pairEnum,pairIndex,sourceLabels,faceEnum,scalarEnum,finProdFinEquiv] <;> omega
  · cases u
    simp [pairEnum,pairIndex,sourceLabels,faceEnum,scalarEnum,finProdFinEquiv]
    omega
def scalarAction (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (FaceIndex C H 3) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (scalarEnum.symm.permCongr σ))

theorem sign_scalarAction (σ : Equiv.Perm (Fin 4)) : Equiv.Perm.sign (scalarAction C H σ) = σ.sign := by
  simp [scalarAction,Equiv.Perm.sign_sumCongr]

theorem sign_scalar_then_pairs (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign ((pairEnum C H).symm.trans ((scalarAction C H σ).trans (orderedPairEnum C H))) = σ.sign := by
  have he : (pairEnum C H).symm.trans ((scalarAction C H σ).trans (orderedPairEnum C H)) =
      ((pairEnum C H).permCongr (scalarAction C H σ)).trans ((pairEnum C H).symm.trans (orderedPairEnum C H)) := by
    ext j
    simp [Equiv.permCongr_def]
  rw [he,Equiv.Perm.sign_trans,Equiv.Perm.sign_permCongr,sign_scalarAction,sign_pair_order]
  simp

def slotZero : Equiv.Perm (Fin 4) := Equiv.swap 2 3
def slotOne : Equiv.Perm (Fin 4) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
@[simp] theorem sign_slotZero : slotZero.sign = -1 := by simp [slotZero]
@[simp] theorem sign_slotOne : slotOne.sign = 1 := by simp [slotOne,Equiv.Perm.sign_trans]

end Generic
section Actual
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphNativeTransport
variable {n : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin 4}

def actualIndex (hlu : l ≤ u) : NativeFaceIndex i a S 3 ≃ Fin (D (i := i) (a := a) (S := S) (l := l) (u := u)) :=
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

theorem actual_inside_val (hlu : l ≤ u) (j : Fin 3) (hj : j ∈ boundaryClusterBlock l u) :
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

theorem actual_outside_val (hlu : l ≤ u) (j : Fin 3) (hj : j ∉ boundaryClusterBlock l u) :
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
theorem nativeDimension : D (i := i) (a := a) (S := S) (l := l) (u := u) =
    N (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) * 2 := by
  have hb := boundary_card_sum (l := l) (u := u)
  dsimp [D, shapeDegree, coarseDegree, GraphForms.dimension, N, coarseN, shapeN] at *
  omega

theorem nativeIndexEnum_eq_pairEnum :
    (nativeIndexEnum (i := i) (a := a) (S := S) (l := l) (u := u)).trans
      (finCongr nativeDimension) = pairEnum (BoundaryClusterCoarseIndex i S)
        (BoundaryClusterShapeIndex a S) := by
  rw [pairEnum_eq_faceEnum]
  rfl

theorem actual_slotZero :
    (actualIndex (i := i) (a := a) (S := S) (l := 0) (u := 2) (by decide)).trans
      (finCongr nativeDimension) =
    (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) slotZero).trans
      (orderedPairEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S)) := by
  ext j
  change (actualIndex (i := i) (a := a) (S := S) (l := 0) (u := 2) (by decide) j).val = _
  rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u
  · rw [actual_coarse_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
      finProdFinEquiv, shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 4) ≤ 2 by decide), shapeN, coarseEnum]
    omega
  · rw [actual_shape_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels, finProdFinEquiv, shapeEnum]
    omega
  · fin_cases j
    · rw [actual_inside_val _ _ (by decide)]
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotZero, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, Fin.divNat, Fin.modNat]
      omega
    · rw [actual_inside_val _ _ (by decide)]
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotZero, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, Fin.divNat, Fin.modNat]
      omega
    · rw [actual_outside_val _ _ (by decide)]
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotZero, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, coarseN, Fin.divNat, Fin.modNat,
        shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 4) ≤ 2 by decide),
        Fin.succAbove, outsideOrderedEnum_val (show (0 : Fin 4) ≤ 2 by decide), centerSlot]
      omega
  · cases u
    rw [actual_center_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
      finProdFinEquiv, slotZero, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, coarseN, Fin.divNat, Fin.modNat,
      shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (0 : Fin 4) ≤ 2 by decide)]
    omega

theorem actual_slotOne :
    (actualIndex (i := i) (a := a) (S := S) (l := 1) (u := 3) (by decide)).trans
      (finCongr nativeDimension) =
    (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) slotOne).trans
      (orderedPairEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S)) := by
  ext j
  change (actualIndex (i := i) (a := a) (S := S) (l := 1) (u := 3) (by decide) j).val = _
  rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u
  · rw [actual_coarse_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
      finProdFinEquiv, shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (1 : Fin 4) ≤ 3 by decide), shapeN, coarseEnum]
    omega
  · rw [actual_shape_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels, finProdFinEquiv, shapeEnum]
    omega
  · fin_cases j
    · rw [actual_outside_val _ _ (by decide)]
      have ho : outsideOrderedEnum (1 : Fin 4) 3 ⟨(0 : Fin 3), by decide⟩ =
          ⟨0, by rw [outsideM_eq_sub (show (1 : Fin 4) ≤ 3 by decide)]; decide⟩ := by
        apply Fin.ext
        simpa using outsideOrderedEnum_val (show (1 : Fin 4) ≤ 3 by decide) ⟨(0 : Fin 3), by decide⟩
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotOne, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, coarseN, Fin.divNat, Fin.modNat,
        shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (1 : Fin 4) ≤ 3 by decide),
        Fin.succAbove, ho, centerSlot]
      omega
    · rw [actual_inside_val _ _ (by decide)]
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotOne, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, Fin.divNat, Fin.modNat]
      omega
    · rw [actual_inside_val _ _ (by decide)]
      simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
        finProdFinEquiv, slotOne, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, Fin.divNat, Fin.modNat]
      omega
  · cases u
    rw [actual_center_val]
    simp [scalarAction, orderedPairEnum, pairIndex, targetLabels, splitLabels,
      finProdFinEquiv, slotOne, Equiv.swap_apply_def, Equiv.permCongr_def, shapeN, coarseN, Fin.divNat, Fin.modNat,
      shapeDegree, GraphForms.dimension, shapeM_eq_sub (show (1 : Fin 4) ≤ 3 by decide)]
    omega

theorem nativeOrderedPermutation_sign_of_actual (hlu : l ≤ u) (σ : Equiv.Perm (Fin 4))
    (he : (actualIndex (i := i) (a := a) (S := S) hlu).trans (finCongr nativeDimension) =
      (scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) σ).trans
        (orderedPairEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S))) :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) hlu).sign = σ.sign := by
  let e := finCongr (nativeDimension (i := i) (a := a) (S := S) (l := l) (u := u))
  have hd : e.permCongr (nativeOrderedPermutation hlu) =
      (pairEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S)).symm.trans
        ((scalarAction (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) σ).trans
          (orderedPairEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S))) := by
    rw [← he, ← nativeIndexEnum_eq_pairEnum (l := l) (u := u)]
    ext j
    rfl
  have hs := congrArg Equiv.Perm.sign hd
  rw [Equiv.Perm.sign_permCongr, sign_scalar_then_pairs] at hs
  exact hs

/-- The first actual boundary chamber has the odd scalar swap `2 ↔ center`. -/
theorem nativeOrderedPermutation_slotZero :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) (l := (0 : Fin 4)) (u := 2) (by decide)).sign = -1 := by
  rw [nativeOrderedPermutation_sign_of_actual _ slotZero actual_slotZero, sign_slotZero]

/-- The second actual boundary chamber has the even scalar cycle `(0 2 1)`. -/
theorem nativeOrderedPermutation_slotOne :
    (nativeOrderedPermutation (i := i) (a := a) (S := S) (l := (1 : Fin 4)) (u := 3) (by decide)).sign = 1 := by
  rw [nativeOrderedPermutation_sign_of_actual _ slotOne actual_slotOne, sign_slotOne]

end Actual

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestOrderedSlotSign
