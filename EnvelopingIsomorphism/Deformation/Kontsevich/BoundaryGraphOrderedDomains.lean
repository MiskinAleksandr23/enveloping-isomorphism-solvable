import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates

/-! Ordered physical shape/coarse configurations and anchor-preserving cluster index maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
open Configuration BoundaryGraphFaceFactorization
open scoped BigOperators Classical
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem shapeOrderedEnum_symm_val (hlu : l ≤ u) (j : Fin (shapeM l u)) :
    ((shapeOrderedEnum l u).symm j).val.val = l.val + j.val := by
  let f : Fin (shapeM l u) → Fin m := fun j ↦
    ((blockOffsetEquiv hlu).symm (Fin.cast (shapeM_eq_sub hlu) j)).val
  have hf := Finset.orderEmbOfFin_unique
    (show (boundaryClusterBlock l u).card = shapeM l u from (Fintype.card_coe _).symm)
    (f := f) (fun j ↦ ((blockOffsetEquiv hlu).symm (Fin.cast (shapeM_eq_sub hlu) j)).property)
    (by intro j k hjk; change l.val + j.val < l.val + k.val; exact Nat.add_lt_add_left hjk _)
  have h := congrArg Fin.val (congrFun hf j)
  exact h.symm

theorem shapeOrderedEnum_val (hlu : l ≤ u) (j : ShapeBoundary l u) :
    (shapeOrderedEnum l u j).val = j.val.val - l.val := by
  have h := shapeOrderedEnum_symm_val hlu (shapeOrderedEnum l u j)
  rw [Equiv.symm_apply_apply] at h
  omega

def outsideOffsetEquiv (hlu : l ≤ u) : OutsideBoundary l u ≃ Fin (m - (u.val - l.val)) where
  toFun j := ⟨if j.val.val < l.val then j.val.val else j.val.val - (u.val - l.val), by
    have hu := u.isLt
    have hj := j.val.isLt
    have hn := j.property
    simp only [mem_boundaryClusterBlock] at hn
    split_ifs <;> omega⟩
  invFun j := ⟨⟨if j.val < l.val then j.val else j.val + (u.val - l.val), by
      have hu := u.isLt
      have hj := j.isLt
      have hl : l.val ≤ u.val := hlu
      split_ifs <;> omega⟩, by
    simp only [mem_boundaryClusterBlock]
    have hl : l.val ≤ u.val := hlu
    split_ifs <;> omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hl : l.val ≤ u.val := hlu
    have hn := j.property
    simp only [mem_boundaryClusterBlock] at hn
    change (if (if j.val.val < l.val then j.val.val else j.val.val - (u.val - l.val)) < l.val
      then (if j.val.val < l.val then j.val.val else j.val.val - (u.val - l.val))
      else (if j.val.val < l.val then j.val.val else j.val.val - (u.val - l.val)) + (u.val - l.val)) = j.val.val
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    have hl : l.val ≤ u.val := hlu
    change (if (if j.val < l.val then j.val else j.val + (u.val - l.val)) < l.val
      then (if j.val < l.val then j.val else j.val + (u.val - l.val))
      else (if j.val < l.val then j.val else j.val + (u.val - l.val)) - (u.val - l.val)) = j.val
    split_ifs <;> omega

theorem outsideOrderedEnum_symm_val (hlu : l ≤ u) (j : Fin (outsideM l u)) :
    ((outsideOrderedEnum l u).symm j).val.val =
      if j.val < l.val then j.val else j.val + (u.val - l.val) := by
  let f : Fin (outsideM l u) → Fin m := fun j ↦
    ((outsideOffsetEquiv hlu).symm (Fin.cast (outsideM_eq_sub hlu) j)).val
  have hf := Finset.orderEmbOfFin_unique
    (show ((boundaryClusterBlock l u)ᶜ).card = outsideM l u from by
      simpa only [Finset.mem_compl] using (Fintype.card_coe ((boundaryClusterBlock l u)ᶜ)).symm)
    (f := f) (fun j ↦ by exact Finset.mem_compl.mpr ((outsideOffsetEquiv hlu).symm (Fin.cast (outsideM_eq_sub hlu) j)).property)
    (by
      intro j k hjk
      change (if j.val < l.val then j.val else j.val + (u.val - l.val)) <
        (if k.val < l.val then k.val else k.val + (u.val - l.val))
      have hjk' : j.val < k.val := hjk
      split_ifs <;> omega)
  have h := congrArg Fin.val (congrFun hf j)
  exact h.symm

theorem outsideOrderedEnum_val (hlu : l ≤ u) (j : OutsideBoundary l u) :
    (outsideOrderedEnum l u j).val =
      if j.val.val < l.val then j.val.val else j.val.val - (u.val - l.val) := by
  have h := outsideOrderedEnum_symm_val hlu (outsideOrderedEnum l u j)
  rw [Equiv.symm_apply_apply] at h
  have hnot := j.property
  simp only [mem_boundaryClusterBlock] at hnot
  have hl : l.val ≤ u.val := hlu
  split_ifs at h ⊢ <;> omega

def shapeSourceEquiv (ha : a ∈ S) : {j : Fin n // j ∈ S} ≃ Fin (shapeN a S + 1) where
  toFun j := shapeSource (a := a) j.val j.property
  invFun j := Fin.cases ⟨a,ha⟩ (fun k ↦ ⟨(shapeEnum.symm k).val,(shapeEnum.symm k).property.1⟩) j
  left_inv j := by
    apply Subtype.ext
    by_cases hj : j.val = a
    · simp [shapeSource,hj]
    · simp [shapeSource,hj]
  right_inv j := by
    cases j using Fin.cases with
    | zero => simp [shapeSource]
    | succ j => simp [shapeSource, (shapeEnum.symm j).property.2]

def coarseSourceEquiv (hi : i ∉ S) : {j : Fin n // j ∉ S} ≃ Fin (coarseN i S + 1) where
  toFun j := coarseSource (i := i) j.val j.property
  invFun j := Fin.cases ⟨i,hi⟩ (fun k ↦ ⟨(coarseEnum.symm k).val,(coarseEnum.symm k).property.1⟩) j
  left_inv j := by
    apply Subtype.ext
    by_cases hj : j.val = i
    · simp [coarseSource,hj]
    · simp [coarseSource,hj]
  right_inv j := by
    cases j using Fin.cases with
    | zero => simp [coarseSource]
    | succ j => simp [coarseSource, (coarseEnum.symm j).property.2]


def physicalShapeCoordinates (D : BoundaryClusterData i a m S l u) : ShapeCoordinates a S l u :=
  (fun j ↦ D.velocity (shapeEnum.symm j).val,
    fun j ↦ D.boundaryVelocity ((shapeOrderedEnum l u).symm j).val)

def physicalCoarseCoordinates (D : BoundaryClusterData i a m S l u) : CoarseCoordinates i S l u :=
  (fun j ↦ D.base (coarseEnum.symm j).val,
    (centerSlot D.block_order).insertNth D.center
      (fun j ↦ D.boundaryBase ((outsideOrderedEnum l u).symm j).val))

theorem physicalShape_interior (D : BoundaryClusterData i a m S l u) (j : Fin (shapeN a S + 1)) :
    GraphForms.interiorPoint j (physicalShapeCoordinates D) =
      D.velocity ((shapeSourceEquiv D.anchor_mem).symm j).val := by
  cases j using Fin.cases with
  | zero => exact D.velocity_anchor.symm
  | succ j => rfl

theorem physicalCoarse_interior (D : BoundaryClusterData i a m S l u) (j : Fin (coarseN i S + 1)) :
    GraphForms.interiorPoint j (physicalCoarseCoordinates D) =
      D.base ((coarseSourceEquiv D.normalized_not_mem).symm j).val := by
  cases j using Fin.cases with
  | zero => exact D.base_normalized.symm
  | succ j => rfl

theorem physicalShape_admissible (D : BoundaryClusterData i a m S l u) :
    GraphForms.Admissible (physicalShapeCoordinates D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact D.velocity_im_pos _ (shapeEnum.symm j).property.1
  · intro j k h
    apply (shapeSourceEquiv D.anchor_mem).symm.injective
    apply Subtype.ext
    exact D.velocity_injective_on _ _ ((shapeSourceEquiv D.anchor_mem).symm j).property
      ((shapeSourceEquiv D.anchor_mem).symm k).property (by simpa only [physicalShape_interior] using h)
  · intro j k hjk
    exact D.boundaryVelocity_strictMono_on _ _ ((shapeOrderedEnum l u).symm j).property
      ((shapeOrderedEnum l u).symm k).property (shapeOrderedEnum_symm_strictMono hjk)

theorem center_lt_succAbove_iff (hlu : l ≤ u) (j : Fin (outsideM l u)) :
    centerSlot hlu < (centerSlot hlu).succAbove j ↔ l.val ≤ j.val := by
  by_cases hj : j.castSucc < centerSlot hlu
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    change (l.val < j.val) ↔ l.val ≤ j.val
    have h : j.val < l.val := hj
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)]
    change (l.val < j.val + 1) ↔ l.val ≤ j.val
    omega

theorem succAbove_lt_center_iff (hlu : l ≤ u) (j : Fin (outsideM l u)) :
    (centerSlot hlu).succAbove j < centerSlot hlu ↔ j.val < l.val := by
  by_cases hj : j.castSucc < centerSlot hlu
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)]
    change (j.val + 1 < l.val) ↔ j.val < l.val
    have h : l.val ≤ j.val := le_of_not_gt hj
    omega

theorem physicalCoarse_boundary_strictMono (D : BoundaryClusterData i a m S l u) :
    StrictMono (physicalCoarseCoordinates D).2 := by
  intro j k hjk
  cases j using Fin.succAboveCases (centerSlot D.block_order) with
  | x =>
    cases k using Fin.succAboveCases (centerSlot D.block_order) with
    | x => exact (hjk.false).elim
    | p k =>
      have hk := (center_lt_succAbove_iff D.block_order k).mp hjk
      have hv : u.val ≤ ((outsideOrderedEnum l u).symm k).val.val := by
        rw [outsideOrderedEnum_symm_val D.block_order, if_neg (not_lt_of_ge hk)]
        have hl : l.val ≤ u.val := D.block_order
        omega
      simp only [physicalCoarseCoordinates, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      exact D.center_lt_boundaryBase _ hv
  | p j =>
    cases k using Fin.succAboveCases (centerSlot D.block_order) with
    | x =>
      have hj := (succAbove_lt_center_iff D.block_order j).mp hjk
      have hv : ((outsideOrderedEnum l u).symm j).val.val < l.val := by
        rw [outsideOrderedEnum_symm_val D.block_order, if_pos hj]
        exact hj
      simp only [physicalCoarseCoordinates, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      exact D.boundaryBase_lt_center _ hv
    | p k =>
      have hlt : j < k := (Fin.strictMono_succAbove (centerSlot D.block_order)).lt_iff_lt.mp hjk
      simp only [physicalCoarseCoordinates, Fin.insertNth_apply_succAbove]
      exact D.boundaryBase_lt _ _ (outsideOrderedEnum_symm_strictMono hlt)
        (fun h ↦ ((outsideOrderedEnum l u).symm j).property h.1)

theorem physicalCoarse_admissible (D : BoundaryClusterData i a m S l u) :
    GraphForms.Admissible (physicalCoarseCoordinates D) := by
  refine ⟨?_, ?_, physicalCoarse_boundary_strictMono D⟩
  · intro j
    exact D.base_im_pos_off _ (coarseEnum.symm j).property.1
  · intro j k h
    apply (coarseSourceEquiv D.normalized_not_mem).symm.injective
    apply Subtype.ext
    exact D.base_injective_off _ _ ((coarseSourceEquiv D.normalized_not_mem).symm j).property
      ((coarseSourceEquiv D.normalized_not_mem).symm k).property (by simpa only [physicalCoarse_interior] using h)


theorem orderedSplitFace_eq_physical (D : BoundaryClusterData i a m S l u)
    (y : FaceCoordinates i a S m)
    (hD : D.coordinates = (BoundaryClusterFreeCoordinates.faceEmbedding y).parameters l u) :
    orderedSplitFace D.block_order y = (physicalShapeCoordinates D, physicalCoarseCoordinates D) := by
  have hb (j : Fin n) : D.base j = (BoundaryClusterFreeCoordinates.faceEmbedding y).base j :=
    congrArg (fun z ↦ z.2.1 j) hD
  have hv (j : Fin n) : D.velocity j = (BoundaryClusterFreeCoordinates.faceEmbedding y).velocity j :=
    congrArg (fun z ↦ z.2.2.1 j) hD
  have hqb (j : Fin m) : D.boundaryBase j = (BoundaryClusterFreeCoordinates.faceEmbedding y).boundaryBase l u j :=
    congrArg (fun z ↦ z.2.2.2.1 j) hD
  have hqv (j : Fin m) : D.boundaryVelocity j = (BoundaryClusterFreeCoordinates.faceEmbedding y).boundaryVelocity l u j :=
    congrArg (fun z ↦ z.2.2.2.2 j) hD
  have hc : D.center = (BoundaryClusterFreeCoordinates.faceEmbedding y).center := congrArg Prod.fst hD
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change y.2.1 (shapeEnum.symm j) = D.velocity (shapeEnum.symm j).val
      simpa [BoundaryClusterFreeCoordinates.velocity_shape, BoundaryClusterFreeCoordinates.faceEmbedding] using (hv (shapeEnum.symm j).val).symm
    · funext j
      obtain ⟨j, rfl⟩ := (shapeOrderedEnum l u).surjective j
      rw [ordered_shape_boundary]
      change y.2.2.1 j.val = D.boundaryVelocity ((shapeOrderedEnum l u).symm (shapeOrderedEnum l u j)).val
      rw [Equiv.symm_apply_apply]
      simpa [BoundaryClusterFreeCoordinates.boundaryVelocity, j.property, BoundaryClusterFreeCoordinates.faceEmbedding] using (hqv j.val).symm
  · apply Prod.ext
    · funext j
      change y.1 (coarseEnum.symm j) = D.base (coarseEnum.symm j).val
      simpa [BoundaryClusterFreeCoordinates.base_coarse, BoundaryClusterFreeCoordinates.faceEmbedding] using (hb (coarseEnum.symm j).val).symm
    · funext j
      cases j using Fin.succAboveCases (centerSlot D.block_order) with
      | x =>
        rw [ordered_coarse_center]
        simp only [physicalCoarseCoordinates, Fin.insertNth_apply_same]
        exact hc.symm
      | p j =>
        obtain ⟨j, rfl⟩ := (outsideOrderedEnum l u).surjective j
        rw [ordered_coarse_outside]
        simp only [physicalCoarseCoordinates, Fin.insertNth_apply_succAbove, Equiv.symm_apply_apply]
        simpa [BoundaryClusterFreeCoordinates.boundaryBase, j.property, BoundaryClusterFreeCoordinates.faceEmbedding] using (hqb j.val).symm

theorem orderedSplitFace_admissible (hlu : l ≤ u) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    GraphForms.Admissible (orderedSplitFace hlu y).1 ∧ GraphForms.Admissible (orderedSplitFace hlu y).2 := by
  obtain ⟨D,hD⟩ := (BoundaryClusterFreeCoordinates.faceEmbedding y).exists_datum l u hy
  have h := orderedSplitFace_eq_physical D y hD
  rw [h]
  exact ⟨physicalShape_admissible D, physicalCoarse_admissible D⟩

def physicalShapeNormalized (D : BoundaryClusterData i a m S l u) :
    Configuration.Normalized (0 : Fin (shapeN a S + 1)) (shapeM l u) :=
  GraphForms.toNormalized ⟨physicalShapeCoordinates D, physicalShape_admissible D⟩

def physicalCoarseNormalized (D : BoundaryClusterData i a m S l u) :
    Configuration.Normalized (0 : Fin (coarseN i S + 1)) (outsideM l u + 1) :=
  GraphForms.toNormalized ⟨physicalCoarseCoordinates D, physicalCoarse_admissible D⟩


def anchoredPartitionEquiv (ha : a ∈ S) (hi : i ∉ S) :
    Fin ((coarseN i S + 1) + (shapeN a S + 1)) ≃ Fin n :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (coarseSourceEquiv hi).symm (shapeSourceEquiv ha).symm).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : Fin n ↦ j ∈ S))))

@[simp] theorem anchoredPartition_outer (ha : a ∈ S) (hi : i ∉ S) (j : Fin (coarseN i S + 1)) :
    anchoredPartitionEquiv ha hi (Fin.castAdd (shapeN a S + 1) j) =
      ((coarseSourceEquiv hi).symm j).val := by
  simp [anchoredPartitionEquiv]

@[simp] theorem anchoredPartition_inner (ha : a ∈ S) (hi : i ∉ S) (j : Fin (shapeN a S + 1)) :
    anchoredPartitionEquiv ha hi (Fin.natAdd (coarseN i S + 1) j) =
      ((shapeSourceEquiv ha).symm j).val := by
  simp [anchoredPartitionEquiv]

@[simp] theorem anchoredPartition_outer_anchor (ha : a ∈ S) (hi : i ∉ S) :
    anchoredPartitionEquiv ha hi (Fin.castAdd (shapeN a S + 1) 0) = i := by
  rw [anchoredPartition_outer]
  rfl

@[simp] theorem anchoredPartition_inner_anchor (ha : a ∈ S) (hi : i ∉ S) :
    anchoredPartitionEquiv ha hi (Fin.natAdd (coarseN i S + 1) 0) = a := by
  rw [anchoredPartition_inner]
  rfl

def graftBoundaryEquiv (hlu : l < u) :
    Fin (outsideM l u + (shapeM l u - 1) + 1) ≃ Fin m := finCongr (graft_external_count hlu)

@[simp] theorem graftBoundaryEquiv_val (hlu : l < u)
    (j : Fin (outsideM l u + (shapeM l u - 1) + 1)) : (graftBoundaryEquiv hlu j).val = j.val := rfl

def outerArity (ha : a ∈ S) (hi : i ∉ S) (q : Fin n → ℕ) (j : Fin (coarseN i S + 1)) : ℕ :=
  q (anchoredPartitionEquiv ha hi (Fin.castAdd (shapeN a S + 1) j))

def innerArity (ha : a ∈ S) (hi : i ∉ S) (q : Fin n → ℕ) (j : Fin (shapeN a S + 1)) : ℕ :=
  q (anchoredPartitionEquiv ha hi (Fin.natAdd (coarseN i S + 1) j))

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
