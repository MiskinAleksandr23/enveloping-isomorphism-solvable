import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.FixedAnchorPermutation

/-! The actual interior insertion basis permutation is even: complex labels
move in oriented two-dimensional blocks, including the angle/radius pair. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign
open ClusterCoordinateOrder
open scoped Classical
variable (C H : Type*) [Fintype C] [Fintype H] (m : ℕ)
abbrev Labels := C ⊕ H ⊕ Unit
abbrev labelCount := Fintype.card C + (Fintype.card H + 1)

def labelEnum : Labels C H ≃ Fin (labelCount C H) :=
  (Equiv.sumCongr (Fintype.equivFin C)
    ((Equiv.sumCongr (Fintype.equivFin H) (Fintype.equivFin Unit)).trans finSumFinEquiv)).trans finSumFinEquiv

def pairIndex : FullIndex C H m ≃ ((Labels C H × Fin 2) ⊕ Fin m) where
  toFun
    | .inl ⟨c,k⟩ => .inl (.inl c,k)
    | .inr (.inl ⟨h,k⟩) => .inl (.inr (.inl h),k)
    | .inr (.inr (.inl j)) => .inr j
    | .inr (.inr (.inr (.inl _))) => .inl (.inr (.inr ()),0)
    | .inr (.inr (.inr (.inr _))) => .inl (.inr (.inr ()),1)
  invFun
    | .inl (.inl c,k) => .inl ⟨c,k⟩
    | .inl (.inr (.inl h),k) => .inr (.inl ⟨h,k⟩)
    | .inl (.inr (.inr _),k) => if k = 0 then .inr (.inr (.inr (.inl ()))) else .inr (.inr (.inr (.inr ())))
    | .inr j => .inr (.inr (.inl j))
  left_inv q := by
    rcases q with ⟨c,k⟩ | ⟨h,k⟩ | j | u | u <;> simp
  right_inv q := by
    rcases q with ⟨c|h|u,k⟩ | j
    · rfl
    · rfl
    · cases u; fin_cases k <;> rfl
    · rfl

def canonicalIndex : FullIndex C H m ≃ Fin (GraphForms.dimension (labelCount C H) m) :=
  (pairIndex C H m).trans
    ((Equiv.sumCongr (Equiv.prodCongr (labelEnum C H) (Equiv.refl (Fin 2))) (Equiv.refl (Fin m))).trans
      (GraphForms.coordinateIndexEquiv (labelCount C H) m))



@[simp] theorem native_coarse_val (c : C) (k : Fin 2) :
    (fullEnum C H m (.inl ⟨c,k⟩)).val = (Fintype.equivFin C c).val * 2 + k.val := by
  simp [fullEnum, indexSplit, faceEnum, complexIndexEnum, finProdFinEquiv]
  omega
@[simp] theorem native_shape_val (h : H) (k : Fin 2) :
    (fullEnum C H m (.inr (.inl ⟨h,k⟩))).val = Fintype.card C * 2 + (Fintype.equivFin H h).val * 2 + k.val := by
  simp [fullEnum, indexSplit, faceEnum, complexIndexEnum, finProdFinEquiv]
  omega
@[simp] theorem native_boundary_val (j : Fin m) :
    (fullEnum C H m (.inr (.inr (.inl j)))).val = Fintype.card C * 2 + Fintype.card H * 2 + j.val := by
  simp [fullEnum, indexSplit, faceEnum, Nat.add_assoc]
@[simp] theorem native_angle_val :
    (fullEnum C H m (.inr (.inr (.inr (.inl ()))))).val = Fintype.card C * 2 + Fintype.card H * 2 + m := by
  simp [fullEnum, indexSplit, faceEnum, Nat.add_assoc]
@[simp] theorem native_radius_val :
    (fullEnum C H m (.inr (.inr (.inr (.inr ()))))).val = Fintype.card C * 2 + Fintype.card H * 2 + m + 1 := by
  simp [fullEnum, indexSplit, faceDimension, Nat.add_assoc]

@[simp] theorem canonical_coarse_val (c : C) (k : Fin 2) :
    (canonicalIndex C H m (.inl ⟨c,k⟩)).val = (Fintype.equivFin C c).val * 2 + k.val := by
  simp [canonicalIndex,pairIndex,labelEnum,GraphForms.coordinateIndexEquiv,finProdFinEquiv]
  omega
@[simp] theorem canonical_shape_val (h : H) (k : Fin 2) :
    (canonicalIndex C H m (.inr (.inl ⟨h,k⟩))).val = Fintype.card C * 2 + (Fintype.equivFin H h).val * 2 + k.val := by
  simp [canonicalIndex,pairIndex,labelEnum,GraphForms.coordinateIndexEquiv,finProdFinEquiv]
  omega
@[simp] theorem canonical_boundary_val (j : Fin m) :
    (canonicalIndex C H m (.inr (.inr (.inl j)))).val = Fintype.card C * 2 + Fintype.card H * 2 + 2 + j.val := by
  simp [canonicalIndex,pairIndex,labelEnum,labelCount,GraphForms.coordinateIndexEquiv]
  omega
@[simp] theorem canonical_angle_val :
    (canonicalIndex C H m (.inr (.inr (.inr (.inl ()))))).val = Fintype.card C * 2 + Fintype.card H * 2 := by
  simp [canonicalIndex,pairIndex,labelEnum,GraphForms.coordinateIndexEquiv,finProdFinEquiv]
  omega
@[simp] theorem canonical_radius_val :
    (canonicalIndex C H m (.inr (.inr (.inr (.inr ()))))).val = Fintype.card C * 2 + Fintype.card H * 2 + 1 := by
  simp [canonicalIndex,pairIndex,labelEnum,GraphForms.coordinateIndexEquiv,finProdFinEquiv]
  omega

abbrev prefixSize := Fintype.card C * 2 + Fintype.card H * 2

def splitFin : Fin (GraphForms.dimension (labelCount C H) m) ≃ (Fin (prefixSize C H) ⊕ Fin (m+2)) :=
  (finCongr (by dsimp [GraphForms.dimension,labelCount,prefixSize]; omega)).trans finSumFinEquiv.symm

def shuffle : Equiv.Perm (Fin (GraphForms.dimension (labelCount C H) m)) :=
  (splitFin C H m).symm.permCongr
    (Equiv.sumCongr (Equiv.refl _) ((finRotate (m+2)) ^ 2))

theorem sign_shuffle : Equiv.Perm.sign (shuffle C H m) = 1 := by
  simp [shuffle, Equiv.Perm.sign_sumCongr, map_pow, pow_two, Int.units_mul_self]

theorem rotate_two_val (j : Fin (m+2)) :
    (((finRotate (m+2)) ^ 2) j).val = if j.val < m then j.val + 2 else j.val - m := by
  have hj := j.isLt
  simp only [pow_two, Equiv.Perm.mul_apply, coe_finRotate, Fin.ext_iff, Fin.val_last]
  split_ifs <;> simp_all <;> omega

theorem shuffle_prefix (w : Fin (GraphForms.dimension (labelCount C H) m))
    (hw : w.val < prefixSize C H) : (shuffle C H m w).val = w.val := by
  have he : w = (splitFin C H m).symm (.inl ⟨w.val,hw⟩) := by
    apply Fin.ext
    simp [splitFin]
  conv_lhs => rw [he]
  simp only [shuffle, Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
  simp [splitFin, finCongr]

theorem shuffle_tail (w : Fin (GraphForms.dimension (labelCount C H) m))
    (j : Fin (m+2)) (hw : w.val = prefixSize C H + j.val) :
    (shuffle C H m w).val = prefixSize C H + if j.val < m then j.val + 2 else j.val - m := by
  have he : w = (splitFin C H m).symm (.inr j) := by
    apply Fin.ext
    simpa [splitFin] using hw
  rw [he]
  simp only [shuffle, Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr]
  simp [splitFin, finCongr, rotate_two_val]

def sourceCanonical : FullIndex C H m ≃ Fin (GraphForms.dimension (labelCount C H) m) :=
  (fullEnum C H m).trans (finCongr (by dsimp [faceDimension,GraphForms.dimension,labelCount]; omega))

theorem shuffle_sourceCanonical (j : FullIndex C H m) :
    shuffle C H m (sourceCanonical C H m j) = canonicalIndex C H m j := by
  apply Fin.ext
  rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u | u
  · rw [shuffle_prefix]
    · simp [sourceCanonical]
    · have hc := (Fintype.equivFin C c).isLt
      have hk := k.isLt
      simp only [sourceCanonical,Equiv.trans_apply,finCongr_apply,Fin.val_cast,native_coarse_val]
      dsimp [prefixSize]
      omega
  · rw [shuffle_prefix]
    · simp [sourceCanonical]
    · have hh := (Fintype.equivFin H h).isLt
      have hk := k.isLt
      simp only [sourceCanonical,Equiv.trans_apply,finCongr_apply,Fin.val_cast,native_shape_val]
      dsimp [prefixSize]
      omega
  · rw [shuffle_tail C H m _ ⟨j.val,by omega⟩ (by simp [sourceCanonical,prefixSize])]
    simp [j.isLt,prefixSize]
    omega
  · cases u
    rw [shuffle_tail C H m _ ⟨m,by omega⟩ (by simp [sourceCanonical,prefixSize])]
    simp [prefixSize]
  · cases u
    rw [shuffle_tail C H m _ ⟨m+1,by omega⟩ (by simp [sourceCanonical,prefixSize,Nat.add_assoc])]
    simp [prefixSize]

theorem sign_source_canonical :
    Equiv.Perm.sign ((sourceCanonical C H m).trans (canonicalIndex C H m).symm) = 1 := by
  have he : (sourceCanonical C H m).trans (canonicalIndex C H m).symm =
      (canonicalIndex C H m).symm.permCongr (shuffle C H m).symm := by
    ext j
    apply (canonicalIndex C H m).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.permCongr_def,
      Equiv.symm_symm]
    exact ((shuffle C H m).eq_symm_apply).mpr (shuffle_sourceCanonical C H m j)
  rw [he,Equiv.Perm.sign_permCongr]
  simpa using congrArg Inv.inv (sign_shuffle C H m)

def targetOfLabels {n : ℕ} (e : Labels C H ≃ Fin n) :
    FullIndex C H m ≃ Fin (GraphForms.dimension n m) :=
  (pairIndex C H m).trans
    ((Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin 2))) (Equiv.refl (Fin m))).trans
      (GraphForms.coordinateIndexEquiv n m))

theorem sign_source_target {n : ℕ} (e : Labels C H ≃ Fin n)
    (hd : faceDimension C H m + 1 = GraphForms.dimension n m) :
    Equiv.Perm.sign (((fullEnum C H m).trans (finCongr hd)).trans (targetOfLabels C H m e).symm) = 1 := by
  have hn : labelCount C H = n := by
    have h := Fintype.card_congr e
    simpa [Labels,labelCount] using h
  subst n
  let p : Equiv.Perm (Fin (labelCount C H)) := (labelEnum C H).symm.trans e
  have ht : targetOfLabels C H m e =
      (canonicalIndex C H m).trans (GraphForms.fixedAnchorCoordinatePerm (m := m) p) := by
    ext j
    rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u | u <;>
      simp [targetOfLabels,canonicalIndex,pairIndex,GraphForms.fixedAnchorCoordinatePerm,
        Equiv.permCongr_def,p]
  rw [ht]
  change Equiv.Perm.sign ((sourceCanonical C H m).trans
    ((GraphForms.fixedAnchorCoordinatePerm (m := m) p).symm.trans (canonicalIndex C H m).symm)) = 1
  rw [Equiv.Perm.sign_trans_trans]
  change Equiv.Perm.sign (GraphForms.fixedAnchorCoordinatePerm (m := m) p).symm *
    Equiv.Perm.sign ((sourceCanonical C H m).trans (canonicalIndex C H m).symm) = 1
  rw [sign_source_canonical]
  have hs := GraphForms.sign_fixedAnchorCoordinatePerm (m := m) p
  simpa using congrArg Inv.inv hs

/-- The finite basis permutation of the actual physical interior insertion is even. -/
theorem sign_basisPermutation {n m : ℕ} {i a b : Fin (n+1)} {S : Finset (Fin (n+1))}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Equiv.Perm.sign (ClusterFaceOrientation.Interior.basisPermutation (m := m) ha hb hba hanchor) = 1 := by
  let e := (InteriorClusterInsertionCoordinates.labelEquiv hb hba hanchor).trans (finSuccAboveEquiv i).symm
  have ht : ClusterFaceOrientation.Interior.targetIndex (m := m) hb hba hanchor =
      targetOfLabels (ClusterCoarseIndex i a S) (ClusterShapeIndex a b S) m e := by
    ext j
    rcases j with ⟨c,k⟩ | ⟨h,k⟩ | j | u | u <;>
      simp [ClusterFaceOrientation.Interior.targetIndex,
        InteriorClusterInsertionOrientation.realIndexEquiv,
        ClusterStandardCoordinates.realIndexEquiv,targetOfLabels,pairIndex,e]
  rw [ClusterFaceOrientation.Interior.basisPermutation,ht]
  exact sign_source_target _ _ m e (ClusterFaceOrientation.Interior.dimension_eq ha hb hba hanchor)

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign
