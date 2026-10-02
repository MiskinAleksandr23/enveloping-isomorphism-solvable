import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSignedChange
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphRadiusFirstTransport
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductGraphDensity
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceSwapSign
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleSign

/-! Explicit derivative reduction for the paired product orientation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductSign
open InteriorGraphFaceCoordinates PairedForestOverlapJacobian PairedForestSmoothProduct
open PairedForestSimpleCluster BoxStokes OrientedFormChangeVariables ForestRadialFaceImmersion
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

/-- The derivative at zero angle and zero shape is just the literal coordinate
reordering; rotation contributes no additional determinant there. -/
def linearToAngular : ProductCoordinates i a b S m →L[ℝ] ClusterAngularCoordinates i a b S m where
  toFun p := (fun j ↦ p.2.1 (coarseEnum j), fun j ↦ p.1.2 (shapeEnum j), p.2.2, p.1.1, 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp
  cont := by fun_prop

theorem hasFDerivAt_toAngular_zero :
    HasFDerivAt (toAngular : ProductCoordinates i a b S m → _) linearToAngular 0 := by
  have hD := (linearToAngular (i := i) (a := a) (b := b) (S := S) (m := m)).hasFDerivAt (x := 0)
  have hp : DifferentiableAt ℝ (fun p : ProductCoordinates i a b S m ↦ circleParameter p.1.1) 0 :=
    ((contDiff_circleParameter.comp (show ContDiff ℝ ⊤
      (fun p : ProductCoordinates i a b S m ↦ p.1.1) from by fun_prop)).differentiable (by simp)).differentiableAt
  have hshape := hasFDerivAt_pi.mpr (fun j ↦ hp.hasFDerivAt.mul ((ContinuousLinearMap.proj j).hasFDerivAt.comp 0 hD.snd.fst))
  have hzero : circleParameter (0 : ℝ) = 1 := by simp [circleParameter_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, hzero, Function.comp_apply,
    ContinuousLinearMap.proj_apply, map_zero, Pi.zero_apply, one_smul, zero_smul, add_zero] at hshape
  have h := hD.fst.prodMk (hshape.prodMk hD.snd.snd)
  change HasFDerivAt toAngular _ 0 at h
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, linearToAngular]

variable {N r : ℕ} (hdim : GraphForms.dimension N m = r + 1)
  (x : Compactification (0 : Fin (N + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : ForestRadialFaceClassification.kind 0 x o = .paired)

def linearProductToNative : Coord r →L[ℝ] Coord r :=
  (faceProjection (Fin.last r)).comp ((simpleCoordinates hdim x o ho).toContinuousLinearMap.comp
    (linearToAngular.comp (PairedForestCartesianChange.cartesian hdim x o ho).toContinuousLinearMap))

theorem fderiv_productToNative_zero :
    fderiv ℝ (productToNative hdim x o ho) 0 = linearProductToNative hdim x o ho := by
  have ha : HasFDerivAt (toAngular : Product x o ho → _) linearToAngular
      (PairedForestCartesianChange.cartesian hdim x o ho (0 : Coord r)) := by
    rw [map_zero]
    exact hasFDerivAt_toAngular_zero
  have h := (faceProjection (Fin.last r)).hasFDerivAt.comp 0
    ((simpleCoordinates hdim x o ho).hasFDerivAt.comp 0
      (ha.comp 0 (PairedForestCartesianChange.cartesian hdim x o ho).hasFDerivAt))
  exact h.fderiv


abbrev C := ClusterCoarseIndex (0 : Fin (N + 1)) (anchor x o ho) (PairedForestSimpleCluster.S x o ho)
abbrev H := ClusterShapeIndex (anchor x o ho) (reference x o ho) (PairedForestSimpleCluster.S x o ho)

include hdim in
theorem faceDimension_eq : ClusterCoordinateOrder.faceDimension (C x o ho) (H x o ho) m = r := by
  have h := ClusterFaceOrientation.Interior.dimension_eq (m := m) (anchor_mem x o ho)
    (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)
  change ClusterCoordinateOrder.faceDimension (C x o ho) (H x o ho) m + 1 = _ at h
  omega

def nativeFaceOrder : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m ≃ Fin r :=
  (ClusterCoordinateOrder.faceEnum (C x o ho) (H x o ho) m).trans (finCongr (faceDimension_eq hdim x o ho))

def nativeFullOrder : ClusterAngularCoordinates.CoordinateIndex (0 : Fin (N + 1))
    (anchor x o ho) (reference x o ho) (PairedForestSimpleCluster.S x o ho) m ≃ Fin (r + 1) :=
  (ClusterFaceOrientation.Interior.sourceIndex (anchor_mem x o ho) (reference_mem x o ho)
    (reference_ne_anchor x o ho) (anchor_global x o ho)).trans (finCongr hdim)

theorem simpleCoordinates_apply (p : PairedForestFullOverlap.Angular x o ho)
    (j : ClusterAngularCoordinates.CoordinateIndex (0 : Fin (N + 1))
      (anchor x o ho) (reference x o ho) (PairedForestSimpleCluster.S x o ho) m) :
    simpleCoordinates hdim x o ho p (nativeFullOrder hdim x o ho j) =
      ClusterAngularCoordinates.coordinateBasis.repr p j := by
  simp [simpleCoordinates, simpleBasis, nativeFullOrder, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]

theorem nativeFullOrder_face (j : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m) :
    nativeFullOrder hdim x o ho ((ClusterCoordinateOrder.indexSplit (C x o ho) (H x o ho) m).symm (.inl j)) =
      (nativeFaceOrder hdim x o ho j).castSucc := by
  apply Fin.ext
  simp [nativeFullOrder, nativeFaceOrder, ClusterFaceOrientation.Interior.sourceIndex,
    ClusterFaceOrientation.Interior.nativeEnum, ClusterCoordinateOrder.fullEnum]

theorem linearProductToNative_apply (y : Coord r)
    (j : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m) :
    linearProductToNative hdim x o ho y (nativeFaceOrder hdim x o ho j) =
      ClusterAngularCoordinates.coordinateBasis.repr
        (linearToAngular (PairedForestCartesianChange.cartesian hdim x o ho y))
        ((ClusterCoordinateOrder.indexSplit (C x o ho) (H x o ho) m).symm (.inl j)) := by
  change simpleCoordinates hdim x o ho
      (linearToAngular (PairedForestCartesianChange.cartesian hdim x o ho y))
      ((Fin.last r).succAbove (nativeFaceOrder hdim x o ho j)) = _
  rw [Fin.succAbove_last, ← nativeFullOrder_face, simpleCoordinates_apply]


def productFaceSplit : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m ≃
    (Unit ⊕ (Σ _ : H x o ho, Fin 2)) ⊕ ((Σ _ : C x o ho, Fin 2) ⊕ Fin m) where
  toFun
    | .inl j => .inr (.inl j)
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr (.inl j)) => .inr (.inr j)
    | .inr (.inr (.inr u)) => .inl (.inl u)
  invFun
    | .inl (.inl u) => .inr (.inr (.inr u))
    | .inl (.inr j) => .inr (.inl j)
    | .inr (.inl j) => .inl j
    | .inr (.inr j) => .inr (.inr (.inl j))
  left_inv j := by rcases j with j | j | j | u <;> rfl
  right_inv j := by rcases j with (u | j) | (j | j) <;> rfl

def productFaceOrder : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m ≃ Fin r :=
  (productFaceSplit x o ho).trans
    (((Equiv.sumCongr
      ((Equiv.sumCongr (Fintype.equivFin Unit) (ClusterCoordinateOrder.complexIndexEnum (H x o ho))).trans finSumFinEquiv)
      ((Equiv.sumCongr (ClusterCoordinateOrder.complexIndexEnum (C x o ho)) (Equiv.refl (Fin m))).trans finSumFinEquiv)).trans
        finSumFinEquiv).trans (finCongr (PairedForestCartesianChange.dimension_eq hdim x o ho)))

theorem linearProductToNative_apply_order (y : Coord r)
    (j : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m) :
    linearProductToNative hdim x o ho y (nativeFaceOrder hdim x o ho j) =
      y (productFaceOrder hdim x o ho j) := by
  rw [linearProductToNative_apply]
  rcases j with ⟨j,k⟩ | ⟨j,k⟩ | j | u
  · fin_cases k <;>
      simp [ClusterAngularCoordinates.coordinateBasis, ClusterCoordinateOrder.indexSplit,
        linearToAngular, Pi.basis_repr, PairedForestCartesianChange.cartesian,
        PlanarCoarseCartesian.cartesian, PlanarCoarseCartesian.coarse,
        PlanarCoarseCartesian.shape, productFaceOrder, productFaceSplit,
        ClusterCoordinateOrder.complexIndexEnum] <;> rfl
  · fin_cases k <;>
      simp [ClusterAngularCoordinates.coordinateBasis, ClusterCoordinateOrder.indexSplit,
        linearToAngular, Pi.basis_repr, PairedForestCartesianChange.cartesian,
        PlanarCoarseCartesian.cartesian, PlanarCoarseCartesian.coarse,
        PlanarCoarseCartesian.shape, productFaceOrder, productFaceSplit,
        ClusterCoordinateOrder.complexIndexEnum] <;> rfl
  · simp [ClusterAngularCoordinates.coordinateBasis, ClusterCoordinateOrder.indexSplit,
      linearToAngular, PairedForestCartesianChange.cartesian,
      PlanarCoarseCartesian.cartesian, PlanarCoarseCartesian.coarse,
      PlanarCoarseCartesian.shape, productFaceOrder, productFaceSplit]
    rfl
  · cases u
    haveI : Subsingleton (Fin (Fintype.card Unit)) := by
      rw [Fintype.card_unique]
      infer_instance
    have hunit : Fintype.equivFin Unit () = 0 := Subsingleton.elim _ _
    simp [ClusterAngularCoordinates.coordinateBasis, ClusterCoordinateOrder.indexSplit,
      linearToAngular, PairedForestCartesianChange.cartesian,
      PlanarCoarseCartesian.cartesian, PlanarCoarseCartesian.coarse,
      PlanarCoarseCartesian.shape, productFaceOrder, productFaceSplit, hunit]
    change y _ = y _
    congr 1
    apply Fin.ext
    simp [hunit]


def orderPermutation : Equiv.Perm (Fin r) :=
  (nativeFaceOrder hdim x o ho).symm.trans (productFaceOrder hdim x o ho)

theorem linearProductToNative_apply_perm (y : Coord r) (j : Fin r) :
    linearProductToNative hdim x o ho y j = y (orderPermutation hdim x o ho j) := by
  obtain ⟨j, rfl⟩ := (nativeFaceOrder hdim x o ho).surjective j
  simpa only [orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply] using
    linearProductToNative_apply_order hdim x o ho y j

theorem det_linearProductToNative :
    (linearProductToNative hdim x o ho).det = (Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ) := by
  change (linearProductToNative hdim x o ho).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (linearProductToNative hdim x o ho).toLinearMap =
      (1 : Matrix (Fin r) (Fin r) ℝ).submatrix (orderPermutation hdim x o ho) id := by
    ext j k
    simp only [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, Matrix.one_apply]
    change linearProductToNative hdim x o ho (standardBasis r k) j = _
    rw [linearProductToNative_apply_perm]
    simp [standardBasis, Pi.single_apply, eq_comm]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one]

theorem productSign_eq_orderPermutation : productSign hdim x o ho =
    (Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ) := by
  have h := productSign_jacobian hdim x o ho (0 : Coord r)
  rw [jacobian, fderiv_productToNative_zero, det_linearProductToNative] at h
  have hs : (Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ) *
      (Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ) = 1 := by
    simp [← Int.cast_mul, ← Units.val_mul]
  have habs : |(Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (orderPermutation hdim x o ho)) with he | he <;> simp [he]
  rw [habs] at h
  have hn : (Equiv.Perm.sign (orderPermutation hdim x o ho) : ℝ) ≠ 0 := by
    intro hz
    simp [hz] at hs
  exact mul_right_cancel₀ hn (h.trans hs.symm)


def swappedFaceOrder : ClusterCoordinateOrder.FaceIndex (C x o ho) (H x o ho) m ≃ Fin r :=
  (ClusterFaceBasisSign.faceSwap (C x o ho) (H x o ho) m).trans
    ((ClusterCoordinateOrder.faceEnum (H x o ho) (C x o ho) m).trans
      (finCongr ((ClusterFaceBasisSign.faceDimension_swap (C x o ho) (H x o ho) m).symm.trans
        (faceDimension_eq hdim x o ho))))

theorem productFaceOrder_eq : productFaceOrder hdim x o ho =
    (swappedFaceOrder hdim x o ho).trans (finRotate r) := by
  have hd := faceDimension_eq hdim x o ho
  dsimp only [ClusterCoordinateOrder.faceDimension] at hd
  have hr : r ≠ 0 := by omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  ext j
  rcases j with ⟨j,k⟩ | ⟨j,k⟩ | j | u
  · have hj := (Fintype.equivFin (C x o ho) j).isLt
    have hk := k.isLt
    simp [-finRotate_apply, productFaceOrder, productFaceSplit, swappedFaceOrder, ClusterFaceBasisSign.faceSwap,
      ClusterCoordinateOrder.faceEnum, ClusterCoordinateOrder.complexIndexEnum, coe_finRotate, Fin.ext_iff]
    split_ifs <;> omega
  · have hj := (Fintype.equivFin (H x o ho) j).isLt
    have hk := k.isLt
    simp [-finRotate_apply, productFaceOrder, productFaceSplit, swappedFaceOrder, ClusterFaceBasisSign.faceSwap,
      ClusterCoordinateOrder.faceEnum, ClusterCoordinateOrder.complexIndexEnum, coe_finRotate, Fin.ext_iff]
    split_ifs <;> omega
  · have hj := j.isLt
    simp [-finRotate_apply, productFaceOrder, productFaceSplit, swappedFaceOrder, ClusterFaceBasisSign.faceSwap,
      ClusterCoordinateOrder.faceEnum, ClusterCoordinateOrder.complexIndexEnum, coe_finRotate, Fin.ext_iff]
    split_ifs <;> omega
  · cases u
    haveI : Subsingleton (Fin (Fintype.card Unit)) := by rw [Fintype.card_unique]; infer_instance
    have hunit : Fintype.equivFin Unit () = 0 := Subsingleton.elim _ _
    simp [-finRotate_apply, productFaceOrder, productFaceSplit, swappedFaceOrder, ClusterFaceBasisSign.faceSwap,
      ClusterCoordinateOrder.faceEnum, ClusterCoordinateOrder.complexIndexEnum, coe_finRotate, Fin.ext_iff, hunit]
    omega

theorem sign_swapped_order : Equiv.Perm.sign
    ((nativeFaceOrder hdim x o ho).symm.trans (swappedFaceOrder hdim x o ho)) = 1 := by
  have he : (nativeFaceOrder hdim x o ho).symm.trans (swappedFaceOrder hdim x o ho) =
      (nativeFaceOrder hdim x o ho).permCongr
        (ClusterFaceBasisSign.faceSwapPermutation (C x o ho) (H x o ho) m).symm := by
    ext j
    simp [nativeFaceOrder, swappedFaceOrder, ClusterFaceBasisSign.faceSwapPermutation,
      Equiv.permCongr_def, finCongr]
  rw [he, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_symm,
    ClusterFaceBasisSign.sign_face_swap_blocks]

theorem sign_orderPermutation : Equiv.Perm.sign (orderPermutation hdim x o ho) = (-1) ^ (r - 1) := by
  rw [orderPermutation, productFaceOrder_eq, ← Equiv.trans_assoc, Equiv.Perm.sign_trans,
    sign_swapped_order, mul_one, sign_finRotate]

theorem productSign_eq_pow : productSign hdim x o ho = (-1 : ℝ) ^ (r - 1) := by
  rw [productSign_eq_orderPermutation, sign_orderPermutation]
  simp

/-- The physical outward product orientation is minus the ordered product
frame. Both intermediate signs are computed from actual coordinate maps. -/
theorem productFaceSign_eq_neg_one : productFaceSign hdim x o ho = -1 := by
  have hd := faceDimension_eq hdim x o ho
  dsimp only [ClusterCoordinateOrder.faceDimension] at hd
  have hr : 0 < r := by omega
  rw [productFaceSign, simpleSign_eq_neg_one, productSign_eq_pow]
  have hp : (-1 : ℝ) ^ (r - 1) * (-1 : ℝ) ^ (r - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hr' : r = (r - 1) + 1 := by omega
  rw [hr', pow_succ]
  simp only [Nat.add_sub_cancel]
  nlinarith

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductSign
