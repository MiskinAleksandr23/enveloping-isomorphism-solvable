import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoorientation
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceBasisSign

/-! The proper-real physical multiplier is the sign of the actual native
coordinate permutation, including the relocation of the radial coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalParity
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestFullJacobian RealForestPhysicalFactor
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

abbrev C := BoundaryClusterCoarseIndex b (labelsSet x o)
abbrev H := BoundaryClusterShapeIndex a (labelsSet x o)
abbrev Q := BoundaryClusterFreeCoordinates.CoordinateIndex b a (labelsSet x o) m

def faceIndex : BoundaryGraphFaceFactorization.NativeFaceIndex b a (labelsSet x o) m ≃ Fin r :=
  (BoundaryGraphFaceFactorization.nativeIndexEnum (l := lower x o) (u := upper x o)).trans
    (finCongr (RealForestFaceChangeVariables.dimension_eq hdim x o a b ha hb))

def radialLastIndex : Q x o a b ≃ Fin (r+1) :=
  (ClusterCoordinateOrder.indexSplit (C x o b) (H x o a) m).trans
    ((Equiv.sumCongr (faceIndex hdim x o a b ha hb) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv)

def radialFirstIndex : Q x o a b ≃ Fin (r+1) :=
  (radialLastIndex hdim x o a b ha hb).trans (finRotate (r+1))

def physicalIndex : Q x o a b ≃ Fin (r+1) :=
  (ClusterFaceOrientation.Real.targetIndex ha hb).trans (finCongr hdim)

/-- Actual source-native to physical coordinate permutation. -/
def physicalPermutation : Equiv.Perm (Fin (r+1)) :=
  (radialFirstIndex hdim x o a b ha hb).symm.trans (physicalIndex hdim x o a b ha hb)

private theorem faceCoordinates_repr (q : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m)
    (j : BoundaryGraphFaceFactorization.NativeFaceIndex b a (labelsSet x o) m) :
    RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb q
      (faceIndex hdim x o a b ha hb j) = BoundaryGraphFaceFactorization.nativeFaceBasis.repr q j := by
  simp only [RealForestFaceChangeVariables.simpleCoordinates, ContinuousLinearEquiv.trans_apply,
    faceIndex, Equiv.trans_apply, ForestGlobalGraphStokes.coordinateCast_apply]
  simp [BoundaryGraphNativeTransport.nativeCoordinates, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]

private theorem fullCoordinates_rotate (q : BoundaryClusterFreeCoordinates b a (labelsSet x o) m)
    (j : Fin (r+1)) :
    fullCoordinates hdim x o a b ha hb q (finRotate (r+1) j) =
      (BoundaryGraphNativeOrientation.appendRadius r)
        (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb
          (BoundaryClusterFreeCoordinates.splitRadius q).1, q.radius) j := by
  change ((BoundaryGraphNativeOrientation.appendRadius r)
    (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb
      (BoundaryClusterFreeCoordinates.splitRadius q).1, q.radius))
      ((finRotate (r+1)).symm (finRotate (r+1) j)) = _
  rw [Equiv.symm_apply_apply]

theorem fullCoordinates_repr (q : BoundaryClusterFreeCoordinates b a (labelsSet x o) m)
    (j : Q x o a b) :
    fullCoordinates hdim x o a b ha hb q (radialFirstIndex hdim x o a b ha hb j) =
      BoundaryClusterFreeCoordinates.coordinateBasis.repr q j := by
  change fullCoordinates hdim x o a b ha hb q (finRotate (r+1) (radialLastIndex hdim x o a b ha hb j)) = _
  rw [fullCoordinates_rotate]
  obtain ⟨j,rfl⟩ := (ClusterCoordinateOrder.indexSplit (C x o b) (H x o a) m).symm.surjective j
  rcases j with j | u
  · have hi : radialLastIndex hdim x o a b ha hb
        ((ClusterCoordinateOrder.indexSplit (C x o b) (H x o a) m).symm (.inl j)) =
        (faceIndex hdim x o a b ha hb j).castSucc := by
      simp only [radialLastIndex, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
      apply Fin.ext
      rfl
    rw [hi]
    change (Fin.last r).insertNth (α := fun _ => ℝ) q.radius
      (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb
        (BoundaryClusterFreeCoordinates.splitRadius q).1) (faceIndex hdim x o a b ha hb j).castSucc = _
    rw [← Fin.succAbove_last, Fin.insertNth_apply_succAbove, faceCoordinates_repr]
    rcases j with j | j | j | u <;> rfl
  · cases u
    have hi : radialLastIndex hdim x o a b ha hb
        ((ClusterCoordinateOrder.indexSplit (C x o b) (H x o a) m).symm (.inr ())) = Fin.last r := by
      apply Fin.ext
      simp [radialLastIndex]
    rw [hi]
    change (Fin.last r).insertNth (α := fun _ => ℝ) q.radius
      (RealForestFaceChangeVariables.simpleCoordinates hdim x o a b ha hb
        (BoundaryClusterFreeCoordinates.splitRadius q).1) (Fin.last r) = _
    rw [Fin.insertNth_apply_same]
    simp [BoundaryClusterFreeCoordinates.coordinateBasis, ClusterCoordinateOrder.indexSplit,
      BoundaryClusterFreeCoordinates.radius]

theorem physicalOutput_repr (y : Coord (r+1)) (j : Q x o a b) :
    physicalOutput hdim x o a b ha hb y (physicalIndex hdim x o a b ha hb j) =
      y (radialFirstIndex hdim x o a b ha hb j) := by
  change ForestGlobalGraphStokes.nativeCoordinates hdim
    (ClusterStandardCoordinates.freeGraph b ((RealClusterInsertionCoordinates.outputCoordinates ha hb).symm
      ((fullCoordinates hdim x o a b ha hb).symm y)))
    (finCongr hdim (ClusterFaceOrientation.Real.targetIndex ha hb j)) = _
  rw [ForestGlobalGraphStokes.nativeCoordinates, ContinuousLinearEquiv.trans_apply,
    ForestGlobalGraphStokes.coordinateCast_apply]
  change (GraphForms.realBasis n m).repr
    (ClusterStandardCoordinates.freeGraph b ((RealClusterInsertionCoordinates.outputCoordinates ha hb).symm
      ((fullCoordinates hdim x o a b ha hb).symm y)))
    (ClusterStandardCoordinates.realIndexEquiv b (RealClusterInsertionOrientation.realIndexEquiv ha hb j)) = _
  rw [ClusterStandardCoordinates.standard_repr]
  change RealClusterInsertionOrientation.freeBasis.repr
    ((RealClusterInsertionCoordinates.outputCoordinates ha hb).symm ((fullCoordinates hdim x o a b ha hb).symm y))
    (RealClusterInsertionOrientation.realIndexEquiv ha hb j) = _
  rw [← RealClusterInsertionOrientation.outputCoordinates_repr ha hb _ j,
    ContinuousLinearEquiv.apply_symm_apply, ← fullCoordinates_repr hdim x o a b ha hb]
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem physicalOutput_apply (y : Coord (r+1)) (j : Fin (r+1)) :
    physicalOutput hdim x o a b ha hb y j = y ((physicalPermutation hdim x o a b ha hb).symm j) := by
  obtain ⟨j,rfl⟩ := (physicalIndex hdim x o a b ha hb).surjective j
  rw [physicalOutput_repr]
  simp [physicalPermutation]

/-- Exact determinant of the actual physical coordinate map. -/
theorem det_physicalOutput : (physicalOutput hdim x o a b ha hb).toLinearMap.det =
    (Equiv.Perm.sign (physicalPermutation hdim x o a b ha hb) : ℝ) := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (physicalOutput hdim x o a b ha hb).toLinearMap =
      (1 : Matrix (Fin (r+1)) (Fin (r+1)) ℝ).submatrix
        (physicalPermutation hdim x o a b ha hb).symm id := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
    change physicalOutput hdim x o a b ha hb (Pi.single j 1) i = _
    rw [physicalOutput_apply]
    simp only [Pi.single_apply]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one, Equiv.Perm.sign_symm]

theorem physicalSign_eq_permutation : physicalSign hdim x o a b ha hb =
    (Equiv.Perm.sign (physicalPermutation hdim x o a b ha hb) : ℝ) := by
  unfold physicalSign
  rw [det_physicalOutput]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (physicalPermutation hdim x o a b ha hb)) with h | h <;>
    rw [h] <;> norm_num

/-- Radial-last real insertion permutes complete complex pairs, hence is even. -/
theorem real_basisPermutation_sign {N M : ℕ} {i c : Fin (N+1)} {S : Finset (Fin (N+1))}
    (hc : c ∈ S) (hi : i ∉ S) :
    Equiv.Perm.sign (ClusterFaceOrientation.Real.basisPermutation (m := M) hc hi) = 1 := by
  let e := (RealClusterInsertionCoordinates.labelEquiv hc hi).trans (finSuccAboveEquiv i).symm
  have ht : ClusterFaceOrientation.Real.targetIndex (m := M) hc hi =
      ClusterFaceBasisSign.targetOfLabels (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex c S) M e := by
    apply Equiv.ext
    intro j
    rcases j with ⟨d,k⟩ | ⟨h,k⟩ | j | u | u <;>
      simp [ClusterFaceOrientation.Real.targetIndex, RealClusterInsertionOrientation.realIndexEquiv,
        ClusterStandardCoordinates.realIndexEquiv, ClusterFaceBasisSign.targetOfLabels,
        ClusterFaceBasisSign.pairIndex, e]
  rw [ClusterFaceOrientation.Real.basisPermutation, ht]
  exact ClusterFaceBasisSign.sign_source_target _ _ M e (ClusterFaceOrientation.Real.dimension_eq hc hi)

theorem radialLastIndex_eq : radialLastIndex hdim x o a b ha hb =
    (ClusterFaceOrientation.Real.sourceIndex ha hb).trans (finCongr hdim) := by
  apply Equiv.ext
  intro j
  apply Fin.ext
  obtain ⟨j,rfl⟩ := (ClusterCoordinateOrder.indexSplit (C x o b) (H x o a) m).symm.surjective j
  rcases j with j | u
  · simp only [radialLastIndex, ClusterFaceOrientation.Real.sourceIndex,
      ClusterFaceOrientation.Real.nativeEnum, ClusterCoordinateOrder.fullEnum,
      Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_castAdd]
    rfl
  · cases u
    simp [radialLastIndex, ClusterFaceOrientation.Real.sourceIndex,
      ClusterFaceOrientation.Real.nativeEnum, ClusterCoordinateOrder.fullEnum]

theorem physicalPermutation_sign :
    Equiv.Perm.sign (physicalPermutation hdim x o a b ha hb) = (-1 : ℤˣ) ^ r := by
  have hl : Equiv.Perm.sign ((radialLastIndex hdim x o a b ha hb).symm.trans
      (physicalIndex hdim x o a b ha hb)) = 1 := by
    have he : (radialLastIndex hdim x o a b ha hb).symm.trans (physicalIndex hdim x o a b ha hb) =
        (physicalIndex hdim x o a b ha hb).permCongr
          (ClusterFaceOrientation.Real.basisPermutation ha hb).symm := by
      apply Equiv.ext
      intro j
      simp only [radialLastIndex_eq, physicalIndex, ClusterFaceOrientation.Real.basisPermutation,
        Equiv.permCongr_def, Equiv.trans_apply, Equiv.symm_trans_apply,
        Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm]
    rw [he, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_symm, real_basisPermutation_sign]
  have he : physicalPermutation hdim x o a b ha hb =
      (finRotate (r+1)).symm.trans ((radialLastIndex hdim x o a b ha hb).symm.trans
        (physicalIndex hdim x o a b ha hb)) := by
    apply Equiv.ext
    intro j
    rfl
  rw [he, Equiv.Perm.sign_trans, hl, one_mul, Equiv.Perm.sign_symm, sign_finRotate]
  simp

/-- The actual physical sign is precisely the r-place relocation of radius. -/
theorem physicalSign_eq : physicalSign hdim x o a b ha hb = (-1 : ℝ) ^ r := by
  rw [physicalSign_eq_permutation, physicalPermutation_sign]
  norm_cast

/-- For the main three-boundary-point relation, the physical multiplier is +1. -/
theorem physicalSign_three {N R : ℕ} (hd : GraphForms.dimension N 3 = R+1)
    (X : Compactification (0 : Fin (N+1)) 3) (O : Orbit 0 X) (A B : Fin (N+1))
    (hA : A ∈ labelsSet X O) (hB : B ∉ labelsSet X O) : physicalSign hd X O A B hA hB = 1 := by
  rw [physicalSign_eq]
  have hR : R = 2 * (N+1) := by simp only [GraphForms.dimension] at hd; omega
  rw [hR, pow_mul]
  norm_num

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalParity
