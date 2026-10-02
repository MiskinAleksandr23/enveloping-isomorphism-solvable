import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterCoordinateOrder
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterOutwardFrame

/-! Physical standard-coordinate insertion Jacobians and outward-normal-first
frames. Every remaining permutation sign comes from an actual finite bijection. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceOrientation

open ClusterStandardCoordinates

variable {n m : ℕ}

section Generic

variable {J E : Type*} [Fintype J] [DecidableEq J] [AddCommGroup E] [Module ℝ E]
  (i : Fin (n + 1))

/-- The physical standard matrix is obtained by the two actual basis-index
bijections. This keeps their sign instead of assuming an orientation. -/
theorem det_standardMatrix (b : Module.Basis J ℝ E)
    (t : Module.Basis J ℝ (InteriorClusterInsertionCoordinates.FreeCoordinates i m))
    (sourceIndex targetIndex : J ≃ Fin (GraphForms.dimension n m))
    (hcoord : ∀ z j, (GraphForms.realBasis n m).repr (freeGraph i z) (targetIndex j) = t.repr z j)
    (D : E →ₗ[ℝ] InteriorClusterInsertionCoordinates.FreeCoordinates i m) :
    (LinearMap.toMatrix (b.reindex sourceIndex) (GraphForms.realBasis n m)
      ((freeGraph i).toLinearMap.comp D)).det =
      (Equiv.Perm.sign (sourceIndex.trans targetIndex.symm) : ℝ) *
        (LinearMap.toMatrix b t D).det := by
  have hm : LinearMap.toMatrix (b.reindex sourceIndex) (GraphForms.realBasis n m)
      ((freeGraph i).toLinearMap.comp D) =
      Matrix.reindex targetIndex sourceIndex (LinearMap.toMatrix b t D) := by
    ext j k
    obtain ⟨j, rfl⟩ := targetIndex.surjective j
    obtain ⟨k, rfl⟩ := sourceIndex.surjective k
    simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
      Equiv.symm_apply_apply, LinearMap.comp_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact hcoord _ j
  rw [hm, Matrix.det_reindex]

end Generic

namespace Interior

open InteriorClusterInsertionCoordinates InteriorClusterInsertionJacobian

variable {i a b : Fin (n + 1)} {S : Finset (Fin (n + 1))}

local instance : DecidableEq (ClusterAngularCoordinates.CoordinateIndex i a b S m) := Classical.decEq _

abbrev faceDimension (i a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) (m : ℕ) :=
  ClusterCoordinateOrder.faceDimension (ClusterCoarseIndex i a S) (ClusterShapeIndex a b S) m

def nativeEnum : ClusterAngularCoordinates.CoordinateIndex i a b S m ≃ Fin (faceDimension i a b S m + 1) :=
  ClusterCoordinateOrder.fullEnum (ClusterCoarseIndex i a S) (ClusterShapeIndex a b S) m

theorem dimension_eq (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    faceDimension i a b S m + 1 = GraphForms.dimension n m := by
  have hcard := Fintype.card_congr (nativeEnum (i := i) (a := a) (b := b) (S := S) (m := m))
  have hdim := Module.finrank_eq_card_basis (ClusterAngularCoordinates.coordinateBasis
    (i := i) (a := a) (b := b) (S := S) (m := m))
  rw [ClusterAngularCoordinates.finrank_eq ha hb hba hanchor, hcard, Fintype.card_fin] at hdim
  unfold GraphForms.dimension
  omega

def sourceIndex (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    ClusterAngularCoordinates.CoordinateIndex i a b S m ≃ Fin (GraphForms.dimension n m) :=
  nativeEnum.trans (finCongr (dimension_eq ha hb hba hanchor))

def targetIndex (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    ClusterAngularCoordinates.CoordinateIndex i a b S m ≃ Fin (GraphForms.dimension n m) :=
  (InteriorClusterInsertionOrientation.realIndexEquiv hb hba hanchor).trans (realIndexEquiv i)

def basisPermutation (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Equiv.Perm (ClusterAngularCoordinates.CoordinateIndex i a b S m) :=
  (sourceIndex ha hb hba hanchor).trans (targetIndex hb hba hanchor).symm

def physicalInsertion (x : ClusterAngularCoordinates i a b S m) : GraphForms.Coordinates n m :=
  freeGraph i (insertion x)

/-- The true physical Jacobian in the actual standard graph basis. -/
theorem det_physicalInsertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    (LinearMap.toMatrix
      (ClusterAngularCoordinates.coordinateBasis.reindex (sourceIndex ha hb hba hanchor))
      (GraphForms.realBasis n m) (fderiv ℝ physicalInsertion x).toLinearMap).det =
      (Equiv.Perm.sign (basisPermutation (m := m) ha hb hba hanchor) : ℝ) *
        (-x.2.2.2.2 ^ (2 * S.card - 3)) := by
  have h := (freeGraph i).hasFDerivAt.comp x
    (InteriorClusterInsertionOrientation.differentiableAt_insertion x).hasFDerivAt
  change HasFDerivAt physicalInsertion _ x at h
  rw [h.fderiv]
  change (LinearMap.toMatrix _ _ ((freeGraph i).toLinearMap.comp
    (fderiv ℝ insertion x).toLinearMap)).det = _
  rw [det_standardMatrix i _ (InteriorClusterInsertionOrientation.insertionTargetBasis hb hba hanchor)
      (sourceIndex ha hb hba hanchor) (targetIndex hb hba hanchor) ?_,
    InteriorClusterInsertionOrientation.det_toMatrix_insertion ha hb hba hanchor x]
  · rfl
  intro z j
  rw [targetIndex, Equiv.trans_apply, standard_repr]
  simp [InteriorClusterInsertionOrientation.insertionTargetBasis]

def radialLastBasis : Module.Basis (Fin (faceDimension i a b S m + 1)) ℝ
    (ClusterAngularCoordinates i a b S m) :=
  ClusterAngularCoordinates.coordinateBasis.reindex nativeEnum

def outwardFrame : Fin (faceDimension i a b S m + 1) → ClusterAngularCoordinates i a b S m :=
  ClusterOutwardFrame.frame radialLastBasis

theorem det_outwardFrame :
    (radialLastBasis (i := i) (a := a) (b := b) (S := S) (m := m)).det outwardFrame =
      (-1 : ℝ) ^ (faceDimension i a b S m + 1) :=
  ClusterOutwardFrame.basis_det_frame _

@[simp] theorem outwardFrame_zero_radius :
    (outwardFrame (i := i) (a := a) (b := b) (S := S) (m := m) 0).2.2.2.2 = -1 := by
  simp [outwardFrame, ClusterOutwardFrame.frame_zero, radialLastBasis, nativeEnum,
    ClusterCoordinateOrder.fullEnum_symm_last, ClusterCoordinateOrder.radiusIndex,
    ClusterAngularCoordinates.coordinateBasis]

end Interior

namespace Real

open RealClusterInsertionCoordinates RealClusterInsertionJacobian

variable {i a : Fin (n + 1)} {S : Finset (Fin (n + 1))}

local instance : DecidableEq (BoundaryClusterFreeCoordinates.CoordinateIndex i a S m) := Classical.decEq _

abbrev faceDimension (i a : Fin (n + 1)) (S : Finset (Fin (n + 1))) (m : ℕ) :=
  ClusterCoordinateOrder.faceDimension (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) m

def nativeEnum : BoundaryClusterFreeCoordinates.CoordinateIndex i a S m ≃ Fin (faceDimension i a S m + 1) :=
  ClusterCoordinateOrder.fullEnum (BoundaryClusterCoarseIndex i S) (BoundaryClusterShapeIndex a S) m

theorem dimension_eq (ha : a ∈ S) (hi : i ∉ S) :
    faceDimension i a S m + 1 = GraphForms.dimension n m := by
  have hcard := Fintype.card_congr (nativeEnum (i := i) (a := a) (S := S) (m := m))
  have hdim := Module.finrank_eq_card_basis (BoundaryClusterFreeCoordinates.coordinateBasis
    (i := i) (a := a) (S := S) (m := m))
  rw [BoundaryClusterFreeCoordinates.finrank_eq ha hi, hcard, Fintype.card_fin] at hdim
  unfold GraphForms.dimension
  omega

def sourceIndex (ha : a ∈ S) (hi : i ∉ S) :
    BoundaryClusterFreeCoordinates.CoordinateIndex i a S m ≃ Fin (GraphForms.dimension n m) :=
  nativeEnum.trans (finCongr (dimension_eq ha hi))

def targetIndex (ha : a ∈ S) (hi : i ∉ S) :
    BoundaryClusterFreeCoordinates.CoordinateIndex i a S m ≃ Fin (GraphForms.dimension n m) :=
  (RealClusterInsertionOrientation.realIndexEquiv ha hi).trans (realIndexEquiv i)

def basisPermutation (ha : a ∈ S) (hi : i ∉ S) :
    Equiv.Perm (BoundaryClusterFreeCoordinates.CoordinateIndex i a S m) :=
  (sourceIndex ha hi).trans (targetIndex ha hi).symm

def physicalInsertion (l u : Fin (m + 1)) (x : BoundaryClusterFreeCoordinates i a S m) :
    GraphForms.Coordinates n m := freeGraph i (insertion l u x)

theorem det_physicalInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    (LinearMap.toMatrix (BoundaryClusterFreeCoordinates.coordinateBasis.reindex (sourceIndex ha hi))
      (GraphForms.realBasis n m) (fderiv ℝ (physicalInsertion l u) x).toLinearMap).det =
      (Equiv.Perm.sign (basisPermutation (m := m) ha hi) : ℝ) *
        x.radius ^ (2 * S.card + (boundaryClusterBlock l u).card - 2) := by
  have h := (freeGraph i).hasFDerivAt.comp x
    (RealClusterInsertionOrientation.differentiableAt_insertion l u x).hasFDerivAt
  change HasFDerivAt (physicalInsertion l u) _ x at h
  rw [h.fderiv]
  change (LinearMap.toMatrix _ _ ((freeGraph i).toLinearMap.comp
    (fderiv ℝ (insertion l u) x).toLinearMap)).det = _
  rw [det_standardMatrix i _ (RealClusterInsertionOrientation.insertionTargetBasis ha hi)
      (sourceIndex ha hi) (targetIndex ha hi) ?_,
    RealClusterInsertionOrientation.det_toMatrix_insertion l u ha hi x]
  · rfl
  intro z j
  rw [targetIndex, Equiv.trans_apply, standard_repr]
  simp [RealClusterInsertionOrientation.insertionTargetBasis]
  rfl

def radialLastBasis : Module.Basis (Fin (faceDimension i a S m + 1)) ℝ
    (BoundaryClusterFreeCoordinates i a S m) :=
  BoundaryClusterFreeCoordinates.coordinateBasis.reindex nativeEnum

def outwardFrame : Fin (faceDimension i a S m + 1) → BoundaryClusterFreeCoordinates i a S m :=
  ClusterOutwardFrame.frame radialLastBasis

theorem det_outwardFrame :
    (radialLastBasis (i := i) (a := a) (S := S) (m := m)).det outwardFrame =
      (-1 : ℝ) ^ (faceDimension i a S m + 1) :=
  ClusterOutwardFrame.basis_det_frame _

@[simp] theorem outwardFrame_zero_radius :
    (outwardFrame (i := i) (a := a) (S := S) (m := m) 0).radius = -1 := by
  simp [outwardFrame, ClusterOutwardFrame.frame_zero, radialLastBasis, nativeEnum,
    ClusterCoordinateOrder.fullEnum_symm_last, ClusterCoordinateOrder.radiusIndex,
    BoundaryClusterFreeCoordinates.coordinateBasis, BoundaryClusterFreeCoordinates.radius]

end Real

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFaceOrientation
