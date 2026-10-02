import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterRadialJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeJacobian

/-! Actual real-cluster insertion determinant in the native free coordinates.
The boundary entries retain their original label order; a diagonal mask scales
exactly the entries belonging to the cluster. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionJacobian

open Configuration RealClusterInsertionCoordinates

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)}

abbrev Block (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (BoundaryClusterCoarseIndex i S → ℂ) × (BoundaryClusterShapeIndex a S → ℂ) × (Fin m → ℝ)

abbrev BlockIndex (i a : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (Σ _ : BoundaryClusterCoarseIndex i S, Fin 2) ⊕
    (Σ _ : BoundaryClusterShapeIndex a S, Fin 2) ⊕ Fin m

local instance : DecidableEq (BlockIndex i a S m) := Classical.decEq _

def blockBasis : Module.Basis (BlockIndex i a S m) ℝ (Block i a S m) :=
  (Pi.basis (fun _ : BoundaryClusterCoarseIndex i S => Complex.basisOneI)).prod
    ((Pi.basis (fun _ : BoundaryClusterShapeIndex a S => Complex.basisOneI)).prod
      (Pi.basisFun ℝ (Fin m)))

def blockCoordinates : Block i a S m ≃L[ℝ] (BlockIndex i a S m → ℝ) := blockBasis.equivFunL

@[simp] theorem blockCoordinates_coarse (z : Block i a S m)
    (j : BoundaryClusterCoarseIndex i S) (k : Fin 2) :
    blockCoordinates z (.inl ⟨j, k⟩) = Complex.basisOneI.repr (z.1 j) k := by
  simp [blockCoordinates, blockBasis, Pi.basis_repr]

@[simp] theorem blockCoordinates_shape (z : Block i a S m)
    (j : BoundaryClusterShapeIndex a S) (k : Fin 2) :
    blockCoordinates z (.inr (.inl ⟨j, k⟩)) = Complex.basisOneI.repr (z.2.1 j) k := by
  simp [blockCoordinates, blockBasis, Pi.basis_repr]

@[simp] theorem blockCoordinates_boundary (z : Block i a S m) (j : Fin m) :
    blockCoordinates z (.inr (.inr j)) = z.2.2 j := by
  simp [blockCoordinates, blockBasis]

def splitCoordinates : BoundaryClusterFreeCoordinates i a S m ≃L[ℝ]
    RealClusterRadialJacobian.Space (BlockIndex i a S m) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => (blockCoordinates (x.1, x.2.1, x.2.2.1), x.2.2.2)
    invFun := fun p =>
      ((blockCoordinates.symm p.1).1, (blockCoordinates.symm p.1).2.1,
        (blockCoordinates.symm p.1).2.2, p.2)
    left_inv := by intro x; simp
    right_inv := by intro p; simp
    map_add' := by
      intro x y
      apply Prod.ext
      · exact map_add (blockCoordinates (i := i) (a := a) (S := S) (m := m))
          (x.1, x.2.1, x.2.2.1) (y.1, y.2.1, y.2.2.1)
      · rfl
    map_smul' := by
      intro r x
      apply Prod.ext
      · exact map_smul (blockCoordinates (i := i) (a := a) (S := S) (m := m)) r
          (x.1, x.2.1, x.2.2.1)
      · rfl }

@[simp] theorem splitCoordinates_apply (x : BoundaryClusterFreeCoordinates i a S m) :
    splitCoordinates x = (blockCoordinates (x.1, x.2.1, x.2.2.1), x.2.2.2) := rfl

def activeIndices (T : Finset (Fin m)) : Finset (BlockIndex i a S m) :=
  Finset.disjSum ∅ (Finset.disjSum Finset.univ T)

def shiftMask (T : Finset (Fin m)) : BlockIndex i a S m → ℝ
  | .inl _ => 0
  | .inr (.inl ⟨_, k⟩) => if k = 0 then 1 else 0
  | .inr (.inr j) => if j ∈ T then 1 else 0

theorem card_activeIndices (T : Finset (Fin m)) (ha : a ∈ S) :
    (activeIndices (i := i) (a := a) (S := S) T).card = 2 * S.card + T.card - 2 := by
  have hs : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, ha⟩
  simp only [activeIndices, Finset.card_disjSum, Finset.card_empty, Finset.card_univ,
    Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, smul_eq_mul,
    card_boundaryClusterShapeIndex a S ha]
  omega

def groupedInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S) :
    BoundaryClusterFreeCoordinates i a S m → BoundaryClusterFreeCoordinates i a S m :=
  outputCoordinates ha hi ∘ RealClusterInsertionCoordinates.insertion l u

theorem split_groupedInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    splitCoordinates (groupedInsertion l u ha hi x) =
      RealClusterRadialJacobian.insertion (activeIndices (boundaryClusterBlock l u))
        (shiftMask (boundaryClusterBlock l u)) (splitCoordinates x) := by
  change splitCoordinates (outputCoordinates ha hi (RealClusterInsertionCoordinates.insertion l u x)) = _
  rw [outputCoordinates_insertion]
  apply Prod.ext
  · funext q
    rcases q with ⟨j, k⟩ | ⟨j, k⟩ | j
    · simp only [splitCoordinates_apply, RealClusterRadialJacobian.insertion,
        blockCoordinates_coarse, shiftMask, activeIndices, Finset.inl_mem_disjSum,
        Finset.notMem_empty, if_false, zero_mul, one_mul, zero_add]
    · fin_cases k <;>
        simp [splitCoordinates_apply, RealClusterRadialJacobian.insertion,
          shiftMask, activeIndices, BoundaryClusterFreeCoordinates.center,
          BoundaryClusterFreeCoordinates.radius]
    · by_cases hj : j ∈ boundaryClusterBlock l u
      · simp only [splitCoordinates_apply, RealClusterRadialJacobian.insertion,
          blockCoordinates_boundary, shiftMask, activeIndices, Finset.inr_mem_disjSum,
          if_pos hj, one_mul]
        rfl
      · simp only [splitCoordinates_apply, RealClusterRadialJacobian.insertion,
          blockCoordinates_boundary, shiftMask, activeIndices, Finset.inr_mem_disjSum,
          if_neg hj, zero_mul, one_mul, zero_add]
  · rfl

theorem differentiableAt_groupedInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    DifferentiableAt ℝ (groupedInsertion l u ha hi) x := by
  have hfun : groupedInsertion l u ha hi = fun y => splitCoordinates.symm
      (RealClusterRadialJacobian.insertion (activeIndices (boundaryClusterBlock l u))
        (shiftMask (boundaryClusterBlock l u)) (splitCoordinates y)) := by
    funext y
    apply splitCoordinates.injective
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using split_groupedInsertion l u ha hi y
  rw [hfun]
  exact splitCoordinates.symm.differentiableAt.comp x
    ((RealClusterRadialJacobian.hasFDerivAt_insertion _ _ (splitCoordinates x)).differentiableAt.comp x
      splitCoordinates.differentiableAt)

/-- Exact positive-sign radial power for the genuine native insertion. -/
theorem det_fderiv_groupedInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    LinearMap.det (fderiv ℝ (groupedInsertion l u ha hi) x).toLinearMap =
      x.radius ^ (2 * S.card + (boundaryClusterBlock l u).card - 2) := by
  have hfun : (fun p => splitCoordinates (groupedInsertion l u ha hi (splitCoordinates.symm p))) =
      RealClusterRadialJacobian.insertion (activeIndices (boundaryClusterBlock l u))
        (shiftMask (i := i) (a := a) (S := S) (boundaryClusterBlock l u)) := by
    funext p
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      split_groupedInsertion l u ha hi (splitCoordinates.symm p)
  rw [← GraphForms.det_fderiv_linearConjugate splitCoordinates _ x
      (differentiableAt_groupedInsertion l u ha hi x), hfun,
    RealClusterRadialJacobian.det_fderiv_insertion, card_activeIndices _ ha]
  rfl

theorem det_fderiv_groupedInsertion_pos (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) (hr : 0 < x.radius) :
    0 < LinearMap.det (fderiv ℝ (groupedInsertion l u ha hi) x).toLinearMap := by
  rw [det_fderiv_groupedInsertion l u ha hi]
  exact pow_pos hr _

theorem abs_det_fderiv_groupedInsertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) (hr : 0 < x.radius) :
    |LinearMap.det (fderiv ℝ (groupedInsertion l u ha hi) x).toLinearMap| =
      x.radius ^ (2 * S.card + (boundaryClusterBlock l u).card - 2) := by
  rw [abs_of_pos (det_fderiv_groupedInsertion_pos l u ha hi x hr),
    det_fderiv_groupedInsertion l u ha hi]

end EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionJacobian
