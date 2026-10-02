import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionJacobian

/-! The explicit real-coordinate permutation for the general real-cluster
insertion. Its target basis consists of actual single-coordinate vectors in the
original free-label array. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionOrientation

open RealClusterInsertionCoordinates RealClusterInsertionJacobian

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)}

abbrev FreeRealIndex (i : Fin n) (m : ℕ) := (Σ _ : FreeIndex i, Fin 2) ⊕ Fin m

local instance : DecidableEq (BoundaryClusterFreeCoordinates.CoordinateIndex i a S m) :=
  Classical.decEq _

def freeBasis : Module.Basis (FreeRealIndex i m) ℝ (FreeCoordinates i m) :=
  (Pi.basis (fun _ : FreeIndex i => Complex.basisOneI)).prod (Pi.basisFun ℝ (Fin m))

/-- The full real coordinate permutation. Coarse and shape labels retain their
real/imaginary order, boundaries retain their labels, and center/radius occupy
the real/imaginary slots of the marked anchor label. -/
def realIndexEquiv (ha : a ∈ S) (hi : i ∉ S) :
    BoundaryClusterFreeCoordinates.CoordinateIndex i a S m ≃ FreeRealIndex i m where
  toFun
    | .inl ⟨j, k⟩ => .inl ⟨labelEquiv ha hi (.inl j), k⟩
    | .inr (.inl ⟨j, k⟩) => .inl ⟨labelEquiv ha hi (.inr (.inl j)), k⟩
    | .inr (.inr (.inl j)) => .inr j
    | .inr (.inr (.inr (.inl _))) =>
        .inl ⟨labelEquiv ha hi (.inr (.inr ())), 0⟩
    | .inr (.inr (.inr (.inr _))) =>
        .inl ⟨labelEquiv ha hi (.inr (.inr ())), 1⟩
  invFun
    | .inr j => .inr (.inr (.inl j))
    | .inl ⟨j, k⟩ => match (labelEquiv ha hi).symm j with
      | .inl q => .inl ⟨q, k⟩
      | .inr (.inl q) => .inr (.inl ⟨q, k⟩)
      | .inr (.inr _) => if k = 0 then .inr (.inr (.inr (.inl ())))
          else .inr (.inr (.inr (.inr ())))
  left_inv q := by
    rcases q with ⟨j, k⟩ | ⟨j, k⟩ | j | u | u
    · simp only [Equiv.symm_apply_apply]
    · simp only [Equiv.symm_apply_apply]
    · rfl
    · cases u; simp only [Equiv.symm_apply_apply]; rfl
    · cases u; simp only [Equiv.symm_apply_apply]; rfl
  right_inv q := by
    rcases q with ⟨j, k⟩ | j
    · obtain ⟨j, rfl⟩ := (labelEquiv ha hi).surjective j
      rcases j with j | j | u
      · simp only [Equiv.symm_apply_apply]
      · simp only [Equiv.symm_apply_apply]
      · cases u
        fin_cases k <;> simp only [Equiv.symm_apply_apply] <;> rfl
    · rfl

theorem outputCoordinates_repr (ha : a ∈ S) (hi : i ∉ S) (z : FreeCoordinates i m)
    (q : BoundaryClusterFreeCoordinates.CoordinateIndex i a S m) :
    BoundaryClusterFreeCoordinates.coordinateBasis.repr (outputCoordinates ha hi z) q =
      freeBasis.repr z (realIndexEquiv ha hi q) := by
  rcases q with ⟨j, k⟩ | ⟨j, k⟩ | j | u | u
  · simp [BoundaryClusterFreeCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · simp [BoundaryClusterFreeCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · simp [BoundaryClusterFreeCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates]
  · cases u
    simp [BoundaryClusterFreeCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · cases u
    simp [BoundaryClusterFreeCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]

/-- Actual single-coordinate target basis, in the explicitly displayed order. -/
def insertionTargetBasis (ha : a ∈ S) (hi : i ∉ S) :
    Module.Basis (BoundaryClusterFreeCoordinates.CoordinateIndex i a S m) ℝ (FreeCoordinates i m) :=
  freeBasis.reindex (realIndexEquiv ha hi).symm

theorem insertionTargetBasis_map (ha : a ∈ S) (hi : i ∉ S) :
    (insertionTargetBasis (m := m) ha hi).map
      (outputCoordinates ha hi).toLinearEquiv =
      BoundaryClusterFreeCoordinates.coordinateBasis := by
  apply DFunLike.ext
  intro q
  apply BoundaryClusterFreeCoordinates.coordinateBasis.repr.injective
  ext k
  rw [Module.Basis.map_apply]
  change BoundaryClusterFreeCoordinates.coordinateBasis.repr
    (outputCoordinates ha hi (insertionTargetBasis ha hi q)) k = _
  rw [outputCoordinates_repr]
  simp [insertionTargetBasis, Module.Basis.reindex_apply, Finsupp.single_apply]

theorem toMatrix_outputCoordinates_comp (ha : a ∈ S) (hi : i ∉ S)
    (D : BoundaryClusterFreeCoordinates i a S m →ₗ[ℝ] FreeCoordinates i m) :
    LinearMap.toMatrix BoundaryClusterFreeCoordinates.coordinateBasis
      (insertionTargetBasis ha hi) D =
    LinearMap.toMatrix BoundaryClusterFreeCoordinates.coordinateBasis
      BoundaryClusterFreeCoordinates.coordinateBasis
      ((outputCoordinates ha hi).toLinearMap.comp D) := by
  ext q k
  simp only [LinearMap.toMatrix_apply, insertionTargetBasis, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, LinearMap.comp_apply]
  exact (outputCoordinates_repr ha hi _ q).symm

theorem differentiableAt_insertion (l u : Fin (m + 1))
    (x : BoundaryClusterFreeCoordinates i a S m) :
    DifferentiableAt ℝ (RealClusterInsertionCoordinates.insertion l u) x := by
  have hc := (BoundaryClusterFreeCoordinates.contDiff_radius (i := i) (a := a) (S := S)
    (m := m)).differentiable (by simp)
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr
    intro j
    exact ((BoundaryClusterFreeCoordinates.contDiff_base j.val).differentiable
      (by simp)).differentiableAt.add
      ((Complex.ofRealCLM.differentiableAt.comp x hc.differentiableAt).mul
        ((BoundaryClusterFreeCoordinates.contDiff_velocity j.val).differentiable
          (by simp)).differentiableAt)
  · apply differentiableAt_pi.mpr
    intro j
    exact ((BoundaryClusterFreeCoordinates.contDiff_boundaryBase l u j).differentiable
      (by simp)).differentiableAt.add (hc.differentiableAt.mul
      ((BoundaryClusterFreeCoordinates.contDiff_boundaryVelocity l u j).differentiable
        (by simp)).differentiableAt)

/-- The native insertion's actual real matrix, with its explicit target-label
permutation, has the computed oriented determinant. -/
theorem det_toMatrix_insertion (l u : Fin (m + 1)) (ha : a ∈ S) (hi : i ∉ S)
    (x : BoundaryClusterFreeCoordinates i a S m) :
    (LinearMap.toMatrix BoundaryClusterFreeCoordinates.coordinateBasis
      (insertionTargetBasis ha hi)
      (fderiv ℝ (RealClusterInsertionCoordinates.insertion l u) x).toLinearMap).det =
      x.radius ^ (2 * S.card + (boundaryClusterBlock l u).card - 2) := by
  rw [toMatrix_outputCoordinates_comp, LinearMap.det_toMatrix]
  have h := (outputCoordinates ha hi).hasFDerivAt.comp x
    (differentiableAt_insertion l u x).hasFDerivAt
  have he := h.fderiv
  change fderiv ℝ (groupedInsertion l u ha hi) x = _ at he
  rw [← det_fderiv_groupedInsertion l u ha hi x, he]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionOrientation
