import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionJacobian

/-! The explicit real-coordinate permutation for the general interior-cluster
insertion. Its target basis consists of actual single-coordinate vectors in the
original free-label array. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionOrientation

open InteriorClusterInsertionCoordinates InteriorClusterInsertionJacobian

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev FreeRealIndex (i : Fin n) (m : ℕ) := (Σ _ : FreeIndex i, Fin 2) ⊕ Fin m

local instance : DecidableEq (ClusterAngularCoordinates.CoordinateIndex i a b S m) :=
  Classical.decEq _

def freeBasis : Module.Basis (FreeRealIndex i m) ℝ (FreeCoordinates i m) :=
  (Pi.basis (fun _ : FreeIndex i => Complex.basisOneI)).prod (Pi.basisFun ℝ (Fin m))

/-- The full real coordinate permutation. Coarse and shape labels retain their
real/imaginary order, boundaries retain their labels, and angle/radius occupy
the real/imaginary slots of the marked reference label. -/
def realIndexEquiv (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    ClusterAngularCoordinates.CoordinateIndex i a b S m ≃ FreeRealIndex i m where
  toFun
    | .inl ⟨j, k⟩ => .inl ⟨labelEquiv hb hba hanchor (.inl j), k⟩
    | .inr (.inl ⟨j, k⟩) => .inl ⟨labelEquiv hb hba hanchor (.inr (.inl j)), k⟩
    | .inr (.inr (.inl j)) => .inr j
    | .inr (.inr (.inr (.inl _))) =>
        .inl ⟨labelEquiv hb hba hanchor (.inr (.inr ())), 0⟩
    | .inr (.inr (.inr (.inr _))) =>
        .inl ⟨labelEquiv hb hba hanchor (.inr (.inr ())), 1⟩
  invFun
    | .inr j => .inr (.inr (.inl j))
    | .inl ⟨j, k⟩ => match (labelEquiv hb hba hanchor).symm j with
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
    · obtain ⟨j, rfl⟩ := (labelEquiv hb hba hanchor).surjective j
      rcases j with j | j | u
      · simp only [Equiv.symm_apply_apply]
      · simp only [Equiv.symm_apply_apply]
      · cases u
        fin_cases k <;> simp only [Equiv.symm_apply_apply] <;> rfl
    · rfl

theorem outputCoordinates_repr (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (z : FreeCoordinates i m)
    (q : ClusterAngularCoordinates.CoordinateIndex i a b S m) :
    ClusterAngularCoordinates.coordinateBasis.repr (outputCoordinates hb hba hanchor z) q =
      freeBasis.repr z (realIndexEquiv hb hba hanchor q) := by
  rcases q with ⟨j, k⟩ | ⟨j, k⟩ | j | u | u
  · simp [ClusterAngularCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · simp [ClusterAngularCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · simp [ClusterAngularCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates]
  · cases u
    simp [ClusterAngularCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]
  · cases u
    simp [ClusterAngularCoordinates.coordinateBasis, freeBasis, realIndexEquiv,
      outputCoordinates, Pi.basis_repr]

/-- Actual single-coordinate target basis, in the explicitly displayed order. -/
def insertionTargetBasis (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Module.Basis (ClusterAngularCoordinates.CoordinateIndex i a b S m) ℝ (FreeCoordinates i m) :=
  freeBasis.reindex (realIndexEquiv hb hba hanchor).symm

theorem insertionTargetBasis_map (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    (insertionTargetBasis (m := m) hb hba hanchor).map
      (outputCoordinates hb hba hanchor).toLinearEquiv =
      ClusterAngularCoordinates.coordinateBasis := by
  apply DFunLike.ext
  intro q
  apply ClusterAngularCoordinates.coordinateBasis.repr.injective
  ext k
  rw [Module.Basis.map_apply]
  change ClusterAngularCoordinates.coordinateBasis.repr
    (outputCoordinates hb hba hanchor (insertionTargetBasis hb hba hanchor q)) k = _
  rw [outputCoordinates_repr]
  simp [insertionTargetBasis, Module.Basis.reindex_apply, Finsupp.single_apply]

theorem toMatrix_outputCoordinates_comp (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i)
    (D : ClusterAngularCoordinates i a b S m →ₗ[ℝ] FreeCoordinates i m) :
    LinearMap.toMatrix ClusterAngularCoordinates.coordinateBasis
      (insertionTargetBasis hb hba hanchor) D =
    LinearMap.toMatrix ClusterAngularCoordinates.coordinateBasis
      ClusterAngularCoordinates.coordinateBasis
      ((outputCoordinates hb hba hanchor).toLinearMap.comp D) := by
  ext q k
  simp only [LinearMap.toMatrix_apply, insertionTargetBasis, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, LinearMap.comp_apply]
  exact (outputCoordinates_repr hb hba hanchor _ q).symm

theorem differentiableAt_insertion (x : ClusterAngularCoordinates i a b S m) :
    DifferentiableAt ℝ (InteriorClusterInsertionCoordinates.insertion) x := by
  apply DifferentiableAt.prodMk
  · exact differentiableAt_pi.mpr fun j =>
      ((ClusterAngularCoordinates.contDiff_position (i := i) (a := a) (b := b) (S := S)
        (m := m) j.val).differentiable (by simp)).differentiableAt
  · fun_prop

/-- The native insertion's actual real matrix, with its explicit target-label
permutation, has the computed oriented determinant. -/
theorem det_toMatrix_insertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularCoordinates i a b S m) :
    (LinearMap.toMatrix ClusterAngularCoordinates.coordinateBasis
      (insertionTargetBasis hb hba hanchor)
      (fderiv ℝ InteriorClusterInsertionCoordinates.insertion x).toLinearMap).det =
      -x.2.2.2.2 ^ (2 * S.card - 3) := by
  rw [toMatrix_outputCoordinates_comp, LinearMap.det_toMatrix]
  have h := (outputCoordinates hb hba hanchor).hasFDerivAt.comp x
    (differentiableAt_insertion x).hasFDerivAt
  have he := h.fderiv
  change fderiv ℝ (groupedInsertion hb hba hanchor) x = _ at he
  rw [← det_fderiv_groupedInsertion ha hb hba hanchor x, he]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionOrientation
