import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterInsertionOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterInsertionOrientation

/-! Actual standard graph coordinates for an original label array with an
arbitrary fixed anchor omitted. The indexing uses `Fin.succAbove`. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterStandardCoordinates

open InteriorClusterInsertionCoordinates

variable {n m : ℕ}

def freeGraph (i : Fin (n + 1)) : FreeCoordinates i m ≃L[ℝ] GraphForms.Coordinates n m :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun z => (fun j => z.1 (finSuccAboveEquiv i j), z.2)
    invFun := fun z => (fun j => z.1 ((finSuccAboveEquiv i).symm j), z.2)
    left_inv := by intro z; simp
    right_inv := by intro z; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem freeGraph_apply (i : Fin (n + 1)) (z : FreeCoordinates i m) :
    freeGraph i z = (fun j => z.1 (finSuccAboveEquiv i j), z.2) := rfl

def realIndexEquiv (i : Fin (n + 1)) :
    InteriorClusterInsertionOrientation.FreeRealIndex i m ≃ Fin (GraphForms.dimension n m) :=
  (Equiv.sumCongr
    ((Equiv.sigmaEquivProd (FreeIndex i) (Fin 2)).trans
      (Equiv.prodCongr (finSuccAboveEquiv i).symm (Equiv.refl (Fin 2))))
    (Equiv.refl (Fin m))).trans (GraphForms.coordinateIndexEquiv n m)

/-- Each actual standard graph coordinate is the stated original-label real coordinate. -/
theorem standard_repr (i : Fin (n + 1)) (z : FreeCoordinates i m)
    (q : InteriorClusterInsertionOrientation.FreeRealIndex i m) :
    (GraphForms.realBasis n m).repr (freeGraph i z) (realIndexEquiv i q) =
      InteriorClusterInsertionOrientation.freeBasis.repr z q := by
  rcases q with ⟨j, k⟩ | j
  · change GraphForms.realCoordinates n m (freeGraph i z)
      (GraphForms.coordinateIndexEquiv n m (.inl ((finSuccAboveEquiv i).symm j, k))) = _
    rw [GraphForms.realCoordinates_internal]
    simp [freeGraph_apply, InteriorClusterInsertionOrientation.freeBasis, Pi.basis_repr]
  · change GraphForms.realCoordinates n m (freeGraph i z)
      (GraphForms.externalBasisIndex n j) = _
    rw [GraphForms.realCoordinates_external]
    simp [InteriorClusterInsertionOrientation.freeBasis]

theorem freeBasis_map (i : Fin (n + 1)) :
    ((InteriorClusterInsertionOrientation.freeBasis (i := i) (m := m)).map
      (freeGraph i).toLinearEquiv).reindex (realIndexEquiv i) = GraphForms.realBasis n m := by
  apply Module.Basis.eq_ofRepr_eq_repr
  intro z q
  obtain ⟨q, rfl⟩ := (realIndexEquiv i).surjective q
  simp only [Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_apply_apply, Module.Basis.map_repr]
  change InteriorClusterInsertionOrientation.freeBasis.repr ((freeGraph i).symm z) q = _
  have h := standard_repr i ((freeGraph i).symm z) q
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterStandardCoordinates
