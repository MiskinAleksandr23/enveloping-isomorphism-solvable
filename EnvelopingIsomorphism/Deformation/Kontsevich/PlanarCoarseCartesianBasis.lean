import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian

/-! Exact images of the standard Cartesian basis in the original angular,
interleaved complex, and coarse graph frames. No orientation is discarded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian
open BoxStokes InteriorFiberAngleSplit
open scoped Classical

@[simp] theorem split_fst (A B : ℕ) (y : Coord (A + B)) (j : Fin A) :
    (split A B y).1 j = y (finSumFinEquiv (Sum.inl j)) := rfl
@[simp] theorem split_snd (A B : ℕ) (y : Coord (A + B)) (j : Fin B) :
    (split A B y).2 j = y (finSumFinEquiv (Sum.inr j)) := rfl

@[simp] theorem complex_re (N : ℕ) (y : Coord (N * 2)) (j : Fin N) :
    (complex N y j).re = y (finProdFinEquiv (j, 0)) := rfl
@[simp] theorem complex_im (N : ℕ) (y : Coord (N * 2)) (j : Fin N) :
    (complex N y j).im = y (finProdFinEquiv (j, 1)) := rfl

theorem complex_coordinates (N : ℕ) (y : Coord (N * 2)) :
    (AngularRadial.realBasis N).equivFun (complex N y) = y := by
  funext k
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases k <;> simp [AngularRadial.realBasis, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Pi.basis_repr]

@[simp] theorem complex_standardBasis (N : ℕ) (j : Fin (N * 2)) :
    complex N (standardBasis (N * 2) j) = AngularRadial.realBasis N j := by
  apply (AngularRadial.realBasis N).equivFun.injective
  rw [complex_coordinates]
  simp only [standardBasis, Module.Basis.equivFun_apply, Module.Basis.repr_self]
  ext k
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

@[simp] theorem split_standardBasis_inl (A B : ℕ) (j : Fin A) :
    split A B (standardBasis (A + B) (finSumFinEquiv (Sum.inl j))) = (standardBasis A j, 0) := by
  apply Prod.ext
  · funext k
    simp [standardBasis, Pi.single_apply, Fin.ext_iff] <;> omega
  · funext k
    simp [standardBasis, Pi.single_apply, Fin.ext_iff] <;> omega

@[simp] theorem split_standardBasis_inr (A B : ℕ) (j : Fin B) :
    split A B (standardBasis (A + B) (finSumFinEquiv (Sum.inr j))) = (0, standardBasis B j) := by
  apply Prod.ext
  · funext k
    simp [standardBasis, Pi.single_apply, Fin.ext_iff] <;> omega
  · funext k
    simp [standardBasis, Pi.single_apply, Fin.ext_iff] <;> omega

/-- Only the displayed sum order changes; every index value is retained. -/
def shapeIndex (N : ℕ) : Fin (InteriorFiberAngleSplit.Dim N + 1) ≃ Fin (1 + N * 2) :=
  finCongr (by dsimp [InteriorFiberAngleSplit.Dim, AngularRadial.realDimension]; omega)

theorem shape_standardBasis (N : ℕ) (j : Fin (InteriorFiberAngleSplit.Dim N + 1)) :
    shape N (standardBasis (1 + N * 2) (shapeIndex N j)) = fiberFrame N j := by
  cases j using Fin.cases with
  | zero =>
    have hi : shapeIndex N 0 = finSumFinEquiv (Sum.inl (0 : Fin 1)) := by apply Fin.ext; rfl
    rw [hi, shape, ContinuousLinearEquiv.trans_apply, split_standardBasis_inl]
    apply Prod.ext
    · rfl
    · change complex N 0 = 0
      exact (complex N).map_zero
  | succ j =>
    have hi : shapeIndex N j.succ = finSumFinEquiv (Sum.inr j) := by apply Fin.ext; simp [shapeIndex]; omega
    rw [hi, shape, ContinuousLinearEquiv.trans_apply, split_standardBasis_inr]
    apply Prod.ext
    · rfl
    · exact complex_standardBasis N j

theorem coarse_standardBasis (M m : ℕ) (j : Fin (M * 2 + m)) :
    coarse M m (standardBasis (M * 2 + m) j) = GraphForms.realBasis M m j := by
  obtain ⟨j, rfl⟩ := (GraphForms.coordinateIndexEquiv M m).surjective j
  cases j with
  | inl j =>
    rcases j with ⟨j, k⟩
    rw [GraphForms.realBasis_internal]
    change coarse M m (standardBasis _ (finSumFinEquiv (Sum.inl (finProdFinEquiv (j, k))))) = _
    rw [coarse, ContinuousLinearEquiv.trans_apply, split_standardBasis_inl]
    apply Prod.ext
    · change complex M (standardBasis _ (finProdFinEquiv (j, k))) = Pi.single j (Complex.basisOneI k)
      rw [complex_standardBasis]
      simp [AngularRadial.realBasis, Module.Basis.reindex_apply, Pi.basis_apply]
    · rfl
  | inr j =>
    rw [show GraphForms.realBasis M m (GraphForms.coordinateIndexEquiv M m (.inr j)) =
      GraphForms.externalTangent j from GraphForms.realBasis_external j]
    change coarse M m (standardBasis _ (finSumFinEquiv (Sum.inr j))) = _
    rw [coarse, ContinuousLinearEquiv.trans_apply, split_standardBasis_inr]
    apply Prod.ext
    · change complex M 0 = 0
      exact (complex M).map_zero
    · rfl

def productIndex (N M m : ℕ) :
    Fin ((InteriorFiberAngleSplit.Dim N + 1) + GraphForms.dimension M m) ≃ Fin (Dim N M m) :=
  finCongr (by dsimp [InteriorFiberAngleSplit.Dim, AngularRadial.realDimension, GraphForms.dimension, Dim]; omega)

/-- Exact ordered product frame: angle first, shape 1,I pairs, coarse 1,I pairs,
then boundary coordinates, with no hidden determinant or measure factor. -/
theorem cartesian_standardBasis (N M m : ℕ)
    (j : Fin ((InteriorFiberAngleSplit.Dim N + 1) + GraphForms.dimension M m)) :
    cartesian N M m (standardBasis (Dim N M m) (productIndex N M m j)) =
      GraphFormProduct.productVectors (fiberFrame N) (GraphForms.realBasis M m) j := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    have he : productIndex N M m (finSumFinEquiv (Sum.inl j)) =
        finSumFinEquiv (Sum.inl (shapeIndex N j)) := by apply Fin.ext; rfl
    rw [he, cartesian, ContinuousLinearEquiv.trans_apply, split_standardBasis_inl]
    simp only [GraphFormProduct.productVectors, Equiv.symm_apply_apply, Sum.elim_inl]
    change (shape N (standardBasis _ (shapeIndex N j)), coarse M m 0) = _
    rw [shape_standardBasis, map_zero]
  | inr j =>
    have he : productIndex N M m (finSumFinEquiv (Sum.inr j)) = finSumFinEquiv (Sum.inr j) := by
      apply Fin.ext
      simp [productIndex, InteriorFiberAngleSplit.Dim, AngularRadial.realDimension]
    rw [he, cartesian, ContinuousLinearEquiv.trans_apply, split_standardBasis_inr]
    simp only [GraphFormProduct.productVectors, Equiv.symm_apply_apply, Sum.elim_inr]
    change (shape N 0, coarse M m (standardBasis _ j)) = _
    rw [coarse_standardBasis, map_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian
