import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exact dimension vanishing for determinant products of two pulled blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
open ContinuousAlternatingMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {r s : ℕ}

/-- A nonzero full determinant forces each actual block to fit its factor dimension. -/
theorem productCovectors_card_le (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (v : Fin (r + s) → E × F)
    (hn : ofCovectors (productCovectors α β) v ≠ 0) :
    r ≤ Module.finrank ℝ E ∧ s ≤ Module.finrank ℝ F := by
  have hlin := Matrix.linearIndependent_cols_of_det_ne_zero hn
  let evalE : Module.Dual ℝ E →ₗ[ℝ] (Fin (r + s) → ℝ) :=
    { toFun := fun l k ↦ l (v k).1
      map_add' := fun l q ↦ rfl
      map_smul' := fun c l ↦ rfl }
  let evalF : Module.Dual ℝ F →ₗ[ℝ] (Fin (r + s) → ℝ) :=
    { toFun := fun l k ↦ l (v k).2
      map_add' := fun l q ↦ rfl
      map_smul' := fun c l ↦ rfl }
  have hleft := hlin.comp (fun j : Fin r ↦ finSumFinEquiv (Sum.inl j))
    (finSumFinEquiv.injective.comp Sum.inl_injective)
  have hright := hlin.comp (fun j : Fin s ↦ finSumFinEquiv (Sum.inr j))
    (finSumFinEquiv.injective.comp Sum.inr_injective)
  have he : LinearIndependent ℝ (fun j ↦ (α j).toLinearMap) := by
    apply LinearIndependent.of_comp evalE
    convert hleft using 1 <;> try rfl
    funext j k
    simp [evalE, Matrix.col, productCovectors, Function.comp_def]
  have hf : LinearIndependent ℝ (fun j ↦ (β j).toLinearMap) := by
    apply LinearIndependent.of_comp evalF
    convert hright using 1 <;> try rfl
    funext j k
    simp [evalF, Matrix.col, productCovectors, Function.comp_def]
  exact ⟨by simpa only [Fintype.card_fin, Subspace.dual_finrank_eq] using he.fintype_card_le_finrank,
    by simpa only [Fintype.card_fin, Subspace.dual_finrank_eq] using hf.fintype_card_le_finrank⟩

/-- At full face degree, any mismatch in the internal edge count kills the
whole alternating form, not merely one chosen evaluation. -/
theorem form_product_eq_zero_of_dimension_mismatch
    (α : Fin r → E →L[ℝ] ℝ) (β : Fin s → F →L[ℝ] ℝ)
    (htotal : r + s = Module.finrank ℝ E + Module.finrank ℝ F)
    (hr : r ≠ Module.finrank ℝ E) : ofCovectors (productCovectors α β) = 0 := by
  ext v
  change ofCovectors (productCovectors α β) v = 0
  by_contra hn
  have h := productCovectors_card_le α β v hn
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
