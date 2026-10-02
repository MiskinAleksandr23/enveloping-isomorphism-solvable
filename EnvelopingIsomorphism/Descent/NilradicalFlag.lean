import EnvelopingIsomorphism.Lie.NilradicalBaseChange
import EnvelopingIsomorphism.Identification.IdealFiltration
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The nilradical flag in adapted coordinates after arbitrary characteristic-zero
field extension. Filtration preservation is proved from A4 and characteristicity. -/

namespace EnvelopingIsomorphism.Descent

open Module
open EnvelopingIsomorphism.Lie EnvelopingIsomorphism.Identification
open scoped TensorProduct

noncomputable section

variable {k L M : Type*} [Field k] [LieRing L] [LieAlgebra k L]
variable [LieRing M] [LieAlgebra k M]

theorem map_lowerCentralSeriesOfIdeal (e : L ≃ₗ⁅k⁆ M) (N : LieIdeal k L) (d : ℕ) :
    (lowerCentralSeriesOfIdeal N d).map e.toLieHom =
      lowerCentralSeriesOfIdeal (N.map e.toLieHom) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [lowerCentralSeriesOfIdeal_succ, LieIdeal.map_bracket_eq e.toLieHom e.surjective,
      ih, lowerCentralSeriesOfIdeal_succ]

theorem map_nilradical_lowerCentralFiltration (e : L ≃ₗ⁅k⁆ M) (d : ℕ) :
    (lowerCentralFiltration (nilradical k L) d).map e.toLieHom =
      lowerCentralFiltration (nilradical k M) d := by
  cases d with
  | zero =>
    simp only [lowerCentralFiltration_zero]
    apply le_antisymm le_top
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact LieIdeal.mem_map (show x ∈ (⊤ : LieIdeal k L) from trivial)
  | succ d =>
    simp only [lowerCentralFiltration_succ, map_lowerCentralSeriesOfIdeal, map_nilradical]

theorem mem_nilradical_lowerCentralFiltration_map (e : L ≃ₗ⁅k⁆ M) (d : ℕ)
    {x : L} (hx : x ∈ lowerCentralFiltration (nilradical k L) d) :
    e x ∈ lowerCentralFiltration (nilradical k M) d := by
  rw [← map_nilradical_lowerCentralFiltration e d]
  exact LieIdeal.mem_map hx

section BaseChange

variable [CharZero k] [Module.Finite k L]
variable (K : Type*) [Field K] [Algebra k K]

theorem nilradical_lowerCentralFiltration_baseChange (d : ℕ) :
    (lowerCentralFiltration (nilradical k L) d).baseChange K =
      lowerCentralFiltration (nilradical K (K ⊗[k] L)) d := by
  cases d with
  | zero => simp only [lowerCentralFiltration_zero, LieSubmodule.baseChange_top]
  | succ d =>
    simpa only [lowerCentralFiltration_succ] using nilradical_lowerCentralSeries_baseChange K d

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original adapted coordinates remain nilradical-adapted after scalar extension.
This uses the proved nilradical base-change theorem, including transcendental extensions. -/
theorem adapted_nilradical_basis_baseChange
    (b : Basis ι k L) (weight : ι → ℕ)
    (hadapted : ∀ d, Submodule.span k (b '' {i | d ≤ weight i}) =
      (lowerCentralFiltration (nilradical k L) d).toSubmodule) (d : ℕ) :
    Submodule.span K (b.baseChange K '' {i | d ≤ weight i}) =
      (lowerCentralFiltration (nilradical K (K ⊗[k] L)) d).toSubmodule := by
  rw [← nilradical_lowerCentralFiltration_baseChange K d]
  change _ = (lowerCentralFiltration (nilradical k L) d).toSubmodule.baseChange K
  rw [← hadapted, Submodule.baseChange_span]
  congr 1
  rw [Set.image_image]
  congr 1
  funext i
  exact Basis.baseChange_apply _ _ _

variable [Module.Finite k M]

/-- A Lie equivalence of scalar-extended algebras is block triangular in any
nilradical-adapted bases. No filtration-preservation premise is used. -/
theorem coefficient_eq_zero_of_lt_weight
    (bL : Basis ι k L) (bM : Basis ι k M) (weight : ι → ℕ)
    (hL : ∀ d, Submodule.span k (bL '' {i | d ≤ weight i}) =
      (lowerCentralFiltration (nilradical k L) d).toSubmodule)
    (hM : ∀ d, Submodule.span k (bM '' {i | d ≤ weight i}) =
      (lowerCentralFiltration (nilradical k M) d).toSubmodule)
    (f : (K ⊗[k] L) ≃ₗ⁅K⁆ (K ⊗[k] M)) (r i : ι)
    (hri : weight r < weight i) :
    (bM.baseChange K).repr (f (bL.baseChange K i)) r = 0 := by
  have hx : bL.baseChange K i ∈ lowerCentralFiltration
      (nilradical K (K ⊗[k] L)) (weight i) := by
    change bL.baseChange K i ∈
      (lowerCentralFiltration (nilradical K (K ⊗[k] L)) (weight i)).toSubmodule
    rw [← adapted_nilradical_basis_baseChange K bL weight hL]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have hy := mem_nilradical_lowerCentralFiltration_map f (weight i) hx
  have hy' : f (bL.baseChange K i) ∈
      Submodule.span K (bM.baseChange K '' {j | weight i ≤ weight j}) := by
    rw [adapted_nilradical_basis_baseChange K bM weight hM]
    exact hy
  by_contra hne
  have hs := (bM.baseChange K).repr_support_subset_of_mem_span _ hy'
  exact (not_le_of_gt hri) (hs (Finsupp.mem_support_iff.mpr hne))

end BaseChange

end

end EnvelopingIsomorphism.Descent
