import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Option

/-! A finite monomial with distinct selected pole coordinates has at most one
factor in each coordinate. The resulting product has the all-coordinate simple-pole bound.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped BigOperators

variable {I J : Type*}

/-- No two slots select the same pole coordinate. Slots selecting none may repeat. -/
def PoleDistinct (ε : I → Option J) : Prop :=
  ∀ i j ν, ε i = some ν → ε j = some ν → i = j

variable [Fintype I] [Fintype J]

/-- The actual finite set of pole coordinates that occur in the selection. -/
def usedPoles (ε : I → Option J) : Finset J := by
  classical
  exact Finset.univ.filter (fun ν ↦ ∃ i, ε i = some ν)

@[simp] theorem mem_usedPoles (ε : I → Option J) (ν : J) :
    ν ∈ usedPoles ε ↔ ∃ i, ε i = some ν := by
  classical
  simp [usedPoles]

/-- Reindex the actual product by its used coordinates, using distinctness only for nonempty choices. -/
theorem prod_option_eq_prod_usedPoles {M : Type*} [CommMonoid M]
    (ε : I → Option J) (hε : PoleDistinct ε) (t : J → M) :
    (∏ i : I, (ε i).elim 1 t) = ∏ ν ∈ usedPoles ε, t ν := by
  classical
  let S := Finset.univ.filter (fun i : I ↦ (ε i).isSome)
  let pick (i : I) (hi : i ∈ S) : J := (ε i).get (Finset.mem_filter.mp hi).2
  have hpick (i : I) (hi : i ∈ S) : ε i = some (pick i hi) := (Option.some_get _).symm
  calc
    _ = ∏ i ∈ S, (ε i).elim 1 t := by
      symm
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro i hi hnot
      have hn : ¬(ε i).isSome := by
        intro hs
        exact hnot (Finset.mem_filter.mpr ⟨hi, hs⟩)
      rw [Option.not_isSome_iff_eq_none.mp hn]
      rfl
    _ = _ := by
      apply Finset.prod_bij pick
      · intro i hi
        exact (mem_usedPoles ε _).mpr ⟨i, hpick i hi⟩
      · intro i hi j hj hij
        exact hε i j _ (hpick i hi) ((hpick j hj).trans (congrArg some hij.symm))
      · intro ν hν
        obtain ⟨i, hi⟩ := (mem_usedPoles ε ν).mp hν
        have his : i ∈ S := by simp [S, hi]
        exact ⟨i, his, Option.some.inj ((hpick i his).symm.trans hi)⟩
      · intro i hi
        rw [hpick i hi]
        rfl

/-- Every distinct-coordinate monomial is bounded by the full simple-pole majorant. -/
theorem prod_option_le_prod_max_one (ε : I → Option J) (hε : PoleDistinct ε)
    (t : J → ℝ) (ht : ∀ ν, 0 ≤ t ν) :
    (∏ i : I, (ε i).elim 1 t) ≤ ∏ ν : J, max 1 (t ν) := by
  rw [prod_option_eq_prod_usedPoles ε hε t]
  calc
    _ ≤ ∏ ν ∈ usedPoles ε, max 1 (t ν) :=
      Finset.prod_le_prod (fun ν _ ↦ ht ν) (fun ν _ ↦ le_max_right _ _)
    _ ≤ _ :=
      Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
        (fun ν _ ↦ zero_le_one.trans (le_max_left _ _)) (fun ν _ _ ↦ le_max_left _ _)

end EnvelopingIsomorphism.Deformation.Kontsevich
