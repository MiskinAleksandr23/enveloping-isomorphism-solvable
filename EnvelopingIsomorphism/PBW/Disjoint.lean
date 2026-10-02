import EnvelopingIsomorphism.PBW.Rules

/-! Disjoint adjacent PBW replacements commute modulo smaller relations. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

theorem insert_eq_sum (p s : List α) (x : L) :
    insert b p s x = (b.repr x).sum (fun i a ↦ a • single (p ++ i :: s) 1) := by
  simp [insert, Finsupp.mapDomain]

theorem insert_cross (p m s : List α) (x y : L) :
    (b.repr x).sum (fun i a ↦ a • insert b (p ++ i :: m) s y) =
      (b.repr y).sum (fun j a ↦ a • insert b p (m ++ j :: s) x) := by
  classical
  simp only [insert_eq_sum, Finsupp.sum, Finset.smul_sum, smul_smul,
    List.append_assoc, List.cons_append]
  rw [Finset.sum_comm]
  simp only [mul_comm]

private theorem insert_eq_finset_sum (p s : List α) (x : L) :
    insert b p s x = ∑ i ∈ (b.repr x).support,
      (b.repr x) i • single (p ++ i :: s) 1 :=
  insert_eq_sum b p s x

theorem disjoint_identity (p m s : List α) (i j k l : α) :
    rhs b p i j (m ++ k :: l :: s) - rhs b (p ++ i :: j :: m) k l s =
      relation b (p ++ j :: i :: m) k l s - relation b p i j (m ++ l :: k :: s) +
      (b.repr ⁅b i, b j⁆).sum (fun a r ↦ r • relation b (p ++ a :: m) k l s) -
      (b.repr ⁅b k, b l⁆).sum (fun a r ↦ r • relation b p i j (m ++ a :: s)) := by
  classical
  have hcross := insert_cross b p m s ⁅b i, b j⁆ ⁅b k, b l⁆
  have hij : (∑ a ∈ (b.repr ⁅b k, b l⁆).support,
      (b.repr ⁅b k, b l⁆) a • single (p ++ i :: j :: (m ++ a :: s)) 1) =
      insert b (p ++ i :: j :: m) s ⁅b k, b l⁆ := by
    simpa [List.append_assoc] using
      (insert_eq_finset_sum b (p ++ i :: j :: m) s ⁅b k, b l⁆).symm
  have hji : (∑ a ∈ (b.repr ⁅b k, b l⁆).support,
      (b.repr ⁅b k, b l⁆) a • single (p ++ j :: i :: (m ++ a :: s)) 1) =
      insert b (p ++ j :: i :: m) s ⁅b k, b l⁆ := by
    simpa [List.append_assoc] using
      (insert_eq_finset_sum b (p ++ j :: i :: m) s ⁅b k, b l⁆).symm
  simp only [relation, rhs, smul_sub, smul_add] at *
  simp only [Finsupp.sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    List.append_assoc, List.cons_append] at *
  simp only [← insert_eq_finset_sum] at *
  rw [hcross, hij, hji]
  abel

theorem disjoint_mem_lower (p m s : List α) (i j k l : α)
    (hji : j < i) (hlk : l < k) :
    rhs b p i j (m ++ k :: l :: s) - rhs b (p ++ i :: j :: m) k l s ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: (m ++ k :: l :: s)) := by
  classical
  rw [disjoint_identity]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · apply Submodule.sub_mem
      · apply relation_mem_lower_of_lt b _ _ _ _ _ hlk
        simpa [List.append_assoc] using wordLT_swap p (m ++ k :: l :: s) hji
      · apply relation_mem_lower_of_lt b _ _ _ _ _ hji
        simpa [List.append_assoc] using wordLT_swap (p ++ i :: j :: m) s hlk
    · apply Submodule.sum_mem
      intro a ha
      apply Submodule.smul_mem
      apply relation_mem_lower_of_length_lt
      simp
  · apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    apply relation_mem_lower_of_length_lt
    simp

end EnvelopingIsomorphism.PBW
