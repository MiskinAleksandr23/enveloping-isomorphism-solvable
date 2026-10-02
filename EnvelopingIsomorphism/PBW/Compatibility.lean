import EnvelopingIsomorphism.PBW.Disjoint
import EnvelopingIsomorphism.PBW.CriticalPairs
import EnvelopingIsomorphism.PBW.Overlaps

/-! Compatibility of all adjacent PBW reductions. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

private theorem rhs_sub_mem_lower_of_prefix_length_le
    (p q s t : List α) (i j k l : α) (hji : j < i) (hlk : l < k)
    (hw : p ++ i :: j :: s = q ++ k :: l :: t) (hlen : p.length ≤ q.length) :
    rhs b p i j s - rhs b q k l t ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: s) := by
  rcases adjacent_pair_overlap_cases hw hlen with hsame | hover | hdisjoint
  · rcases hsame with ⟨rfl, rfl, rfl, rfl⟩
    simp
  · obtain ⟨hq, hj, hs⟩ := hover
    subst q k s
    exact triple_mem_lower b p t i j l hji hlk
  · obtain ⟨m, hq, hs⟩ := hdisjoint
    subst q s
    exact disjoint_mem_lower b p m t i j k l hji hlk

/-- Any two adjacent PBW reductions differ by relations with smaller leading words. -/
theorem rhs_sub_mem_lower
    (p q s t : List α) (i j k l : α) (hji : j < i) (hlk : l < k)
    (hw : p ++ i :: j :: s = q ++ k :: l :: t) :
    rhs b p i j s - rhs b q k l t ∈
      (reductionSystem b).lowerRelations (p ++ i :: j :: s) := by
  rcases Nat.le_total p.length q.length with hlen | hlen
  · exact rhs_sub_mem_lower_of_prefix_length_le b p q s t i j k l hji hlk hw hlen
  · have h := rhs_sub_mem_lower_of_prefix_length_le b q p t s k l i j hlk hji hw.symm hlen
    rw [hw]
    simpa only [neg_sub] using Submodule.neg_mem _ h

/-- The Jacobi identity implies compatibility of the entire PBW reduction system. -/
theorem reductionSystem_compatible : (reductionSystem b).Compatible := by
  intro w a c ha hc
  obtain ⟨p, i, j, s, hji, hw, rfl⟩ := ha
  obtain ⟨q, k, l, t, hlk, hw', rfl⟩ := hc
  rw [hw]
  exact rhs_sub_mem_lower b p q s t i j k l hji hlk (hw.symm.trans hw')

end EnvelopingIsomorphism.PBW
