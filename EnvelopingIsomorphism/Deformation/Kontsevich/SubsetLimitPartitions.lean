import EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits
import Mathlib.Order.Partition.Finpartition

/-! Native finite child partitions extracted from the actual normalized limit
shapes. Every nontrivial parent splits into strictly smaller nonempty fibers. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits

open Filter Topology
open scoped Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

def extendedShape (q : ShapeFamily I) (A : LargeSubset I) (j : I) : ℂ :=
  if hj : j ∈ A.val then q A ⟨j, hj⟩ else 0

@[simp] theorem extendedShape_apply (q : ShapeFamily I) (A : LargeSubset I) (j : A.val) :
    extendedShape q A j = q A j := by
  simp only [extendedShape, dif_pos j.property]

/-- Equal-value fibers, using Mathlib's actual finite partition structure. -/
def partition (q : ShapeFamily I) (A : Finset I) : Finpartition A :=
  if hA : 1 < A.card then Finpartition.ofSetSetoid (Setoid.ker (extendedShape q ⟨A, hA⟩)) A
  else ⊥

theorem eq_shape_of_mem_same_part (q : ShapeFamily I) (A : LargeSubset I)
    {B : Finset I} (hB : B ∈ (partition q A.val).parts)
    (j k : A.val) (hj : j.val ∈ B) (hk : k.val ∈ B) : q A j = q A k := by
  have hpart := (partition q A.val).part_eq_of_mem hB hj
  have hkpart : k.val ∈ (partition q A.val).part j.val := by rw [hpart]; exact hk
  simp only [partition, dif_pos A.property] at hkpart
  have hrel := (Finpartition.mem_part_ofSetSetoid_iff_rel (s := Setoid.ker (extendedShape q A)) A.val).mp hkpart
  have heq := hrel.2.2
  change extendedShape q A j = extendedShape q A k at heq
  simpa only [extendedShape_apply] using heq

/-- Strict decrease is derived from the extracted nonconstant normalized shape. -/
theorem partition_proper (q : ShapeFamily I) (hnc : ∀ A : LargeSubset I, ∃ j k, q A j ≠ q A k)
    (A : Finset I) (hA : 1 < A.card) (B : Finset I) (hB : B ∈ (partition q A).parts) :
    B.card < A.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨(partition q A).le hB, ?_⟩
  intro hBA
  obtain ⟨j, k, hjk⟩ := hnc ⟨A, hA⟩
  exact hjk (eq_shape_of_mem_same_part q ⟨A, hA⟩ hB j k (hBA ▸ j.property) (hBA ▸ k.property))

/-- All true children have zero relative radius along the already selected common subsequence. -/
theorem partition_child_ratio_tendsto_zero (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : ShapeFamily I)
    (hlim : ∀ A : LargeSubset I,
      Tendsto (fun k => normalizedOn A (p (φ k))) atTop (𝓝 (q A)))
    (A B : LargeSubset I) (hB : B.val ∈ (partition q A.val).parts) :
    Tendsto (fun k => radiusOn B (p (φ k)) / radiusOn A (p (φ k))) atTop (𝓝 0) := by
  have hBA : B.val ⊆ A.val := (partition q A.val).le hB
  apply radius_ratio_tendsto_zero p φ q A B hBA (hlim A)
  intro j
  exact eq_shape_of_mem_same_part q A hB (inclusion A B hBA j)
    (inclusion A B hBA (anchor B)) j.property (anchor B).property

end EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits
