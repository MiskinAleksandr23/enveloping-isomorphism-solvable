import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFiber
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestParameters

/-! The actual extracted root shape on the planar collision fiber is exactly
I on upper labels and -I on lower labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterRoot

open Configuration Filter Topology ComplexConjugate
open ExtractedForestParameters ReflectedSubsetNormalization
open scoped Classical

variable {q : ℕ} (a : Fin q) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

def rootSubset : SubsetNormalizedLimits.LargeSubset (DoubledLabel q 0) :=
  ⟨Finset.univ, root_large a x⟩

theorem root_stable : IsStable doubledReflection (rootSubset a x) := by
  simpa only [IsStable, rootSubset, Finset.ext_iff, Finset.mem_image] using
    ReflectedPartitionTree.image_univ (doubledReflection (n := q) (m := 0)) doubledReflection_involutive

theorem base_re (j : DoubledLabel q 0) : (PlanarClusterFiber.base j).re = 0 := by
  unfold PlanarClusterFiber.base
  split_ifs <;> simp

theorem base_norm (j : DoubledLabel q 0) : ‖PlanarClusterFiber.base j‖ = 1 := by
  unfold PlanarClusterFiber.base
  split_ifs <;> simp

theorem norm_base_root : ‖fun j : (rootSubset a x).val => PlanarClusterFiber.base j.val‖ = 1 := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (fun j => (base_norm j.val).le)
  · have h := norm_le_pi_norm (fun j : (rootSubset a x).val => PlanarClusterFiber.base j.val)
      (⟨Sum.inr a, Finset.mem_univ _⟩ : (rootSubset a x).val)
    simpa only [base_norm] using h

include hx

theorem tendsto_point (j : DoubledLabel q 0) :
    Tendsto (fun k => point a x k j) atTop (𝓝 (PlanarClusterFiber.base j)) :=
  (PlanarClusterFiber.tendsto_doubled a x hx j).comp (extraction a x).strictMono.tendsto_atTop

theorem tendsto_root_center :
    Tendsto (fun k => centerOn doubledReflection doubledReflection_involutive (rootSubset a x) (point a x k))
      atTop (𝓝 (0 : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_point a x hx (chosenAnchor doubledReflection doubledReflection_involutive (rootSubset a x)).val))
  simpa only [Function.comp_def, centerOn, if_pos (root_stable a x), base_re, Complex.ofReal_zero] using h

theorem tendsto_root_radius :
    Tendsto (fun k => radiusOn doubledReflection doubledReflection_involutive (rootSubset a x) (point a x k))
      atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun k => fun j : (rootSubset a x).val =>
      point a x k j.val - centerOn doubledReflection doubledReflection_involutive (rootSubset a x) (point a x k))
      atTop (𝓝 (fun j : (rootSubset a x).val => PlanarClusterFiber.base j.val)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [sub_zero] using (tendsto_point a x hx j.val).sub (tendsto_root_center a x hx)
  simpa only [radiusOn_eq_norm, norm_base_root] using h.norm

/-- Literal value of every coordinate of the actual all-subset root limit. -/
theorem root_shape (j : (rootSubset a x).val) :
    (extraction a x).shapes (rootSubset a x) j = PlanarClusterFiber.base j.val := by
  have he := ((continuous_apply j).tendsto ((extraction a x).shapes (rootSubset a x))).comp
    ((extraction a x).limits (rootSubset a x))
  have h := ((tendsto_root_radius a x hx).inv₀ one_ne_zero).smul
    ((tendsto_point a x hx j.val).sub (tendsto_root_center a x hx))
  apply tendsto_nhds_unique he
  simpa only [Function.comp_def, normalizedOn_apply, inv_one, sub_zero, one_smul, point] using h

theorem root_extendedShape (j : DoubledLabel q 0) :
    SubsetNormalizedLimits.extendedShape (extraction a x).shapes (rootSubset a x) j = PlanarClusterFiber.base j := by
  have hj : j ∈ (rootSubset a x).val := Finset.mem_univ _
  rw [SubsetNormalizedLimits.extendedShape, dif_pos hj]
  exact root_shape a x hx _

def upperLabels : Finset (DoubledLabel q 0) := Finset.univ.filter (fun j => PlanarClusterDoubledData.lower j = false)
def lowerLabels : Finset (DoubledLabel q 0) := Finset.univ.filter (fun j => PlanarClusterDoubledData.lower j = true)

omit hx in
@[simp] theorem mem_upperLabels (j : DoubledLabel q 0) : j ∈ upperLabels ↔ PlanarClusterDoubledData.lower j = false := by
  simp [upperLabels]

omit hx in
@[simp] theorem mem_lowerLabels (j : DoubledLabel q 0) : j ∈ lowerLabels ↔ PlanarClusterDoubledData.lower j = true := by
  simp [lowerLabels]

omit hx in
theorem upper_ne_lower (j : Fin q) : (upperLabels : Finset (DoubledLabel q 0)) ≠ lowerLabels := by
  intro h
  have hm : (Sum.inl (Sum.inl j) : DoubledLabel q 0) ∈ upperLabels := by simp
  rw [h] at hm
  simp at hm

omit hx in
theorem base_eq_iff (j k : DoubledLabel q 0) :
    PlanarClusterFiber.base j = PlanarClusterFiber.base k ↔
      PlanarClusterDoubledData.lower j = PlanarClusterDoubledData.lower k := by
  cases hj : PlanarClusterDoubledData.lower j <;> cases hk : PlanarClusterDoubledData.lower k <;>
    norm_num [PlanarClusterFiber.base, hj, hk, Complex.ext_iff]

theorem mem_root_part (j k : DoubledLabel q 0) :
    k ∈ ((extraction a x).partitions Finset.univ).part j ↔
      PlanarClusterDoubledData.lower j = PlanarClusterDoubledData.lower k := by
  change k ∈ (SubsetNormalizedLimits.partition (extraction a x).shapes (rootSubset a x).val).part j ↔ _
  rw [SubsetNormalizedLimits.partition, dif_pos (rootSubset a x).property,
    Finpartition.mem_part_ofSetSetoid_iff_rel]
  simp only [rootSubset, Finset.mem_univ, true_and]
  change SubsetNormalizedLimits.extendedShape (extraction a x).shapes (rootSubset a x) j =
    SubsetNormalizedLimits.extendedShape (extraction a x).shapes (rootSubset a x) k ↔ _
  rw [root_extendedShape a x hx, root_extendedShape a x hx, base_eq_iff]

theorem root_part_eq (j : DoubledLabel q 0) :
    ((extraction a x).partitions Finset.univ).part j =
      if PlanarClusterDoubledData.lower j then lowerLabels else upperLabels := by
  ext k
  cases hj : PlanarClusterDoubledData.lower j <;>
    simp only [mem_root_part a x hx, hj, ↓reduceIte, Bool.false_eq_true, mem_upperLabels, mem_lowerLabels]
  all_goals exact eq_comm

/-- Exactly two native root fibers: every original upper label, and every mirror label. -/
theorem root_parts : ((extraction a x).partitions Finset.univ).parts = {upperLabels, lowerLabels} := by
  ext B
  constructor
  · intro hB
    obtain ⟨j, hj⟩ := ((extraction a x).partitions Finset.univ).nonempty_of_mem_parts hB
    have he := ((extraction a x).partitions Finset.univ).part_eq_of_mem hB hj
    rw [root_part_eq a x hx] at he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases hjl : PlanarClusterDoubledData.lower j <;> simp only [hjl, Bool.false_eq_true, ↓reduceIte] at he
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · have he := root_part_eq a x hx (Sum.inl (Sum.inl a))
      simp only [PlanarClusterDoubledData.lower_upper, Bool.false_eq_true, ↓reduceIte] at he
      rw [← he]
      exact ((extraction a x).partitions Finset.univ).part_mem.mpr (Finset.mem_univ _)
    · have he := root_part_eq a x hx (Sum.inr a)
      simp only [PlanarClusterDoubledData.lower_lower, ↓reduceIte] at he
      rw [← he]
      exact ((extraction a x).partitions Finset.univ).part_mem.mpr (Finset.mem_univ _)

theorem root_child_iff (v : tree a x) :
    (⊥ : tree a x) ⋖ v ↔ v.val = upperLabels ∨ v.val = lowerLabels := by
  rw [(extraction a x).tree_child_iff_partition Finset.univ ⟨Sum.inr a, Finset.mem_univ _⟩]
  change 1 < (Finset.univ : Finset (DoubledLabel q 0)).card ∧
    v.val ∈ ((extraction a x).partitions Finset.univ).parts ↔ _
  rw [root_parts a x hx]
  have hlarge : 1 < (Finset.univ : Finset (DoubledLabel q 0)).card := root_large a x
  simp only [hlarge, true_and, Finset.mem_insert, Finset.mem_singleton]

theorem root_child_count :
    (ClusterPartitionTree.childNodes (hR := ⟨Sum.inr a, Finset.mem_univ _⟩) (⊥ : tree a x)).card = 2 := by
  rw [ClusterPartitionTree.card_childNodes]
  change (ClusterPartitionTree.children (extraction a x).partitions Finset.univ).card = 2
  have hlarge : 1 < (Finset.univ : Finset (DoubledLabel q 0)).card := root_large a x
  rw [ClusterPartitionTree.children, if_pos hlarge, root_parts a x hx,
    Finset.card_pair (upper_ne_lower a)]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterRoot
