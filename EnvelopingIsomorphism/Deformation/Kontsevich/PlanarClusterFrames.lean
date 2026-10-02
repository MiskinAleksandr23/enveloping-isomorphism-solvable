import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterRoot
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestFrames
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusCoordinates

/-! The actual two branches and frame types of the extracted planar fiber tree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFrames

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterRoot
open scoped Classical

variable {q : ℕ} (a : Fin q) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

def upperNode : tree a x :=
  ⟨upperLabels, ClusterPartitionTree.child_mem_clusters (extraction a x).partitions
    (extraction a x).partitions_proper (by
      have hr : 1 < (Finset.univ : Finset (DoubledLabel q 0)).card := root_large a x
      rw [ClusterPartitionTree.children, if_pos hr, root_parts a x hx]
      exact Finset.mem_insert_self _ _)⟩

def lowerNode : tree a x :=
  ⟨lowerLabels, ClusterPartitionTree.child_mem_clusters (extraction a x).partitions
    (extraction a x).partitions_proper (by
      have hr : 1 < (Finset.univ : Finset (DoubledLabel q 0)).card := root_large a x
      rw [ClusterPartitionTree.children, if_pos hr, root_parts a x hx]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

@[simp] theorem upperNode_label : (upperNode a x hx).val = upperLabels := rfl
@[simp] theorem lowerNode_label : (lowerNode a x hx).val = lowerLabels := rfl

theorem root_covBy_upper : (⊥ : tree a x) ⋖ upperNode a x hx :=
  (root_child_iff a x hx _).mpr (Or.inl rfl)

theorem root_covBy_lower : (⊥ : tree a x) ⋖ lowerNode a x hx :=
  (root_child_iff a x hx _).mpr (Or.inr rfl)

theorem upper_ne_lower : upperNode a x hx ≠ lowerNode a x hx :=
  fun h => PlanarClusterRoot.upper_ne_lower a (congrArg Subtype.val h)

theorem reflection_upper : reflection a x (upperNode a x hx) = lowerNode a x hx := by
  apply Subtype.ext
  change (upperLabels : Finset (DoubledLabel q 0)).image doubledReflection = lowerLabels
  ext j
  rcases j with (j | j) | j
  · simp only [Finset.mem_image, mem_lowerLabels, PlanarClusterDoubledData.lower_upper,
      Bool.false_eq_true, iff_false]
    rintro ⟨k, hk, he⟩
    rcases k with (k | k) | k
    · simp [doubledReflection] at he
    · exact Fin.elim0 k
    · simp at hk
  · exact Fin.elim0 j
  · simp only [mem_lowerLabels, PlanarClusterDoubledData.lower_lower, iff_true]
    exact Finset.mem_image.mpr ⟨Sum.inl (Sum.inl j), by simp, rfl⟩

theorem reflection_lower : reflection a x (lowerNode a x hx) = upperNode a x hx := by
  rw [← reflection_upper a x hx, reflection_reflection]

theorem upper_le_leaf (j : Fin q) : upperNode a x hx ≤ canonicalLeaf a x (Sum.inl (Sum.inl j)) := by
  rw [le_canonicalLeaf_iff]
  simp

theorem lower_le_leaf (j : Fin q) : lowerNode a x hx ≤ canonicalLeaf a x (Sum.inr j) := by
  rw [le_canonicalLeaf_iff]
  simp

theorem upper_nonleaf (b : Fin q) (hab : a ≠ b) : ¬IsMax (upperNode a x hx) := by
  intro h
  have ha := le_antisymm (upper_le_leaf a x hx a) (h (upper_le_leaf a x hx a))
  have hb := le_antisymm (upper_le_leaf a x hx b) (h (upper_le_leaf a x hx b))
  have he := canonicalLeaf_injective a x (ha.symm.trans hb)
  exact hab (Sum.inl.inj (Sum.inl.inj he))

def upperActive (b : Fin q) (hab : a ≠ b) : ReflectedRadiusCoordinates.ActiveNode (tree a x) :=
  ⟨upperNode a x hx, ne_of_gt (root_covBy_upper a x hx).lt, upper_nonleaf a x hx b hab⟩

/-- The distinguished radial coordinate is the actual reflection orbit of the upper branch. -/
def upperOrbit (b : Fin q) (hab : a ≠ b) :=
  ReflectedRadiusCoordinates.orbitClass (tree a x) (reflection a x) (reflection_reflection a x)
    (upperActive a x hx b hab)

theorem nonroot_below_branch (v : tree a x) (hv : v ≠ ⊥) :
    upperNode a x hx ≤ v ∨ lowerNode a x hx ≤ v := by
  obtain ⟨w, hw, hwv⟩ := ForestInsertionDifference.exists_child_between (tree a x)
    (bot_lt_iff_ne_bot.mpr hv)
  rcases (root_child_iff a x hx w).mp hw with he | he
  · exact Or.inl ((show w = upperNode a x hx from Subtype.ext he) ▸ hwv)
  · exact Or.inr ((show w = lowerNode a x hx from Subtype.ext he) ▸ hwv)

include hx

theorem nonroot_not_fixed (v : tree a x) (hv : v ≠ ⊥) : reflection a x v ≠ v := by
  intro hfixed
  have hboth : upperNode a x hx ≤ v ∧ lowerNode a x hx ≤ v := by
    rcases nonroot_below_branch a x hx v hv with hu | hl
    · refine ⟨hu, ?_⟩
      have h := (reflection a x).monotone hu
      simpa only [reflection_upper a x hx, hfixed] using h
    · refine ⟨?_, hl⟩
      have h := (reflection a x).monotone hl
      simpa only [reflection_lower a x hx, hfixed] using h
  obtain ⟨j, hj⟩ := node_nonempty a x v
  have hu : j ∈ upperLabels := hboth.1 hj
  have hl : j ∈ lowerLabels := hboth.2 hj
  rw [mem_upperLabels] at hu
  rw [mem_lowerLabels] at hl
  exact Bool.false_ne_true (hu.symm.trans hl)

theorem fixed_iff_root (v : tree a x) : reflection a x v = v ↔ v = ⊥ := by
  constructor
  · intro h
    by_contra hv
    exact nonroot_not_fixed a x hx v hv h
  · rintro rfl
    exact (reflection a x).map_bot

/-- Every deeper parent has the genuine extracted complex two-mark frame. -/
theorem frames_nonroot (v : tree a x) (hv : v ≠ ⊥) (hn : ¬IsMax v) :
    frames a x v hn = .complex (markedPair a x v hn).1 (markedPair a x v hn).2
      (markedPair_spec a x v hn).1 (markedPair_spec a x v hn).2.1
      (markedPair_spec a x v hn).2.2 :=
  frames_nonstable a x v hn (nonroot_not_fixed a x hx v hv)

theorem canonicalIncrement_upper : canonicalIncrement a x (upperNode a x hx) = Complex.I := by
  have h := increment_eq_shape_of_child (extraction a x) Finset.univ
    ⟨Sum.inr a, Finset.mem_univ _⟩ ⊥ (upperNode a x hx) (root_covBy_upper a x hx)
    (Sum.inl (Sum.inl a)) (by simp)
  change canonicalIncrement a x (upperNode a x hx) =
    SubsetNormalizedLimits.extendedShape (extraction a x).shapes (rootSubset a x)
      (Sum.inl (Sum.inl a)) at h
  rw [h, root_extendedShape a x hx]
  simp [PlanarClusterFiber.base]

theorem canonicalIncrement_lower : canonicalIncrement a x (lowerNode a x hx) = -Complex.I := by
  rw [← reflection_upper a x hx, canonicalIncrement_reflect, canonicalIncrement_upper a x hx,
    Complex.conj_I]

theorem root_hasUpperChild : HasUpperChild a x (⊥ : tree a x) :=
  ⟨upperNode a x hx, root_covBy_upper a x hx, by rw [canonicalIncrement_upper a x hx]; norm_num⟩

theorem root_upperChild_unique (v : tree a x) (hv : (⊥ : tree a x) ⋖ v)
    (hi : 0 < (canonicalIncrement a x v).im) : v = upperNode a x hx := by
  rcases (root_child_iff a x hx v).mp hv with he | he
  · exact Subtype.ext he
  · have he' : v = lowerNode a x hx := Subtype.ext he
    rw [he', canonicalIncrement_lower a x hx] at hi
    norm_num at hi

/-- The root's actual chosen frame is the upper height frame. -/
theorem frames_root (hn : ¬IsMax (⊥ : tree a x)) :
    frames a x ⊥ hn = .stableHeight (upperNode a x hx) (root_covBy_upper a x hx) := by
  rw [frames, dif_pos (reflection a x).map_bot, dif_pos (root_hasUpperChild a x hx)]
  have he := root_upperChild_unique a x hx _ (root_hasUpperChild a x hx).choose_spec.1
    (root_hasUpperChild a x hx).choose_spec.2
  simp only [he]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFrames
