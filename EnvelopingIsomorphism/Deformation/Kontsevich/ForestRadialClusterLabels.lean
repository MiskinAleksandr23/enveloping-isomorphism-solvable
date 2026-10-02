import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceClassification
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPattern

/-! Actual label data of codimension-one forest faces: a unique upper cluster
for paired radii, and consecutive boundary blocks for fixed radii. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialClusterLabels

open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ReflectedRadiusCoordinates ForestRadialFaceClassification
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def IsUpper (v : tree i x) : Prop :=
  ∀ a ∈ v.val, ∃ j : Fin n, a = Sum.inl (Sum.inl j)

theorem isUpper_reflection_of_lower (v : tree i x)
    (hv : ∀ a ∈ v.val, ∃ j : Fin n, a = Sum.inr j) : IsUpper i x (reflection i x v) := by
  intro a ha
  rw [reflection_label] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, rfl⟩ := hv b hb
  exact ⟨j, rfl⟩

theorem not_isUpper_reflection (v : tree i x) (hv : IsUpper i x v) :
    ¬ IsUpper i x (reflection i x v) := by
  intro hr
  obtain ⟨a, ha⟩ := node_nonempty i x v
  obtain ⟨j, rfl⟩ := hv a ha
  have hm : Sum.inr j ∈ (reflection i x v).val :=
    (mem_reflection_iff i x v _).mpr ha
  obtain ⟨k, hk⟩ := hr _ hm
  cases hk

/-- One and only one node in a paired radial orbit consists of upper labels. -/
theorem existsUnique_upper_node (o : ForestRadialFaceClassification.Orbit i x)
    (ho : kind i x o = .paired) :
    ∃! v : ActiveNode (tree i x),
      orbitClass (tree i x) (reflection i x) (reflection_reflection i x) v = o ∧ IsUpper i x v.val := by
  have hex : ∃ v : ActiveNode (tree i x),
      orbitClass (tree i x) (reflection i x) (reflection_reflection i x) v = o ∧ IsUpper i x v.val := by
    induction o using Quotient.inductionOn with
    | h u =>
      have hu : reflection i x u.val ≠ u.val := (nodeKind_paired_iff i x u.val).mp ho
      rcases nonfixed_one_side i x u.val hu with h | h
      · exact ⟨u, rfl, h⟩
      · exact ⟨reflect (tree i x) (reflection i x) u,
          orbitClass_reflect (tree i x) (reflection i x) (reflection_reflection i x) u,
          isUpper_reflection_of_lower i x u.val h⟩
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, hv, ?_⟩
  intro w hw
  have h := (orbitClass_eq_iff (tree i x) (reflection i x) (reflection_reflection i x) v w).mp
    (hv.1.trans hw.1.symm)
  rcases h with h | h
  · exact h.symm
  · have he : reflection i x v.val = w.val := congrArg Subtype.val h
    exact (not_isUpper_reflection i x v.val hv.2 (he.symm ▸ hw.2)).elim

def upperNode (o : ForestRadialFaceClassification.Orbit i x) (ho : kind i x o = .paired) :
    ActiveNode (tree i x) := (existsUnique_upper_node i x o ho).choose

theorem upperNode_spec (o : ForestRadialFaceClassification.Orbit i x) (ho : kind i x o = .paired) :
    orbitClass (tree i x) (reflection i x) (reflection_reflection i x) (upperNode i x o ho) = o ∧
      IsUpper i x (upperNode i x o ho).val := (existsUnique_upper_node i x o ho).choose_spec.1

theorem pureBoundary_labels (v : tree i x) (hv : nodeKind i x v = .pureBoundary) :
    ∀ a ∈ v.val, ∃ j : Fin m, a = Sum.inl (Sum.inr j) := by
  obtain ⟨hs, h⟩ := (nodeKind_pureBoundary_iff i x v).mp hv
  intro a ha
  rcases a with (j | j) | j
  · exact (h j ha).elim
  · exact ⟨j, rfl⟩
  · exact (h j ((fixed_mem_mirror_iff i x v hs j).mp ha)).elim

/-- All-interior proper nodes necessarily leave an actual boundary label outside. -/
theorem infinity_outside_boundary (v : ActiveNode (tree i x))
    (hv : nodeKind i x v.val = .infinity) :
    ∃ j : Fin m, Sum.inl (Sum.inr j) ∉ v.val.val := by
  obtain ⟨hs, h⟩ := (nodeKind_infinity_iff i x v.val).mp hv
  by_contra hn
  push Not at hn
  have he : v.val.val = Finset.univ := by
    ext a
    simp only [Finset.mem_univ, iff_true]
    rcases a with (j | j) | j
    · exact h j
    · exact hn j
    · exact (fixed_mem_mirror_iff i x v.val hs j).mpr (h j)
  exact v.property.1 (Subtype.ext he)

private theorem inf_leaf_outside (v : tree i x) (a b : DoubledLabel n m)
    (ha : a ∈ v.val) (hb : b ∉ v.val) :
    canonicalLeaf i x a ⊓ canonicalLeaf i x b = v ⊓ canonicalLeaf i x b := by
  have hva := (le_canonicalLeaf_iff i x v a).mpr ha
  apply le_antisymm
  · apply le_inf
    · rcases le_total_of_directed hva
        (inf_le_left : canonicalLeaf i x a ⊓ canonicalLeaf i x b ≤ canonicalLeaf i x a) with h | h
      · exact h
      · exact (hb ((le_canonicalLeaf_iff i x v b).mp (h.trans inf_le_right))).elim
    · exact inf_le_right
  · exact inf_le_inf hva le_rfl

/-- Boundary labels of every actual extracted node are order-convex. The
proof uses the native strict boundary-gap signs of the extracted geometry. -/
theorem boundary_between (v : tree i x) (j k l : Fin m) (hjk : j < k) (hkl : k < l)
    (hj : Sum.inl (Sum.inr j) ∈ v.val) (hl : Sum.inl (Sum.inr l) ∈ v.val) :
    Sum.inl (Sum.inr k) ∈ v.val := by
  by_contra hk
  let a := canonicalLeaf i x (Sum.inl (Sum.inr k))
  have hva : ¬ v ≤ a := fun h => hk ((le_canonicalLeaf_iff i x v _).mp h)
  have hc : v ⊓ a < v := lt_iff_le_not_ge.mpr ⟨inf_le_left, fun h => hva (h.trans inf_le_right)⟩
  have hca : v ⊓ a < a := by
    refine lt_iff_le_not_ge.mpr ⟨inf_le_right, ?_⟩
    intro h
    exact hva ((canonicalLeaf_isMax i x _) (h.trans inf_le_left))
  obtain ⟨d, hd, hdv⟩ := ForestInsertionDifference.exists_child_between (tree i x) hc
  obtain ⟨e, he, hea⟩ := ForestInsertionDifference.exists_child_between (tree i x) hca
  have hjv := (le_canonicalLeaf_iff i x v _).mpr hj
  have hlv := (le_canonicalLeaf_iff i x v _).mpr hl
  have hij := inf_leaf_outside i x v _ _ hj hk
  have hil := inf_leaf_outside i x v _ _ hl hk
  have hp := canonical_boundary_gap i x j k hjk e d
    (by simpa only [inf_comm, hij] using he) hea
    (by simpa only [inf_comm, hij] using hd) (hdv.trans hjv)
  have hn := canonical_boundary_gap i x k l hkl d e
    (hil.symm ▸ hd) (hdv.trans hlv) (hil.symm ▸ he) hea
  simp only [Complex.sub_re] at hp hn
  linarith

def boundaryLabels (v : tree i x) : Finset (Fin m) :=
  Finset.univ.filter (fun j => Sum.inl (Sum.inr j) ∈ v.val)

@[simp] theorem mem_boundaryLabels (v : tree i x) (j : Fin m) :
    j ∈ boundaryLabels i x v ↔ Sum.inl (Sum.inr j) ∈ v.val := by simp [boundaryLabels]

/-- The boundary labels of a forest node form one of the exact finite blocks
used by the simple real-cluster charts, including the empty block. -/
theorem exists_boundary_block (v : tree i x) :
    ∃ l u : Fin (m + 1), l ≤ u ∧ boundaryLabels i x v = boundaryClusterBlock l u := by
  by_cases hne : (boundaryLabels i x v).Nonempty
  · let a := (boundaryLabels i x v).min' hne
    let b := (boundaryLabels i x v).max' hne
    have ha : a ∈ boundaryLabels i x v := Finset.min'_mem _ _
    have hb : b ∈ boundaryLabels i x v := Finset.max'_mem _ _
    have hab : a ≤ b := Finset.min'_le _ _ hb
    refine ⟨⟨a.val, by omega⟩, ⟨b.val + 1, by omega⟩, ?_, ?_⟩
    · change a.val ≤ b.val + 1
      exact le_trans hab (Nat.le_succ _)
    · ext j
      rw [mem_boundaryClusterBlock]
      constructor
      · intro hj
        exact ⟨Finset.min'_le _ _ hj, Nat.lt_succ_of_le (Finset.le_max' _ _ hj)⟩
      · rintro ⟨haj, hjb⟩
        have haj' : a ≤ j := haj
        have hjb' : j ≤ b := Nat.le_of_lt_succ hjb
        rcases lt_or_eq_of_le haj' with haj' | rfl
        · rcases lt_or_eq_of_le hjb' with hjb' | rfl
          · exact (mem_boundaryLabels i x v j).mpr
              (boundary_between i x v a j b haj' hjb'
                ((mem_boundaryLabels i x v a).mp ha) ((mem_boundaryLabels i x v b).mp hb))
          · exact hb
        · exact ha
  · refine ⟨0, 0, le_rfl, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    ext j
    simp

def interiorLabels (v : tree i x) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Sum.inl (Sum.inl j) ∈ v.val)

@[simp] theorem mem_interiorLabels (v : tree i x) (j : Fin n) :
    j ∈ interiorLabels i x v ↔ Sum.inl (Sum.inl j) ∈ v.val := by simp [interiorLabels]

theorem isUpper_label_eq_image (v : tree i x) (hv : IsUpper i x v) :
    v.val = (interiorLabels i x v).image (fun j => Sum.inl (Sum.inl j)) := by
  ext a
  constructor
  · intro ha
    obtain ⟨j, rfl⟩ := hv a ha
    exact Finset.mem_image.mpr ⟨j, (mem_interiorLabels i x v j).mpr ha, rfl⟩
  · rintro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    exact (mem_interiorLabels i x v j).mp hj

theorem isUpper_card (v : tree i x) (hv : IsUpper i x v) :
    v.val.card = (interiorLabels i x v).card := by
  rw [isUpper_label_eq_image i x v hv]
  exact Finset.card_image_of_injective _ (fun _ _ h => Sum.inl_injective (Sum.inl_injective h))

/-- A radial interior collision has at least two genuine upper labels. -/
theorem upperNode_card (o : ForestRadialFaceClassification.Orbit i x) (ho : kind i x o = .paired) :
    1 < (interiorLabels i x (upperNode i x o ho).val).card := by
  rw [← isUpper_card i x _ (upperNode_spec i x o ho).2]
  exact ExtractedForestIdentification.nonleaf_large i x _ (upperNode i x o ho).property.2

/-- Actual endpoints of the extracted boundary-label block. -/
def blockLower (v : tree i x) : Fin (m + 1) := (exists_boundary_block i x v).choose

def blockUpper (v : tree i x) : Fin (m + 1) := (exists_boundary_block i x v).choose_spec.choose

theorem block_order (v : tree i x) : blockLower i x v ≤ blockUpper i x v :=
  (exists_boundary_block i x v).choose_spec.choose_spec.1

theorem boundaryLabels_eq_block (v : tree i x) :
    boundaryLabels i x v = boundaryClusterBlock (blockLower i x v) (blockUpper i x v) :=
  (exists_boundary_block i x v).choose_spec.choose_spec.2

/-- The stable forest label set is literally the collision mask used by the
simple real-cluster chart; no label/profile correspondence is supplied. -/
theorem fixed_label_mask (v : tree i x) (hv : reflection i x v = v) (a : DoubledLabel n m) :
    a ∈ v.val ↔ boundaryClusterCollapses (interiorLabels i x v)
      (blockLower i x v) (blockUpper i x v) a := by
  rcases a with (j | j) | j
  · exact (mem_interiorLabels i x v j).symm
  · change _ ↔ j ∈ boundaryClusterBlock _ _
    rw [← boundaryLabels_eq_block]
    exact (mem_boundaryLabels i x v j).symm
  · exact (fixed_mem_mirror_iff i x v hv j).trans (mem_interiorLabels i x v j).symm

theorem properReal_anchors (v : tree i x) (hv : nodeKind i x v = .properReal) :
    ∃ a b : Fin n, a ∈ interiorLabels i x v ∧ b ∉ interiorLabels i x v := by
  obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (nodeKind_properReal_iff i x v).mp hv
  exact ⟨a, b, (mem_interiorLabels i x v a).mpr ha,
    fun h => hb ((mem_interiorLabels i x v b).mp h)⟩

theorem pureBoundary_interiorLabels (v : tree i x) (hv : nodeKind i x v = .pureBoundary) :
    interiorLabels i x v = ∅ := by
  have h := (nodeKind_pureBoundary_iff i x v).mp hv |>.2
  apply Finset.eq_empty_iff_forall_notMem.mpr
  exact fun j hj => h j ((mem_interiorLabels i x v j).mp hj)

theorem infinity_interiorLabels (v : tree i x) (hv : nodeKind i x v = .infinity) :
    interiorLabels i x v = Finset.univ := by
  have h := (nodeKind_infinity_iff i x v).mp hv |>.2
  ext j
  simp only [mem_interiorLabels, Finset.mem_univ, iff_true]
  exact h j

/-- A pure-boundary radial node contains at least two boundary labels; a
single fixed boundary leaf cannot create a Stokes face. -/
theorem pureBoundary_block_card (v : ActiveNode (tree i x))
    (hv : nodeKind i x v.val = .pureBoundary) :
    1 < (boundaryClusterBlock (blockLower i x v.val) (blockUpper i x v.val)).card := by
  have he : v.val.val = (boundaryLabels i x v.val).image (fun j => Sum.inl (Sum.inr j)) := by
    ext a
    constructor
    · intro ha
      obtain ⟨j, rfl⟩ := pureBoundary_labels i x v.val hv a ha
      exact Finset.mem_image.mpr ⟨j, (mem_boundaryLabels i x v.val j).mpr ha, rfl⟩
    · intro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact (mem_boundaryLabels i x v.val j).mp hj
  have hc : v.val.val.card = (boundaryLabels i x v.val).card := by
    rw [he]
    exact Finset.card_image_of_injective _ (fun _ _ h => Sum.inr_injective (Sum.inl_injective h))
  rw [← boundaryLabels_eq_block, ← hc]
  exact ExtractedForestIdentification.nonleaf_large i x _ v.property.2

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialClusterLabels
