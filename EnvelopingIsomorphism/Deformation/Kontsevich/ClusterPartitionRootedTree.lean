import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterPartitionTree
import EnvelopingIsomorphism.Deformation.Kontsevich.LaminarRootedTree

/-! The native rooted tree actually constructed from the prescribed finite partitions.
Its labels are the generated clusters; its covers are precisely the partition edges. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterPartitionTree

open scoped Classical

variable {I : Type*} [DecidableEq I]
variable (P : ∀ A : Finset I, Finpartition A)
variable (hproper : ∀ A, 1 < A.card → ∀ B ∈ (P A).parts, B.card < A.card)

/-- All finite laminar input facts are proved from the actual partition recursion. -/
theorem familyData (R : Finset I) (hR : R.Nonempty) :
    LaminarRootedTree.FamilyData (clusters P hproper R) R where
  root_mem := root_mem_clusters P hproper R
  nonempty B hB := nonempty_of_mem_clusters P hproper R B hR hB
  subset_root B hB := subset_of_mem_clusters P hproper R B hB
  laminar B hB C hC := laminar P hproper R B C hB hC

/-- The actual native RootedTree, with finite reachable labels in reverse inclusion order. -/
def tree (R : Finset I) (hR : R.Nonempty) : RootedTree :=
  (familyData P hproper R hR).build

instance treeFintype (R : Finset I) (hR : R.Nonempty) : Fintype (tree P hproper R hR) :=
  inferInstanceAs (Fintype (LaminarRootedTree.Node (clusters P hproper R)))

variable {P hproper} {R : Finset I} {hR : R.Nonempty}

@[simp] theorem tree_le_iff (v w : tree P hproper R hR) : v ≤ w ↔ w.val ⊆ v.val := Iff.rfl

@[simp] theorem tree_lt_iff (v w : tree P hproper R hR) : v < w ↔ w.val ⊂ v.val := Iff.rfl

@[simp] theorem tree_root_label : (⊥ : tree P hproper R hR).val = R := rfl

theorem tree_label_injective : Function.Injective (fun v : tree P hproper R hR ↦ v.val) :=
  Subtype.val_injective

/-- Covers in the native tree are exactly the prescribed child edges. -/
theorem covBy_iff_child (v w : tree P hproper R hR) :
    v ⋖ w ↔ w.val ∈ children P v.val :=
  ((familyData P hproper R hR).covBy_iff_ssubset_no_intermediate v w).trans
    (child_iff_immediate P hproper R v.val w.val hR v.property w.property).symm

/-- Every nonleaf's children form exactly its actual native Finpartition. -/
theorem covBy_iff_part (v w : tree P hproper R hR) :
    v ⋖ w ↔ 1 < v.val.card ∧ w.val ∈ (P v.val).parts := by
  rw [covBy_iff_child, mem_children]

/-- The actual finite set of immediate children in the native tree. -/
def childNodes (v : tree P hproper R hR) : Finset (tree P hproper R hR) :=
  Finset.univ.filter (fun w ↦ v ⋖ w)

@[simp] theorem mem_childNodes (v w : tree P hproper R hR) : w ∈ childNodes v ↔ v ⋖ w := by
  simp [childNodes]

/-- No graph vertices or child labels were introduced or lost by the native tree construction. -/
theorem childNodes_labels (v : tree P hproper R hR) :
    (childNodes v).image (fun w ↦ w.val) = children P v.val := by
  ext B
  constructor
  · rintro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    exact (covBy_iff_child v w).mp ((mem_childNodes v w).mp hw)
  · intro hB
    have hmem : B ∈ clusters P hproper R :=
      clusters_subset_of_mem P hproper R v.val v.property (child_mem_clusters P hproper hB)
    refine Finset.mem_image.mpr ⟨⟨B, hmem⟩, ?_, rfl⟩
    exact (mem_childNodes _ _).mpr ((covBy_iff_child _ _).mpr hB)

theorem childNodes_labels_eq_parts (v : tree P hproper R hR) (hv : 1 < v.val.card) :
    (childNodes v).image (fun w ↦ w.val) = (P v.val).parts := by
  rw [childNodes_labels, children, if_pos hv]

theorem card_childNodes (v : tree P hproper R hR) :
    (childNodes v).card = (children P v.val).card := by
  rw [← childNodes_labels]
  exact (Finset.card_image_of_injective _ tree_label_injective).symm

/-- A leaf for each actual original label, using the proved singleton reachability. -/
def leaf (i : I) (hi : i ∈ R) : tree P hproper R hR :=
  ⟨{i}, singleton_mem_clusters P hproper R i hi⟩

@[simp] theorem leaf_label (i : I) (hi : i ∈ R) :
    (leaf (P := P) (hproper := hproper) (hR := hR) i hi).val = {i} := rfl

@[simp] theorem le_leaf_iff (v : tree P hproper R hR) (i : I) (hi : i ∈ R) :
    v ≤ leaf (hR := hR) i hi ↔ i ∈ v.val := Finset.singleton_subset_iff

theorem leaf_isMax (i : I) (hi : i ∈ R) :
    IsMax (leaf (P := P) (hproper := hproper) (hR := hR) i hi) :=
  (familyData P hproper R hR).isMax_of_singleton _ rfl

/-- The native leaves are exactly singleton labels, not just assumed terminal nodes. -/
theorem isMax_iff_singleton (v : tree P hproper R hR) :
    IsMax v ↔ ∃ i ∈ R, v.val = {i} :=
  (familyData P hproper R hR).isMax_iff_singleton (singleton_mem_clusters P hproper R) v

theorem isMax_iff_card_eq_one (v : tree P hproper R hR) : IsMax v ↔ v.val.card = 1 :=
  (familyData P hproper R hR).isMax_iff_card_eq_one (singleton_mem_clusters P hproper R) v

theorem childNodes_empty_iff_isMax (v : tree P hproper R hR) : childNodes v = ∅ ↔ IsMax v := by
  rw [← Finset.card_eq_zero, card_childNodes, Finset.card_eq_zero,
    children_empty_iff P hproper v.val (nonempty_of_mem_clusters P hproper R v.val hR v.property),
    isMax_iff_card_eq_one]

/-- The recursive tree has no unary internal nodes. -/
theorem one_lt_card_childNodes (v : tree P hproper R hR) (hv : ¬IsMax v) :
    1 < (childNodes v).card := by
  rw [card_childNodes]
  apply one_lt_card_children P hproper
  have hpos := Finset.card_pos.mpr (nonempty_of_mem_clusters P hproper R v.val hR v.property)
  have hne := mt (isMax_iff_card_eq_one v).mpr hv
  omega

/-- Each nonroot's native predecessor is its unique prescribed partition parent. -/
theorem parent_part (v : tree P hproper R hR) (hv : v.val ≠ R) :
    1 < (Order.pred v).val.card ∧ v.val ∈ (P (Order.pred v).val).parts :=
  (covBy_iff_part _ _).mp ((familyData P hproper R hR).parent_covBy v hv)

theorem child_iff_parent (v w : tree P hproper R hR) :
    w.val ∈ children P v.val ↔ w.val ≠ R ∧ Order.pred w = v :=
  (covBy_iff_child v w).symm.trans ((familyData P hproper R hR).covBy_iff_parent v w)

/-- Native inf has the actual least-common-containing-cluster meaning. -/
theorem inf_label_subset_iff (v w z : tree P hproper R hR) :
    (v ⊓ w).val ⊆ z.val ↔ v.val ⊆ z.val ∧ w.val ⊆ z.val :=
  (familyData P hproper R hR).inf_label_subset_iff v w z

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterPartitionTree
