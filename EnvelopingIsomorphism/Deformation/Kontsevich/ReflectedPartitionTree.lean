import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterPartitionRootedTree
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Reflection of the actually generated finite cluster tree

Equivariance of the prescribed native partitions propagates through the
well-founded cluster recursion. It gives an involutive order automorphism
of the existing native rooted tree, hence preserves its actual parent and LCA.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedPartitionTree

open ClusterPartitionTree

variable {I : Type*} [DecidableEq I]
variable (σ : I → I) (hσ : Function.Involutive σ)

include hσ in
theorem image_involutive : Function.Involutive (Finset.image σ) := by
  intro A
  rw [Finset.image_image, show σ ∘ σ = id from funext hσ, Finset.image_id]

/-- The actual finite-set order automorphism induced by the label involution. -/
def imageOrderIso : Finset I ≃o Finset I where
  toFun := Finset.image σ
  invFun := Finset.image σ
  left_inv := image_involutive σ hσ
  right_inv := image_involutive σ hσ
  map_rel_iff' := Finset.image_subset_image_iff hσ.injective

include hσ in
theorem image_univ [Fintype I] : (Finset.univ : Finset I).image σ = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  exact Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, hσ i⟩

theorem parts_map_imageOrderIso (P : ∀ A : Finset I, Finpartition A) (A : Finset I) :
    ((P A).map (imageOrderIso σ hσ)).parts = (P A).parts.image (Finset.image σ) := by
  rw [Finpartition.parts_map, Finset.map_eq_image]
  rfl

variable (P : ∀ A : Finset I, Finpartition A)
variable (hP : ∀ A, (P (A.image σ)).parts = (P A).parts.image (Finset.image σ))

include hP in
/-- The parts-image condition is exactly native transport of the prescribed partition. -/
theorem partition_map_eq (A : Finset I) : P (A.image σ) = (P A).map (imageOrderIso σ hσ) := by
  apply Finpartition.ext
  rw [parts_map_imageOrderIso, hP]

include hσ hP in
theorem reflect_child {A B : Finset I} (hB : B ∈ children P A) :
    B.image σ ∈ children P (A.image σ) := by
  rcases (mem_children P A B).mp hB with ⟨hA, hB⟩
  apply (mem_children P _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [Finset.card_image_of_injective _ hσ.injective] using hA
  · rw [hP]
    exact Finset.mem_image.mpr ⟨B, hB, rfl⟩

include hσ hP in
theorem reflect_child_iff (A B : Finset I) :
    B.image σ ∈ children P (A.image σ) ↔ B ∈ children P A := by
  constructor
  · intro h
    simpa only [image_involutive σ hσ A, image_involutive σ hσ B] using reflect_child σ hσ P hP h
  · exact reflect_child σ hσ P hP

variable (hproper : ∀ A, 1 < A.card → ∀ B ∈ (P A).parts, B.card < A.card)

include hσ hP in
/-- Reflection preserves actual recursive reachability, proved by the finite-set recursion. -/
theorem reflect_mem_clusters (A B : Finset I) (hB : B ∈ clusters P hproper A) :
    B.image σ ∈ clusters P hproper (A.image σ) := by
  induction A using Finset.strongInductionOn generalizing B
  rename_i A ih
  rcases (mem_clusters P hproper A B).mp hB with rfl | ⟨C, hC, hBC⟩
  · exact root_mem_clusters P hproper _
  · apply (mem_clusters P hproper _ _).mpr
    exact Or.inr ⟨C.image σ, reflect_child σ hσ P hP hC,
      ih C (child_ssubset P hproper hC) B hBC⟩

include hσ hP in
theorem reflect_mem_clusters_iff (A B : Finset I) :
    B.image σ ∈ clusters P hproper (A.image σ) ↔ B ∈ clusters P hproper A := by
  constructor
  · intro h
    simpa only [image_involutive σ hσ A, image_involutive σ hσ B] using reflect_mem_clusters σ hσ P hP hproper _ _ h
  · exact reflect_mem_clusters σ hσ P hP hproper A B

include hσ hP in
/-- The complete recursively generated family is carried to the reflected family. -/
theorem clusters_image (A : Finset I) :
    clusters P hproper (A.image σ) = (clusters P hproper A).image (Finset.image σ) := by
  ext B
  constructor
  · intro hB
    have h := reflect_mem_clusters σ hσ P hP hproper _ _ hB
    rw [image_involutive σ hσ A] at h
    exact Finset.mem_image.mpr ⟨B.image σ, h, image_involutive σ hσ B⟩
  · rintro hB
    rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
    exact reflect_mem_clusters σ hσ P hP hproper A C hC

variable (R : Finset I) (hR : R.Nonempty) (hroot : R.image σ = R)

/-- The induced order automorphism uses exactly the existing reachable-node carrier. -/
def nodeOrderIso : tree P hproper R hR ≃o tree P hproper R hR where
  toFun v := ⟨v.val.image σ, by
    have h := reflect_mem_clusters σ hσ P hP hproper R v.val v.property
    simpa only [hroot] using h⟩
  invFun v := ⟨v.val.image σ, by
    have h := reflect_mem_clusters σ hσ P hP hproper R v.val v.property
    simpa only [hroot] using h⟩
  left_inv v := Subtype.ext (image_involutive σ hσ v.val)
  right_inv v := Subtype.ext (image_involutive σ hσ v.val)
  map_rel_iff' := Finset.image_subset_image_iff hσ.injective

@[simp] theorem nodeOrderIso_label (v : tree P hproper R hR) :
    (nodeOrderIso σ hσ P hP hproper R hR hroot v).val = v.val.image σ := rfl

theorem nodeOrderIso_involutive : Function.Involutive (nodeOrderIso σ hσ P hP hproper R hR hroot) := by
  intro v
  apply tree_label_injective
  exact image_involutive σ hσ v.val

@[simp] theorem reflect_ancestor_iff (v w : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot v ≤ nodeOrderIso σ hσ P hP hproper R hR hroot w ↔ v ≤ w :=
  (nodeOrderIso σ hσ P hP hproper R hR hroot).le_iff_le

@[simp] theorem reflect_cover_iff (v w : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot v ⋖ nodeOrderIso σ hσ P hP hproper R hR hroot w ↔ v ⋖ w := by
  rw [covBy_iff_child, covBy_iff_child]
  exact reflect_child_iff σ hσ P hP v.val w.val

@[simp] theorem reflect_parent (v : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot (Order.pred v) =
      Order.pred (nodeOrderIso σ hσ P hP hproper R hR hroot v) :=
  (nodeOrderIso σ hσ P hP hproper R hR hroot).map_pred v

@[simp] theorem reflect_lca (v w : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot (v ⊓ w) =
      nodeOrderIso σ hσ P hP hproper R hR hroot v ⊓ nodeOrderIso σ hσ P hP hproper R hR hroot w :=
  (nodeOrderIso σ hσ P hP hproper R hR hroot).map_inf v w

@[simp] theorem reflect_root : nodeOrderIso σ hσ P hP hproper R hR hroot ⊥ = ⊥ :=
  (nodeOrderIso σ hσ P hP hproper R hR hroot).map_bot

theorem node_fixed_iff (v : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot v = v ↔ v.val.image σ = v.val := by
  constructor
  · exact congrArg (fun w : tree P hproper R hR => w.val)
  · intro h
    apply tree_label_injective
    exact h

/-- A nonfixed reflected pair is disjoint: laminar containment and equal cardinality
would otherwise force it to be fixed. -/
theorem reflected_pair_disjoint (v : tree P hproper R hR)
    (hv : nodeOrderIso σ hσ P hP hproper R hR hroot v ≠ v) :
    Disjoint v.val (nodeOrderIso σ hσ P hP hproper R hR hroot v).val := by
  let w := nodeOrderIso σ hσ P hP hproper R hR hroot v
  have hc : w.val.card = v.val.card := Finset.card_image_of_injective _ hσ.injective
  rcases laminar P hproper R v.val w.val v.property w.property with h | h | h
  · exact (hv (Subtype.ext (Finset.eq_of_subset_of_card_le h hc.le).symm)).elim
  · exact (hv (Subtype.ext (Finset.eq_of_subset_of_card_le h hc.symm.le))).elim
  · exact h

/-- In particular, a cluster containing a fixed boundary label is a fixed node. -/
theorem node_fixed_of_fixed_label (v : tree P hproper R hR) (i : I)
    (hi : i ∈ v.val) (hfix : σ i = i) : nodeOrderIso σ hσ P hP hproper R hR hroot v = v := by
  by_contra h
  have hd := reflected_pair_disjoint σ hσ P hP hproper R hR hroot v h
  exact Finset.disjoint_left.mp hd hi (Finset.mem_image.mpr ⟨i, hi, hfix⟩)

theorem parent_fixed_of_fixed (v : tree P hproper R hR)
    (hv : nodeOrderIso σ hσ P hP hproper R hR hroot v = v) :
    nodeOrderIso σ hσ P hP hproper R hR hroot (Order.pred v) = Order.pred v := by
  rw [reflect_parent, hv]

theorem reflected_pair_lca_fixed (v : tree P hproper R hR) :
    nodeOrderIso σ hσ P hP hproper R hR hroot
        (v ⊓ nodeOrderIso σ hσ P hP hproper R hR hroot v) =
      v ⊓ nodeOrderIso σ hσ P hP hproper R hR hroot v := by
  rw [reflect_lca, nodeOrderIso_involutive]
  exact inf_comm _ _

section BoundaryOrder

variable {B : Type*} [Preorder B] (boundary : B → I)

/-- The boundary labels belonging to the finite cluster form an order-connected set. -/
def BoundaryContiguous (A : Finset I) : Prop :=
  Set.OrdConnected {i : B | boundary i ∈ A}

/-- Any property inherited by the actual child partitions propagates along the actual recursion. -/
theorem property_of_mem_clusters (Q : Finset I → Prop)
    (hchild : ∀ A, Q A → ∀ C ∈ (P A).parts, Q C)
    (A : Finset I) (hA : Q A) (C : Finset I) (hC : C ∈ clusters P hproper A) : Q C := by
  induction A using Finset.strongInductionOn generalizing C
  rename_i A ih
  rcases (mem_clusters P hproper A C).mp hC with rfl | ⟨D, hD, hCD⟩
  · exact hA
  · exact ih D (child_ssubset P hproper hD)
      (hchild A hA D ((mem_children P A D).mp hD).2) C hCD

/-- Boundary contiguity of a root and of its native child parts is inherited by every node. -/
theorem boundaryContiguous_of_mem_clusters
    (hchild : ∀ A, BoundaryContiguous boundary A → ∀ C ∈ (P A).parts, BoundaryContiguous boundary C)
    (hboundaryRoot : BoundaryContiguous boundary R)
    (C : Finset I) (hC : C ∈ clusters P hproper R) : BoundaryContiguous boundary C :=
  property_of_mem_clusters P hproper (BoundaryContiguous boundary) hchild R hboundaryRoot C hC

theorem boundaryContiguous_node
    (hchild : ∀ A, BoundaryContiguous boundary A → ∀ C ∈ (P A).parts, BoundaryContiguous boundary C)
    (hboundaryRoot : BoundaryContiguous boundary R) (v : tree P hproper R hR) :
    BoundaryContiguous boundary v.val :=
  boundaryContiguous_of_mem_clusters P hproper R boundary hchild hboundaryRoot v.val v.property

include hσ in
/-- Reflection fixes the boundary trace whenever it fixes the actual boundary labels. -/
theorem boundaryContiguous_reflect_iff (hboundary : ∀ i, σ (boundary i) = boundary i) (A : Finset I) :
    BoundaryContiguous boundary (A.image σ) ↔ BoundaryContiguous boundary A := by
  have hsets : {i : B | boundary i ∈ A.image σ} = {i : B | boundary i ∈ A} := by
    ext i
    constructor
    · intro hi
      have him : σ (boundary i) ∈ (A.image σ).image σ := Finset.mem_image.mpr ⟨boundary i, hi, rfl⟩
      change boundary i ∈ A
      simpa only [image_involutive σ hσ A, hboundary i] using him
    · intro hi
      exact Finset.mem_image.mpr ⟨boundary i, hi, hboundary i⟩
  unfold BoundaryContiguous
  rw [hsets]

end BoundaryOrder

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedPartitionTree
