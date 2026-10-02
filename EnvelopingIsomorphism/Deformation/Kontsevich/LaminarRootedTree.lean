import Mathlib.Order.SuccPred.Tree
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-! Native rooted trees constructed from finite laminar families of nonempty finite sets. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LaminarRootedTree

variable {I : Type*} [DecidableEq I]

/-- The carrier is the actual family subtype, ordered by reverse inclusion. -/
abbrev Node (F : Finset (Finset I)) := OrderDual {B : Finset I // B ∈ F}

omit [DecidableEq I] in
@[simp] theorem label_le_iff {F : Finset (Finset I)} (v w : Node F) :
    v ≤ w ↔ w.val ⊆ v.val := Iff.rfl

omit [DecidableEq I] in
@[simp] theorem label_lt_iff {F : Finset (Finset I)} (v w : Node F) :
    v < w ↔ w.val ⊂ v.val := Iff.rfl

/-- Exactly the finite-set hypotheses needed for the tree construction. -/
structure FamilyData (F : Finset (Finset I)) (A : Finset I) : Prop where
  root_mem : A ∈ F
  nonempty : ∀ B ∈ F, B.Nonempty
  subset_root : ∀ B ∈ F, B ⊆ A
  laminar : ∀ B ∈ F, ∀ C ∈ F, B ⊆ C ∨ C ⊆ B ∨ Disjoint B C

omit [DecidableEq I] in
private theorem exists_least_in_chain (G : Finset (Finset I)) (hne : G.Nonempty)
    (hchain : ∀ B ∈ G, ∀ C ∈ G, B ⊆ C ∨ C ⊆ B) :
    ∃ B ∈ G, ∀ C ∈ G, B ⊆ C := by
  obtain ⟨B, hB, hmin⟩ := G.exists_min_image Finset.card hne
  refine ⟨B, hB, fun C hC ↦ ?_⟩
  rcases hchain B hB C hC with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h (hmin C hC)).symm.subset

namespace FamilyData

variable {F : Finset (Finset I)} {A : Finset I} (h : FamilyData F A)

include h

omit [DecidableEq I] in
/-- Containers of a nonempty set form a chain inside a laminar family. -/
theorem containers_comparable (B : Finset I) (hB : B.Nonempty)
    {C D : Finset I} (hC : C ∈ F) (hD : D ∈ F) (hBC : B ⊆ C) (hBD : B ⊆ D) :
    C ⊆ D ∨ D ⊆ C := by
  rcases h.laminar C hC D hD with hCD | hDC | hdisj
  · exact Or.inl hCD
  · exact Or.inr hDC
  · obtain ⟨x, hx⟩ := hB
    exact False.elim ((Finset.disjoint_left.mp hdisj) (hBC hx) (hBD hx))

theorem exists_least_container (B : Finset I) (hB : B.Nonempty) (hBA : B ⊆ A) :
    ∃ C ∈ F, B ⊆ C ∧ ∀ D ∈ F, B ⊆ D → C ⊆ D := by
  classical
  obtain ⟨C, hC, hleast⟩ := exists_least_in_chain (F.filter (fun C ↦ B ⊆ C))
    ⟨A, by simp [h.root_mem, hBA]⟩ (by
      intro C hC D hD
      simp only [Finset.mem_filter] at hC hD
      exact h.containers_comparable B hB hC.1 hD.1 hC.2 hD.2)
  simp only [Finset.mem_filter] at hC
  exact ⟨C, hC.1, hC.2, fun D hD hBD ↦ hleast D (by simp [hD, hBD])⟩

def leastContainer (B : Finset I) (hB : B.Nonempty) (hBA : B ⊆ A) : Node F :=
  ⟨(h.exists_least_container B hB hBA).choose,
    (h.exists_least_container B hB hBA).choose_spec.1⟩

theorem subset_leastContainer (B : Finset I) (hB : B.Nonempty) (hBA : B ⊆ A) :
    B ⊆ (h.leastContainer B hB hBA).val :=
  (h.exists_least_container B hB hBA).choose_spec.2.1

theorem leastContainer_subset (B : Finset I) (hB : B.Nonempty) (hBA : B ⊆ A)
    {D : Finset I} (hD : D ∈ F) (hBD : B ⊆ D) : (h.leastContainer B hB hBA).val ⊆ D :=
  (h.exists_least_container B hB hBA).choose_spec.2.2 D hD hBD

/-- The least common ancestor is the least family member containing both labels. -/
def lca (v w : Node F) : Node F :=
  h.leastContainer (v.val ∪ w.val) ((h.nonempty v.val v.property).mono Finset.subset_union_left)
    (Finset.union_subset (h.subset_root v.val v.property) (h.subset_root w.val w.property))

theorem left_subset_lca (v w : Node F) : v.val ⊆ (h.lca v w).val :=
  Finset.subset_union_left.trans (h.subset_leastContainer _ _ _)

theorem right_subset_lca (v w : Node F) : w.val ⊆ (h.lca v w).val :=
  Finset.subset_union_right.trans (h.subset_leastContainer _ _ _)

theorem lca_subset (v w z : Node F) (hv : v.val ⊆ z.val) (hw : w.val ⊆ z.val) :
    (h.lca v w).val ⊆ z.val :=
  h.leastContainer_subset _ _ _ z.property (Finset.union_subset hv hw)

@[reducible] def semilatticeInf : SemilatticeInf (Node F) where
  __ := (inferInstance : PartialOrder (Node F))
  inf := h.lca
  inf_le_left := h.left_subset_lca
  inf_le_right := h.right_subset_lca
  le_inf v w z hv hw := h.lca_subset w z v hv hw

@[reducible] def orderBot : OrderBot (Node F) where
  bot := ⟨A, h.root_mem⟩
  bot_le v := h.subset_root v.val v.property

theorem exists_least_strict_container (v : Node F) (hv : v.val ≠ A) :
    ∃ C ∈ F, v.val ⊂ C ∧ ∀ D ∈ F, v.val ⊂ D → C ⊆ D := by
  classical
  have hvA : v.val ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨h.subset_root v.val v.property, hv⟩
  obtain ⟨C, hC, hleast⟩ := exists_least_in_chain (F.filter (fun C ↦ v.val ⊂ C))
    ⟨A, by simp [h.root_mem, hvA]⟩ (by
      intro C hC D hD
      simp only [Finset.mem_filter] at hC hD
      exact h.containers_comparable v.val (h.nonempty v.val v.property) hC.1 hD.1 hC.2.subset hD.2.subset)
  simp only [Finset.mem_filter] at hC
  exact ⟨C, hC.1, hC.2, fun D hD hvD ↦ hleast D (by simp [hD, hvD])⟩

/-- The root is fixed; every other node gets its least strict container as parent. -/
def parent (v : Node F) : Node F :=
  if hv : v.val = A then v else
    ⟨(h.exists_least_strict_container v hv).choose,
      (h.exists_least_strict_container v hv).choose_spec.1⟩

theorem parent_of_root (v : Node F) (hv : v.val = A) : h.parent v = v := by
  simp [parent, hv]

theorem ssubset_parent (v : Node F) (hv : v.val ≠ A) : v.val ⊂ (h.parent v).val := by
  simpa only [parent, dif_neg hv] using (h.exists_least_strict_container v hv).choose_spec.2.1

theorem parent_subset_of_ssubset (v : Node F) (hv : v.val ≠ A) (z : Node F)
    (hvz : v.val ⊂ z.val) : (h.parent v).val ⊆ z.val := by
  simpa only [parent, dif_neg hv] using
    (h.exists_least_strict_container v hv).choose_spec.2.2 z.val z.property hvz

theorem subset_parent (v : Node F) : v.val ⊆ (h.parent v).val := by
  by_cases hv : v.val = A
  · rw [h.parent_of_root v hv]
  · exact (h.ssubset_parent v hv).subset

@[reducible] def predOrder : PredOrder (Node F) where
  pred := h.parent
  pred_le := h.subset_parent
  min_of_le_pred {v} hle := by
    by_cases hv : v.val = A
    · intro z hz
      change z.val ⊆ v.val
      rw [hv]
      exact h.subset_root z.val z.property
    · exact False.elim ((h.ssubset_parent v hv).not_subset hle)
  le_pred_of_lt {v w} hvw := by
    change (h.parent w).val ⊆ v.val
    have hw : w.val ≠ A := by
      intro heq
      have hsub := h.subset_root v.val v.property
      rw [← heq] at hsub
      exact hvw.not_ge hsub
    exact h.parent_subset_of_ssubset w hw v hvw

/-- All native instances are constructed from finite laminar data, including the predecessor
and its Archimedean property. The carrier retains the actual reverse-inclusion subtype. -/
def build : RootedTree := by
  letI : SemilatticeInf (Node F) := h.semilatticeInf
  letI : OrderBot (Node F) := h.orderBot
  letI : PredOrder (Node F) := h.predOrder
  letI : Fintype (Node F) := inferInstance
  letI : WellFoundedLT (Node F) := Finite.to_wellFoundedLT
  letI : IsPredArchimedean (Node F) := inferInstance
  exact { α := Node F }

@[simp] theorem build_le_iff (v w : h.build) : v ≤ w ↔ w.val ⊆ v.val := Iff.rfl

@[simp] theorem build_lt_iff (v w : h.build) : v < w ↔ w.val ⊂ v.val := Iff.rfl

@[simp] theorem build_bot_label : (⊥ : h.build).val = A := rfl

@[simp] theorem build_inf (v w : h.build) : v ⊓ w = h.lca v w := rfl

@[simp] theorem build_pred (v : h.build) : Order.pred v = h.parent v := rfl

/-- Every ancestor chain is linearly ordered by the inherited native tree order. -/
theorem ancestors_comparable (v w z : h.build) (hv : v ≤ z) (hw : w ≤ z) :
    v ≤ w ∨ w ≤ v :=
  (h.containers_comparable z.val (h.nonempty z.val z.property) v.property w.property hv hw).symm

/-- Native inf is exactly the least containing family node. -/
theorem inf_label_subset_iff (v w z : h.build) :
    (v ⊓ w).val ⊆ z.val ↔ v.val ⊆ z.val ∧ w.val ⊆ z.val := by
  constructor
  · intro hsub
    exact ⟨(h.left_subset_lca v w).trans hsub, (h.right_subset_lca v w).trans hsub⟩
  · rintro ⟨hv, hw⟩
    exact h.lca_subset v w z hv hw

/-- The native cover relation is strict reverse inclusion with no intervening family label. -/
theorem covBy_iff_labels (v w : h.build) :
    v ⋖ w ↔ w.val ⊂ v.val ∧
      ∀ B ∈ F, w.val ⊂ B → B ⊂ v.val → False := by
  constructor
  · rintro ⟨hvw, hno⟩
    exact ⟨hvw, fun B hB hwB hBv ↦ hno (c := ⟨B, hB⟩) hBv hwB⟩
  · rintro ⟨hvw, hno⟩
    exact ⟨hvw, fun z hvz hzw ↦ hno z.val z.property hzw hvz⟩

/-- Existential form suited to identifying the children of a recursive finite partition. -/
theorem covBy_iff_ssubset_no_intermediate (v w : h.build) :
    v ⋖ w ↔ w.val ⊂ v.val ∧ ¬∃ B ∈ F, B ⊂ v.val ∧ w.val ⊂ B := by
  rw [h.covBy_iff_labels]
  constructor
  · rintro ⟨hvw, hno⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨B, hB, hBv, hwB⟩
    exact hno B hB hwB hBv
  · rintro ⟨hvw, hno⟩
    exact ⟨hvw, fun B hB hwB hBv ↦ hno ⟨B, hB, hBv, hwB⟩⟩

/-- Every nonroot node is covered by its explicitly constructed parent. -/
theorem parent_covBy (v : h.build) (hv : v.val ≠ A) : Order.pred v ⋖ v := by
  refine ⟨h.ssubset_parent v hv, ?_⟩
  intro z hpz hzv
  exact hpz.not_ge (h.parent_subset_of_ssubset v hv z hzv)

theorem pred_label_ssubset (v : h.build) (hv : v.val ≠ A) :
    v.val ⊂ (Order.pred v).val := h.ssubset_parent v hv

theorem pred_label_least (v z : h.build) (hvz : v.val ⊂ z.val) :
    (Order.pred v).val ⊆ z.val := by
  have hv : v.val ≠ A := by
    intro heq
    have hsub := h.subset_root z.val z.property
    rw [← heq] at hsub
    exact hvz.not_subset hsub
  exact h.parent_subset_of_ssubset v hv z hvz

/-- Covers identify the parent uniquely in the native predecessor structure. -/
theorem covBy_iff_parent (v w : h.build) :
    v ⋖ w ↔ w.val ≠ A ∧ Order.pred w = v := by
  constructor
  · intro hcov
    refine ⟨?_, hcov.pred_eq⟩
    intro hw
    have hsub := h.subset_root v.val v.property
    rw [← hw] at hsub
    exact hcov.lt.not_ge hsub
  · rintro ⟨hw, rfl⟩
    exact h.parent_covBy w hw

/-- A singleton family node is a leaf, since every node label is nonempty. -/
theorem isMax_of_singleton (v : h.build) {x : I} (hv : v.val = {x}) : IsMax v := by
  intro w hvw
  change v.val ⊆ w.val
  have hw : w.val ⊆ {x} := by
    change w.val ⊆ v.val at hvw
    simpa only [hv] using hvw
  have hweq := (h.nonempty w.val w.property).subset_singleton_iff.mp hw
  rw [hv, hweq]

/-- If every singleton is present, the leaves are exactly the singleton nodes. -/
theorem isMax_iff_singleton (hsingle : ∀ x ∈ A, ({x} : Finset I) ∈ F) (v : h.build) :
    IsMax v ↔ ∃ x ∈ A, v.val = {x} := by
  constructor
  · intro hmax
    obtain ⟨x, hx⟩ := h.nonempty v.val v.property
    have hxA := h.subset_root v.val v.property hx
    let w : h.build := ⟨{x}, hsingle x hxA⟩
    have hvw : v ≤ w := Finset.singleton_subset_iff.mpr hx
    have hwv : w ≤ v := hmax hvw
    exact ⟨x, hxA, Finset.Subset.antisymm hwv hvw⟩
  · rintro ⟨x, hx, hv⟩
    exact h.isMax_of_singleton v hv

theorem isMax_iff_card_eq_one (hsingle : ∀ x ∈ A, ({x} : Finset I) ∈ F) (v : h.build) :
    IsMax v ↔ v.val.card = 1 := by
  rw [h.isMax_iff_singleton hsingle v, Finset.card_eq_one]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, hx⟩
    exact h.subset_root v.val v.property (by simp [hx])

end FamilyData

/-- Raw finite-family factory for a native rooted tree; no tree instance is an input. -/
def tree (F : Finset (Finset I)) (A : Finset I) (hA : A ∈ F)
    (hne : ∀ B ∈ F, B.Nonempty) (hsub : ∀ B ∈ F, B ⊆ A)
    (hlam : ∀ B ∈ F, ∀ C ∈ F, B ⊆ C ∨ C ⊆ B ∨ Disjoint B C) : RootedTree :=
  FamilyData.build ⟨hA, hne, hsub, hlam⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.LaminarRootedTree
