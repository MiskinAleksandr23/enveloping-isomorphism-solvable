import EnvelopingIsomorphism.Deformation.GraphLeibniz
import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.Data.List.NodupEquivFin

/-! Finite-edge Leibniz rules for graph vertex splitting. Assignment indices
are the actual distinct incoming edges, even when coordinate labels repeat. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open MvPolynomial
open scoped BigOperators

section Lists

variable {α σ J : Type*} [DecidableEq J]

/-- Read a factor assignment from the actual edge occupying each derivative position. -/
def labelledAssignment (lab : α → σ) (χ : α → J) :
    (l : List α) → Fin (l.map lab).length → J
  | [] => Fin.elim0
  | e :: l => Fin.cons (χ e) (labelledAssignment lab χ l)

omit [DecidableEq J] in
theorem labelledAssignment_apply (lab : α → σ) (χ : α → J) (l : List α)
    (i : Fin (l.map lab).length) :
    labelledAssignment lab χ l i = χ (l.get ⟨i.val, by simpa only [List.length_map] using i.isLt⟩) := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons e l ih =>
    refine Fin.cases rfl (fun j ↦ ?_) i
    exact ih j

theorem assignedDerivatives_labelled (lab : α → σ) (χ : α → J) (l : List α) (j : J) :
    assignedDerivatives (l.map lab) (labelledAssignment lab χ l) j =
      (l.filter (fun e ↦ χ e = j)).map lab := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    change (if χ e = j then lab e :: assignedDerivatives (l.map lab) (labelledAssignment lab χ l) j
      else assignedDerivatives (l.map lab) (labelledAssignment lab χ l) j) = _
    rw [ih]
    by_cases h : χ e = j <;> simp [h]

end Lists

section Enumerations

variable {R α σ J : Type*} [CommRing R] [DecidableEq α] [Fintype α]
variable [DecidableEq J] [Fintype J]

/-- The position-based expansion equals the sum over assignments of actual edges. -/
theorem iteratedPDeriv_enumeration_prod (l : List α) (hl : l.Nodup) (hall : ∀ e, e ∈ l)
    (lab : α → σ) (f : J → MvPolynomial σ R) :
    iteratedPDeriv (l.map lab) (∏ j, f j) =
      ∑ χ : α → J, ∏ j, iteratedPDeriv ((l.filter (fun e ↦ χ e = j)).map lab) (f j) := by
  rw [iteratedPDeriv_fintype_prod]
  let e : Fin (l.map lab).length ≃ α :=
    (finCongr (List.length_map lab)).trans (List.Nodup.getEquivOfForallMemList l hl hall)
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl J))
  intro a
  have ha : a = labelledAssignment lab (Equiv.arrowCongr e (Equiv.refl J) a) l := by
    funext i
    rw [labelledAssignment_apply]
    change a i = a (e.symm (e i))
    rw [Equiv.symm_apply_apply]
  apply Finset.prod_congr rfl
  intro j hj
  conv_lhs => rw [ha]
  rw [assignedDerivatives_labelled]

end Enumerations

section Finsets

variable {R α σ J : Type*} [CommRing R] [DecidableEq α]
variable [DecidableEq J] [Fintype J]

/-- Select incoming edges assigned to one output factor. -/
def assignedEdges (s : Finset α) (χ : s → J) (j : J) : Finset α :=
  (s.attach.filter (fun e ↦ χ e = j)).map ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq α] [Fintype J] in
@[simp] theorem mem_assignedEdges (s : Finset α) (χ : s → J) (j : J) (e : α) :
    e ∈ assignedEdges s χ j ↔ ∃ h : e ∈ s, χ ⟨e, h⟩ = j := by
  classical
  simp only [assignedEdges, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨x, hx⟩, hc, he⟩
    change x = e at he
    subst x
    exact ⟨hx, hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨⟨e, he⟩, hc, rfl⟩

omit [DecidableEq α] in
theorem attach_toList_perm (s : Finset α) :
    (s.attach.toList.map Subtype.val).Perm s.toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map Subtype.val_injective) (Finset.nodup_toList _)).mpr
  intro e
  simp

omit [DecidableEq α] [Fintype J] in
theorem assignedEdges_toList_perm (s : Finset α) (χ : s → J) (j : J) :
    ((s.attach.toList.filter (fun e ↦ χ e = j)).map Subtype.val).Perm
      (assignedEdges s χ j).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (((Finset.nodup_toList _).filter _).map Subtype.val_injective) (Finset.nodup_toList _)).mpr
  intro e
  simp only [List.mem_map, List.mem_filter, Finset.mem_toList, Finset.mem_attach, true_and,
    mem_assignedEdges, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x, hx⟩, hc, he⟩
    change x = e at he
    subst x
    exact ⟨hx, hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨⟨e, he⟩, hc, rfl⟩

/-- Full finite-edge Leibniz expansion, with no lost multiplicities for repeated labels. -/
theorem iteratedPDeriv_edge_prod {d : ℕ} (s : Finset α) (lab : α → Fin d) (f : J → MvPolynomial (Fin d) R) :
    iteratedPDeriv (s.toList.map lab) (∏ j, f j) =
      ∑ χ : s → J, ∏ j, iteratedPDeriv ((assignedEdges s χ j).toList.map lab) (f j) := by
  classical
  have h := iteratedPDeriv_enumeration_prod s.attach.toList (Finset.nodup_toList _)
    (by intro e; simp) (fun e : s ↦ lab e.val) f
  have hs : iteratedPDeriv (s.attach.toList.map (fun e : s ↦ lab e.val)) =
      iteratedPDeriv (k := R) (s.toList.map lab) := by
    apply KontsevichGraph.General.iteratedPDeriv_perm
    simpa only [List.map_map, Function.comp_def] using (attach_toList_perm s).map lab
  rw [hs] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  apply KontsevichGraph.General.iteratedPDeriv_perm
  simpa only [List.map_map, Function.comp_def] using (assignedEdges_toList_perm s χ j).map lab

end Finsets

end EnvelopingIsomorphism.Deformation
