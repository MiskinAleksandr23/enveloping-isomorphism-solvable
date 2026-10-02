import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.Data.Fin.SuccPred

/-! Admissible graphs obtained by splitting one exterior vertex into two consecutive vertices. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {n m : ℕ} {q : Fin n → ℕ}

/-- Existing exterior vertices move past the newly inserted left vertex. -/
def splitExternalEmbedding (r : Fin m) : Fin m → Fin (m + 1) :=
  r.castSucc.succAbove

/-- Collapse the two consecutive vertices back to the original exterior vertex. -/
def splitExternalCollapse (r : Fin m) : Fin (m + 1) → Fin m := r.predAbove

@[simp] theorem splitExternalEmbedding_self (r : Fin m) :
    splitExternalEmbedding r r = r.succ := Fin.succAbove_castSucc_self r

@[simp] theorem splitExternalCollapse_embedding (r j : Fin m) :
    splitExternalCollapse r (splitExternalEmbedding r j) = j :=
  Fin.predAbove_succAbove r j

@[simp] theorem splitExternalCollapse_left (r : Fin m) :
    splitExternalCollapse r r.castSucc = r := Fin.predAbove_castSucc_self r

@[simp] theorem splitExternalCollapse_right (r : Fin m) :
    splitExternalCollapse r r.succ = r := Fin.predAbove_succ_self r

theorem splitExternalEmbedding_injective (r : Fin m) :
    Function.Injective (splitExternalEmbedding r) := Fin.succAbove_right_injective

@[simp] theorem splitExternalEmbedding_ne_left (r j : Fin m) :
    splitExternalEmbedding r j ≠ r.castSucc := Fin.succAbove_ne r.castSucc j

/-- Choice `0` means the left vertex and choice `1` means the right vertex. -/
def splitExternalVertex (r : Fin m) (c : Fin 2) : Fin (m + 1) :=
  if c = 0 then r.castSucc else r.succ

@[simp] theorem splitExternalVertex_zero (r : Fin m) :
    splitExternalVertex r 0 = r.castSucc := by simp [splitExternalVertex]

@[simp] theorem splitExternalVertex_one (r : Fin m) :
    splitExternalVertex r 1 = r.succ := by simp [splitExternalVertex]

@[simp] theorem splitExternalCollapse_vertex (r : Fin m) (c : Fin 2) :
    splitExternalCollapse r (splitExternalVertex r c) = r := by
  by_cases h : c = 0 <;> simp [splitExternalVertex, h]

@[simp] theorem splitExternalVertex_eq_left_iff (r : Fin m) (c : Fin 2) :
    splitExternalVertex r c = r.castSucc ↔ c = 0 := by
  fin_cases c <;> simp [splitExternalVertex]
  exact Fin.ne_of_gt Fin.castSucc_lt_succ

@[simp] theorem splitExternalVertex_eq_right_iff (r : Fin m) (c : Fin 2) :
    splitExternalVertex r c = r.succ ↔ c = 1 := by
  fin_cases c <;> simp [splitExternalVertex]
  exact Fin.ne_of_lt Fin.castSucc_lt_succ

namespace Graph

/-- Only edges originally arriving at `r` carry a splitting choice. -/
abbrev SplitExternalChoices (Γ : Graph q m) (r : Fin m) :=
  {e : Edge q // Γ.target e = Sum.inr r} → Fin 2

/-- Extend a splitting choice by zero away from the vertex being split. -/
def splitExternalChoice (Γ : Graph q m) (r : Fin m) (χ : Γ.SplitExternalChoices r)
    (e : Edge q) : Fin 2 :=
  if h : Γ.target e = Sum.inr r then χ ⟨e, h⟩ else 0

@[simp] theorem splitExternalChoice_of_hit (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) (h : Γ.target e = Sum.inr r) :
    Γ.splitExternalChoice r χ e = χ ⟨e, h⟩ := by simp [splitExternalChoice, h]

/-- The target function before its admissibility has been proved. -/
def splitExternalTarget (Γ : Graph q m) (r : Fin m) (χ : Γ.SplitExternalChoices r)
    (e : Edge q) : Vertex n (m + 1) :=
  if h : Γ.target e = Sum.inr r then Sum.inr (splitExternalVertex r (χ ⟨e, h⟩))
  else Sum.map id (splitExternalEmbedding r) (Γ.target e)

@[simp] theorem splitExternalTarget_of_hit (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) (h : Γ.target e = Sum.inr r) :
    Γ.splitExternalTarget r χ e = Sum.inr (splitExternalVertex r (χ ⟨e, h⟩)) := by
  simp [splitExternalTarget, h]

/-- Gluing the consecutive new vertices restores each original edge target. -/
@[simp] theorem collapse_splitExternalTarget (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) :
    Sum.map id (splitExternalCollapse r) (Γ.splitExternalTarget r χ e) = Γ.target e := by
  by_cases h : Γ.target e = Sum.inr r
  · simp [splitExternalTarget, h]
  · simp only [splitExternalTarget, dif_neg h]
    cases Γ.target e <;> simp

/-- Splitting preserves admissibility: an alleged loop or repeated target would collapse
to a loop or repeated target of the original graph. -/
def splitExternal (Γ : Graph q m) (r : Fin m) (χ : Γ.SplitExternalChoices r) :
    Graph q (m + 1) where
  target := Γ.splitExternalTarget r χ
  noLoops v a h := Γ.noLoops v a (by
    simpa using congrArg (Sum.map id (splitExternalCollapse r)) h)
  distinctTargets v a b h := Γ.distinctTargets v (by
    simpa using congrArg (Sum.map id (splitExternalCollapse r)) h)

@[simp] theorem splitExternal_target (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) :
    (Γ.splitExternal r χ).target e = Γ.splitExternalTarget r χ e := rfl

@[simp] theorem collapse_splitExternal_target (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) :
    Sum.map id (splitExternalCollapse r) ((Γ.splitExternal r χ).target e) = Γ.target e :=
  Γ.collapse_splitExternalTarget r χ e

theorem splitExternal_target_internal_iff (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) (v : Fin n) :
    (Γ.splitExternal r χ).target e = Sum.inl v ↔ Γ.target e = Sum.inl v := by
  constructor
  · intro h
    simpa using congrArg (Sum.map id (splitExternalCollapse r)) h
  · intro h
    simp [splitExternalTarget, h]

theorem splitExternal_target_unaffected_iff (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) (j : Fin m) (hj : j ≠ r) :
    (Γ.splitExternal r χ).target e = Sum.inr (splitExternalEmbedding r j) ↔
      Γ.target e = Sum.inr j := by
  constructor
  · intro h
    simpa using congrArg (Sum.map id (splitExternalCollapse r)) h
  · intro h
    simp [splitExternalTarget, h, hj]

theorem splitExternal_target_left_iff (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) :
    (Γ.splitExternal r χ).target e = Sum.inr r.castSucc ↔
      Γ.target e = Sum.inr r ∧ Γ.splitExternalChoice r χ e = 0 := by
  by_cases h : Γ.target e = Sum.inr r
  · simp [splitExternalTarget, h]
  · simp only [h, false_and, iff_false]
    intro he
    have := congrArg (Sum.map id (splitExternalCollapse r)) he
    exact h (by simpa using this)

theorem splitExternal_target_right_iff (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (e : Edge q) :
    (Γ.splitExternal r χ).target e = Sum.inr r.succ ↔
      Γ.target e = Sum.inr r ∧ Γ.splitExternalChoice r χ e = 1 := by
  by_cases h : Γ.target e = Sum.inr r
  · simp [splitExternalTarget, h]
  · simp only [h, false_and, iff_false]
    intro he
    have := congrArg (Sum.map id (splitExternalCollapse r)) he
    exact h (by simpa using this)

@[simp] theorem incoming_splitExternal_internal (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (v : Fin n) :
    (Γ.splitExternal r χ).incoming (Sum.inl v) = Γ.incoming (Sum.inl v) := by
  ext e
  simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Γ.splitExternal_target_internal_iff r χ e v

theorem incoming_splitExternal_unaffected (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) (j : Fin m) (hj : j ≠ r) :
    (Γ.splitExternal r χ).incoming (Sum.inr (splitExternalEmbedding r j)) =
      Γ.incoming (Sum.inr j) := by
  ext e
  simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Γ.splitExternal_target_unaffected_iff r χ e j hj

theorem incoming_splitExternal_left (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) :
    (Γ.splitExternal r χ).incoming (Sum.inr r.castSucc) =
      (Γ.incoming (Sum.inr r)).filter (fun e ↦ Γ.splitExternalChoice r χ e = 0) := by
  ext e
  simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Γ.splitExternal_target_left_iff r χ e

theorem incoming_splitExternal_right (Γ : Graph q m) (r : Fin m)
    (χ : Γ.SplitExternalChoices r) :
    (Γ.splitExternal r χ).incoming (Sum.inr r.succ) =
      (Γ.incoming (Sum.inr r)).filter (fun e ↦ Γ.splitExternalChoice r χ e = 1) := by
  ext e
  simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Γ.splitExternal_target_right_iff r χ e

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
