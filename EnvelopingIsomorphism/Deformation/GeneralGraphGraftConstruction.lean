import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Admissible graph insertion with an explicit consecutive exterior block. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {a b m l : ℕ} (qΓ : Fin a → ℕ) (qΔ : Fin b → ℕ)

/-- Canonical concatenation of the two ordered internal-vertex arity families. -/
def graftArity (v : Fin (a + b)) : ℕ := Sum.elim qΓ qΔ (finSumFinEquiv.symm v)

@[simp] theorem graftArity_outer (v : Fin a) :
    graftArity qΓ qΔ (Fin.castAdd b v) = qΓ v := by simp [graftArity]

@[simp] theorem graftArity_inner (v : Fin b) :
    graftArity qΓ qΔ (Fin.natAdd a v) = qΔ v := by simp [graftArity]

theorem graftArity_eq_addCases : graftArity qΓ qΔ = Fin.addCases qΓ qΔ := by
  funext v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v <;> simp

/-- Edges retain their colour: the outer graph first, the inner graph second. -/
def graftEdgeEquiv : Edge (graftArity qΓ qΔ) ≃ Edge qΓ ⊕ Edge qΔ :=
  (Equiv.sigmaCongrLeft (β := fun s ↦ Fin (Sum.elim qΓ qΔ s))
    finSumFinEquiv.symm).trans (Equiv.sumSigmaDistrib _)

def graftOuterEdge : Edge qΓ ↪ Edge (graftArity qΓ qΔ) :=
  Function.Embedding.inl.trans (graftEdgeEquiv qΓ qΔ).symm.toEmbedding

def graftInnerEdge : Edge qΔ ↪ Edge (graftArity qΓ qΔ) :=
  Function.Embedding.inr.trans (graftEdgeEquiv qΓ qΔ).symm.toEmbedding

@[simp] theorem graftEdgeEquiv_outer (e : Edge qΓ) :
    graftEdgeEquiv qΓ qΔ (graftOuterEdge qΓ qΔ e) = Sum.inl e := by
  exact (graftEdgeEquiv qΓ qΔ).apply_symm_apply (Sum.inl e)

@[simp] theorem graftEdgeEquiv_inner (e : Edge qΔ) :
    graftEdgeEquiv qΓ qΔ (graftInnerEdge qΓ qΔ e) = Sum.inr e := by
  exact (graftEdgeEquiv qΓ qΔ).apply_symm_apply (Sum.inr e)

@[simp] theorem graftOuterEdge_source (e : Edge qΓ) :
    (graftOuterEdge qΓ qΔ e).1 = Fin.castAdd b e.1 := rfl

@[simp] theorem graftInnerEdge_source (e : Edge qΔ) :
    (graftInnerEdge qΓ qΔ e).1 = Fin.natAdd a e.1 := rfl

theorem graftEdgeEquiv_slot_val (e : Edge (graftArity qΓ qΔ)) :
    Sum.elim (fun f : Edge qΓ ↦ f.2.val) (fun f : Edge qΔ ↦ f.2.val)
      (graftEdgeEquiv qΓ qΔ e) = e.2.val := by
  have h (s : (v : Fin a ⊕ Fin b) × Fin (Sum.elim qΓ qΔ v)) :
      Sum.elim (fun f : Edge qΓ ↦ f.2.val) (fun f : Edge qΔ ↦ f.2.val)
        (Equiv.sumSigmaDistrib (fun v ↦ Fin (Sum.elim qΓ qΔ v)) s) = s.2.val := by
    rcases s with ⟨v | v, j⟩ <;> rfl
  exact h ⟨finSumFinEquiv.symm e.1, e.2⟩

@[simp] theorem graftOuterEdge_slot_val (e : Edge qΓ) :
    (graftOuterEdge qΓ qΔ e).2.val = e.2.val := by
  simpa only [graftEdgeEquiv_outer, Sum.elim_inl] using
    (graftEdgeEquiv_slot_val qΓ qΔ (graftOuterEdge qΓ qΔ e)).symm

@[simp] theorem graftInnerEdge_slot_val (e : Edge qΔ) :
    (graftInnerEdge qΓ qΔ e).2.val = e.2.val := by
  simpa only [graftEdgeEquiv_inner, Sum.elim_inr] using
    (graftEdgeEquiv_slot_val qΓ qΔ (graftInnerEdge qΓ qΔ e)).symm

theorem graftOuterEdge_mk (v : Fin a) (j : Fin (qΓ v)) :
    graftOuterEdge qΓ qΔ ⟨v, j⟩ =
      ⟨Fin.castAdd b v, Fin.cast (graftArity_outer qΓ qΔ v).symm j⟩ := by
  apply Sigma.ext (graftOuterEdge_source qΓ qΔ ⟨v, j⟩)
  apply heq_of_eq
  apply Fin.ext
  exact graftOuterEdge_slot_val qΓ qΔ ⟨v, j⟩

theorem graftInnerEdge_mk (v : Fin b) (j : Fin (qΔ v)) :
    graftInnerEdge qΓ qΔ ⟨v, j⟩ =
      ⟨Fin.natAdd a v, Fin.cast (graftArity_inner qΓ qΔ v).symm j⟩ := by
  apply Sigma.ext (graftInnerEdge_source qΓ qΔ ⟨v, j⟩)
  apply heq_of_eq
  apply Fin.ext
  exact graftInnerEdge_slot_val qΓ qΔ ⟨v, j⟩

theorem graftOuterEdge_ne_inner (e : Edge qΓ) (f : Edge qΔ) :
    graftOuterEdge qΓ qΔ e ≠ graftInnerEdge qΓ qΔ f := by
  intro h
  have := congrArg (graftEdgeEquiv qΓ qΔ) h
  simp at this

@[simp] theorem graftOuterEdge_eq_iff (e f : Edge qΓ) :
    graftOuterEdge qΓ qΔ e = graftOuterEdge qΓ qΔ f ↔ e = f :=
  (graftOuterEdge qΓ qΔ).injective.eq_iff

@[simp] theorem graftInnerEdge_eq_iff (e f : Edge qΔ) :
    graftInnerEdge qΓ qΔ e = graftInnerEdge qΓ qΔ f ↔ e = f :=
  (graftInnerEdge qΓ qΔ).injective.eq_iff

/-- Edge-label sums split into independent outer and inner label sums. -/
def graftLabelEquiv (d : ℕ) :
    (Edge (graftArity qΓ qΔ) → Fin d) ≃ (Edge qΓ → Fin d) × (Edge qΔ → Fin d) :=
  (Equiv.arrowCongr (graftEdgeEquiv qΓ qΔ) (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem graftLabelEquiv_outer (d : ℕ)
    (lab : Edge (graftArity qΓ qΔ) → Fin d) (e : Edge qΓ) :
    (graftLabelEquiv qΓ qΔ d lab).1 e = lab (graftOuterEdge qΓ qΔ e) := rfl

@[simp] theorem graftLabelEquiv_inner (d : ℕ)
    (lab : Edge (graftArity qΓ qΔ) → Fin d) (e : Edge qΔ) :
    (graftLabelEquiv qΓ qΔ d lab).2 e = lab (graftInnerEdge qΓ qΔ e) := rfl

@[simp] theorem graftLabelEquiv_symm_outer (d : ℕ) (labΓ : Edge qΓ → Fin d)
    (labΔ : Edge qΔ → Fin d) (e : Edge qΓ) :
    (graftLabelEquiv qΓ qΔ d).symm (labΓ, labΔ) (graftOuterEdge qΓ qΔ e) = labΓ e := by
  have h := congrArg (fun p : (Edge qΓ → Fin d) × (Edge qΔ → Fin d) ↦ p.1 e)
    ((graftLabelEquiv qΓ qΔ d).apply_symm_apply (labΓ, labΔ))
  exact h

@[simp] theorem graftLabelEquiv_symm_inner (d : ℕ) (labΓ : Edge qΓ → Fin d)
    (labΔ : Edge qΔ → Fin d) (e : Edge qΔ) :
    (graftLabelEquiv qΓ qΔ d).symm (labΓ, labΔ) (graftInnerEdge qΓ qΔ e) = labΔ e := by
  have h := congrArg (fun p : (Edge qΓ → Fin d) × (Edge qΔ → Fin d) ↦ p.2 e)
    ((graftLabelEquiv qΓ qΔ d).apply_symm_apply (labΓ, labΔ))
  exact h

section Tensors

variable {R : Type*} [CommRing R] {d : ℕ}

/-- Concatenate the actual tensor families, preserving every ordered outgoing slot. -/
def graftTensors (TΓ : (v : Fin a) → Tensor (qΓ v) d R)
    (TΔ : (v : Fin b) → Tensor (qΔ v) d R) :
    (v : Fin (a + b)) → Tensor (graftArity qΓ qΔ v) d R :=
  Fin.addCases
    (fun v lab ↦ TΓ v (fun j ↦ lab (Fin.cast (graftArity_outer qΓ qΔ v).symm j)))
    (fun v lab ↦ TΔ v (fun j ↦ lab (Fin.cast (graftArity_inner qΓ qΔ v).symm j)))

theorem graftTensors_outer (TΓ : (v : Fin a) → Tensor (qΓ v) d R)
    (TΔ : (v : Fin b) → Tensor (qΔ v) d R) (v : Fin a)
    (lab : Fin (graftArity qΓ qΔ (Fin.castAdd b v)) → Fin d) :
    graftTensors qΓ qΔ TΓ TΔ (Fin.castAdd b v) lab =
      TΓ v (fun j ↦ lab (Fin.cast (graftArity_outer qΓ qΔ v).symm j)) := by
  simp [graftTensors]

theorem graftTensors_inner (TΓ : (v : Fin a) → Tensor (qΓ v) d R)
    (TΔ : (v : Fin b) → Tensor (qΔ v) d R) (v : Fin b)
    (lab : Fin (graftArity qΓ qΔ (Fin.natAdd a v)) → Fin d) :
    graftTensors qΓ qΔ TΓ TΔ (Fin.natAdd a v) lab =
      TΔ v (fun j ↦ lab (Fin.cast (graftArity_inner qΓ qΔ v).symm j)) := by
  simp [graftTensors]

@[simp] theorem graftTensors_outer_labels (TΓ : (v : Fin a) → Tensor (qΓ v) d R)
    (TΔ : (v : Fin b) → Tensor (qΔ v) d R) (v : Fin a)
    (lab : Edge (graftArity qΓ qΔ) → Fin d) :
    graftTensors qΓ qΔ TΓ TΔ (Fin.castAdd b v) (fun j ↦ lab ⟨Fin.castAdd b v, j⟩) =
      TΓ v (fun j ↦ lab (graftOuterEdge qΓ qΔ ⟨v, j⟩)) := by
  rw [graftTensors_outer]
  congr 1
  funext j
  rw [graftOuterEdge_mk]

@[simp] theorem graftTensors_inner_labels (TΓ : (v : Fin a) → Tensor (qΓ v) d R)
    (TΔ : (v : Fin b) → Tensor (qΔ v) d R) (v : Fin b)
    (lab : Edge (graftArity qΓ qΔ) → Fin d) :
    graftTensors qΓ qΔ TΓ TΔ (Fin.natAdd a v) (fun j ↦ lab ⟨Fin.natAdd a v, j⟩) =
      TΔ v (fun j ↦ lab (graftInnerEdge qΓ qΔ ⟨v, j⟩)) := by
  rw [graftTensors_inner]
  congr 1
  funext j
  rw [graftInnerEdge_mk]

end Tensors

variable {qΓ qΔ}

/-- The inner exterior block starts at the selected slot and preserves its order. -/
def graftInnerBoundary (r : Fin (m + 1)) (k : Fin (l + 1)) : Fin (m + l + 1) :=
  ⟨r.val + k.val, by omega⟩

/-- Exterior vertices after the insertion slot move right by `l` positions.
At the insertion slot this total map returns the left endpoint of the inner block. -/
def graftOuterBoundary (r j : Fin (m + 1)) : Fin (m + l + 1) :=
  ⟨if j.val ≤ r.val then j.val else j.val + l, by split <;> omega⟩

/-- Contract the whole inner exterior block to the original insertion slot. -/
def graftBoundaryCollapse (r : Fin (m + 1)) (k : Fin (m + l + 1)) : Fin (m + 1) :=
  ⟨if k.val < r.val then k.val else if k.val ≤ r.val + l then r.val else k.val - l,
    by split_ifs <;> omega⟩

@[simp] theorem graftInnerBoundary_val (r : Fin (m + 1)) (k : Fin (l + 1)) :
    (graftInnerBoundary r k).val = r.val + k.val := rfl

@[simp] theorem graftOuterBoundary_val (r j : Fin (m + 1)) :
    (graftOuterBoundary (l := l) r j).val = if j.val ≤ r.val then j.val else j.val + l := rfl

@[simp] theorem graftBoundaryCollapse_inner (r : Fin (m + 1)) (k : Fin (l + 1)) :
    graftBoundaryCollapse r (graftInnerBoundary r k) = r := by
  apply Fin.ext
  simp [graftBoundaryCollapse, graftInnerBoundary]
  omega

@[simp] theorem graftBoundaryCollapse_outer (r j : Fin (m + 1)) :
    graftBoundaryCollapse r (graftOuterBoundary (l := l) r j) = j := by
  apply Fin.ext
  simp only [graftBoundaryCollapse, graftOuterBoundary]
  split_ifs <;> omega

@[simp] theorem graftOuterBoundary_self (r : Fin (m + 1)) :
    graftOuterBoundary (l := l) r r = graftInnerBoundary r 0 := by
  apply Fin.ext
  simp

theorem graftInnerBoundary_injective (r : Fin (m + 1)) :
    Function.Injective (graftInnerBoundary (l := l) r) := by
  intro j k h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa using this

theorem graftOuterBoundary_injective (r : Fin (m + 1)) :
    Function.Injective (graftOuterBoundary (l := l) r) := by
  intro j k h
  simpa using congrArg (graftBoundaryCollapse r) h

theorem graftInnerBoundary_ne_outer (r j : Fin (m + 1)) (hj : j ≠ r)
    (k : Fin (l + 1)) : graftInnerBoundary r k ≠ graftOuterBoundary r j := by
  intro h
  apply hj
  have hh : r = j := by simpa using congrArg (graftBoundaryCollapse r) h
  exact hh.symm

private theorem graftBoundarySum_bijective (r : Fin (m + 1)) :
    Function.Bijective (Sum.elim (graftInnerBoundary (l := l) r)
      (fun j : {j : Fin (m + 1) // j ≠ r} ↦ graftOuterBoundary r j.val)) := by
  constructor
  · rintro (j | j) (k | k) h
    · exact congrArg Sum.inl (graftInnerBoundary_injective r h)
    · exact False.elim (graftInnerBoundary_ne_outer r k.val k.property j h)
    · exact False.elim (graftInnerBoundary_ne_outer r j.val j.property k h.symm)
    · exact congrArg Sum.inr (Subtype.ext (graftOuterBoundary_injective r h))
  · intro k
    by_cases hleft : k.val < r.val
    · refine ⟨Sum.inr ⟨⟨k.val, by omega⟩, ?_⟩, ?_⟩
      · intro h
        have hh : k.val = r.val := congrArg Fin.val h
        omega
      apply Fin.ext
      change (if k.val ≤ r.val then k.val else k.val + l) = k.val
      rw [if_pos (Nat.le_of_lt hleft)]
    · by_cases hblock : k.val ≤ r.val + l
      · refine ⟨Sum.inl ⟨k.val - r.val, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [Sum.elim_inl, graftInnerBoundary_val]
        omega
      · refine ⟨Sum.inr ⟨⟨k.val - l, by omega⟩, ?_⟩, ?_⟩
        · intro h
          have hh : k.val - l = r.val := congrArg Fin.val h
          omega
        apply Fin.ext
        simp only [Sum.elim_inr, graftOuterBoundary_val]
        split_ifs <;> omega

/-- The output exterior vertices are exactly the ordered inner block and the unaffected
outer vertices. Its inverse uses the explicit boundary maps, with no arbitrary enumeration. -/
def graftBoundaryEquiv (r : Fin (m + 1)) :
    Fin (m + l + 1) ≃ Fin (l + 1) ⊕ {j : Fin (m + 1) // j ≠ r} :=
  (Equiv.ofBijective _ (graftBoundarySum_bijective (l := l) r)).symm

@[simp] theorem graftBoundaryEquiv_symm_inner (r : Fin (m + 1)) (k : Fin (l + 1)) :
    (graftBoundaryEquiv r).symm (Sum.inl k) = graftInnerBoundary r k := rfl

@[simp] theorem graftBoundaryEquiv_symm_outer (r : Fin (m + 1))
    (j : {j : Fin (m + 1) // j ≠ r}) :
    (graftBoundaryEquiv (l := l) r).symm (Sum.inr j) = graftOuterBoundary r j.val := rfl

@[simp] theorem graftBoundaryEquiv_inner (r : Fin (m + 1)) (k : Fin (l + 1)) :
    graftBoundaryEquiv r (graftInnerBoundary r k) = Sum.inl k :=
  (graftBoundaryEquiv r).apply_symm_apply (Sum.inl k)

@[simp] theorem graftBoundaryEquiv_outer (r j : Fin (m + 1)) (hj : j ≠ r) :
    graftBoundaryEquiv (l := l) r (graftOuterBoundary r j) = Sum.inr ⟨j, hj⟩ :=
  (graftBoundaryEquiv r).apply_symm_apply (Sum.inr ⟨j, hj⟩)

/-- Embedding of all inner vertices, including its consecutive exterior block. -/
def graftInnerVertex (r : Fin (m + 1)) : Vertex b (l + 1) → Vertex (a + b) (m + l + 1) :=
  Sum.map (Fin.natAdd a) (graftInnerBoundary r)

/-- The total outer vertex embedding; its value at `r` will be overridden by each edge choice. -/
def graftOuterVertex (r : Fin (m + 1)) : Vertex a (m + 1) → Vertex (a + b) (m + l + 1) :=
  Sum.map (Fin.castAdd b) (graftOuterBoundary r)

/-- Collapse all inner internal vertices and the whole exterior block to the insertion slot. -/
def graftCollapse (r : Fin (m + 1)) : Vertex (a + b) (m + l + 1) → Vertex a (m + 1) :=
  Sum.elim (fun v ↦ Sum.elim Sum.inl (fun _ ↦ Sum.inr r) (finSumFinEquiv.symm v))
    (fun k ↦ Sum.inr (graftBoundaryCollapse r k))

@[simp] theorem graftCollapse_inner (r : Fin (m + 1)) (v : Vertex b (l + 1)) :
    graftCollapse (a := a) r (graftInnerVertex r v) = Sum.inr r := by
  cases v <;> simp [graftCollapse, graftInnerVertex]

@[simp] theorem graftCollapse_outer (r : Fin (m + 1)) (v : Vertex a (m + 1)) :
    graftCollapse r (graftOuterVertex (b := b) (l := l) r v) = v := by
  cases v <;> simp [graftCollapse, graftOuterVertex]

theorem graftInnerVertex_injective (r : Fin (m + 1)) :
    Function.Injective (graftInnerVertex (a := a) (b := b) (l := l) r) := by
  rintro (i | i) (j | j) h
  · simp only [graftInnerVertex, Sum.map_inl, Sum.inl.injEq, Fin.natAdd_inj] at h
    exact congrArg Sum.inl h
  · simp [graftInnerVertex] at h
  · simp [graftInnerVertex] at h
  · exact congrArg Sum.inr (graftInnerBoundary_injective r (Sum.inr.inj h))

theorem graftOuterVertex_injective (r : Fin (m + 1)) :
    Function.Injective (graftOuterVertex (a := a) (b := b) (l := l) r) := by
  intro v w h
  simpa using congrArg (graftCollapse r) h

theorem graftInnerVertex_ne_outer (r : Fin (m + 1)) (v : Vertex a (m + 1))
    (hv : v ≠ Sum.inr r) (w : Vertex b (l + 1)) :
    graftInnerVertex r w ≠ graftOuterVertex r v := by
  intro h
  apply hv
  have hh : Sum.inr r = v := by simpa using congrArg (graftCollapse r) h
  exact hh.symm

namespace Graph

variable (Γ : Graph qΓ (m + 1)) (Δ : Graph qΔ (l + 1)) (r : Fin (m + 1))

/-- Each outer edge aimed at the insertion slot chooses any inner vertex. -/
abbrev GraftChoices := {e : Edge qΓ // Γ.target e = Sum.inr r} → Vertex b (l + 1)

/-- Extend choices off the insertion fibre by the first inner exterior vertex. -/
def graftChoice (χ : Γ.GraftChoices (b := b) (l := l) r) (e : Edge qΓ) :
    Vertex b (l + 1) :=
  if h : Γ.target e = Sum.inr r then χ ⟨e, h⟩ else Sum.inr 0

@[simp] theorem graftChoice_of_hit (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) (h : Γ.target e = Sum.inr r) : Γ.graftChoice r χ e = χ ⟨e, h⟩ := by
  simp [graftChoice, h]

/-- Outer edges arriving at the insertion slot are retargeted according to their choice. -/
def graftOuterTarget (χ : Γ.GraftChoices (b := b) (l := l) r) (e : Edge qΓ) :
    Vertex (a + b) (m + l + 1) :=
  if h : Γ.target e = Sum.inr r then graftInnerVertex r (χ ⟨e, h⟩)
  else graftOuterVertex r (Γ.target e)

@[simp] theorem collapse_graftOuterTarget (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) : graftCollapse r (Γ.graftOuterTarget r χ e) = Γ.target e := by
  by_cases h : Γ.target e = Sum.inr r <;> simp [graftOuterTarget, h]

/-- Actual target function of the grafted graph. -/
def graftTarget (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge (graftArity qΓ qΔ)) : Vertex (a + b) (m + l + 1) :=
  Sum.elim (Γ.graftOuterTarget r χ) (fun f ↦ graftInnerVertex r (Δ.target f))
    (graftEdgeEquiv qΓ qΔ e)

@[simp] theorem graftTarget_outer (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) :
    Γ.graftTarget Δ r χ (graftOuterEdge qΓ qΔ e) = Γ.graftOuterTarget r χ e := by
  simp [graftTarget]

@[simp] theorem graftTarget_inner (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΔ) :
    Γ.graftTarget Δ r χ (graftInnerEdge qΓ qΔ e) = graftInnerVertex r (Δ.target e) := by
  simp [graftTarget]

private theorem graftTarget_noLoops (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge (graftArity qΓ qΔ)) : Γ.graftTarget Δ r χ e ≠ Sum.inl e.1 := by
  obtain ⟨f, rfl⟩ := (graftEdgeEquiv qΓ qΔ).symm.surjective e
  rcases f with f | f
  · change Γ.graftTarget Δ r χ (graftOuterEdge qΓ qΔ f) ≠
      Sum.inl (graftOuterEdge qΓ qΔ f).1
    rw [graftTarget_outer, graftOuterEdge_source]
    intro h
    apply Γ.noLoops f.1 f.2
    have hh := congrArg (graftCollapse r) h
    rw [collapse_graftOuterTarget] at hh
    simpa [graftCollapse] using hh
  · change Γ.graftTarget Δ r χ (graftInnerEdge qΓ qΔ f) ≠
      Sum.inl (graftInnerEdge qΓ qΔ f).1
    rw [graftTarget_inner, graftInnerEdge_source]
    intro h
    apply Δ.noLoops f.1 f.2
    apply graftInnerVertex_injective r
    simpa [graftInnerVertex] using h

private theorem graftTarget_eq_of_same_source
    (χ : Γ.GraftChoices (b := b) (l := l) r) (e f : Edge (graftArity qΓ qΔ))
    (hs : e.1 = f.1) (ht : Γ.graftTarget Δ r χ e = Γ.graftTarget Δ r χ f) : e = f := by
  obtain ⟨e, rfl⟩ := (graftEdgeEquiv qΓ qΔ).symm.surjective e
  obtain ⟨f, rfl⟩ := (graftEdgeEquiv qΓ qΔ).symm.surjective f
  rcases e with ⟨v, i⟩ | ⟨v, i⟩ <;> rcases f with ⟨w, j⟩ | ⟨w, j⟩
  · change (graftOuterEdge qΓ qΔ ⟨v, i⟩).1 = (graftOuterEdge qΓ qΔ ⟨w, j⟩).1 at hs
    simp only [graftOuterEdge_source, Fin.castAdd_inj] at hs
    subst w
    have ht' : Γ.target ⟨v, i⟩ = Γ.target ⟨v, j⟩ := by
      change Γ.graftTarget Δ r χ (graftOuterEdge qΓ qΔ ⟨v, i⟩) =
        Γ.graftTarget Δ r χ (graftOuterEdge qΓ qΔ ⟨v, j⟩) at ht
      simpa using congrArg (graftCollapse r) ht
    have hij := Γ.distinctTargets v ht'
    subst j
    rfl
  · change Fin.castAdd b v = Fin.natAdd a w at hs
    have := congrArg finSumFinEquiv.symm hs
    simp at this
  · change Fin.natAdd a v = Fin.castAdd b w at hs
    have := congrArg finSumFinEquiv.symm hs
    simp at this
  · change (graftInnerEdge qΓ qΔ ⟨v, i⟩).1 = (graftInnerEdge qΓ qΔ ⟨w, j⟩).1 at hs
    simp only [graftInnerEdge_source, Fin.natAdd_inj] at hs
    subst w
    have ht' : Δ.target ⟨v, i⟩ = Δ.target ⟨v, j⟩ := by
      apply graftInnerVertex_injective r
      change Γ.graftTarget Δ r χ (graftInnerEdge qΓ qΔ ⟨v, i⟩) =
        Γ.graftTarget Δ r χ (graftInnerEdge qΓ qΔ ⟨v, j⟩) at ht
      simpa using ht
    have hij := Δ.distinctTargets v ht'
    subst j
    rfl

/-- Genuine insertion of an admissible graph into an exterior slot of another admissible
graph, including arbitrary internal outgoing arities and all choices of incoming targets. -/
def graft (χ : Γ.GraftChoices (b := b) (l := l) r) :
    Graph (graftArity qΓ qΔ) (m + l + 1) where
  target := Γ.graftTarget Δ r χ
  noLoops v j := Γ.graftTarget_noLoops Δ r χ ⟨v, j⟩
  distinctTargets v i j h := by
    have hh := Γ.graftTarget_eq_of_same_source Δ r χ ⟨v, i⟩ ⟨v, j⟩ rfl h
    apply Fin.ext
    exact congrArg (fun e : Edge (graftArity qΓ qΔ) ↦ e.2.val) hh

@[simp] theorem graft_target_outer (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) :
    (Γ.graft Δ r χ).target (graftOuterEdge qΓ qΔ e) = Γ.graftOuterTarget r χ e :=
  Γ.graftTarget_outer Δ r χ e

@[simp] theorem graft_target_inner (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΔ) :
    (Γ.graft Δ r χ).target (graftInnerEdge qΓ qΔ e) = graftInnerVertex r (Δ.target e) :=
  Γ.graftTarget_inner Δ r χ e

theorem graftOuterTarget_eq_outer_iff (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) (v : Vertex a (m + 1)) (hv : v ≠ Sum.inr r) :
    Γ.graftOuterTarget r χ e = graftOuterVertex r v ↔ Γ.target e = v := by
  constructor
  · intro h
    simpa using congrArg (graftCollapse r) h
  · intro h
    simp [graftOuterTarget, h, hv]

theorem graftOuterTarget_eq_inner_iff (χ : Γ.GraftChoices (b := b) (l := l) r)
    (e : Edge qΓ) (w : Vertex b (l + 1)) :
    Γ.graftOuterTarget r χ e = graftInnerVertex r w ↔
      Γ.target e = Sum.inr r ∧ Γ.graftChoice r χ e = w := by
  by_cases h : Γ.target e = Sum.inr r
  · simp [graftOuterTarget, h, (graftInnerVertex_injective r).eq_iff]
  · simp only [h, false_and, iff_false]
    intro he
    apply h
    simpa using congrArg (graftCollapse r) he

/-- Original outer edges assigned to a specified inner vertex. -/
def graftAssignedEdges (χ : Γ.GraftChoices (b := b) (l := l) r)
    (w : Vertex b (l + 1)) : Finset (Edge qΓ) :=
  (Γ.incoming (Sum.inr r)).filter (fun e ↦ Γ.graftChoice r χ e = w)

@[simp] theorem mem_graftAssignedEdges (χ : Γ.GraftChoices (b := b) (l := l) r)
    (w : Vertex b (l + 1)) (e : Edge qΓ) :
    e ∈ Γ.graftAssignedEdges r χ w ↔
      Γ.target e = Sum.inr r ∧ Γ.graftChoice r χ e = w := by
  simp [graftAssignedEdges, incoming]

/-- Any unaffected outer vertex receives exactly the embedded original outer edges. -/
theorem incoming_graft_outer (χ : Γ.GraftChoices (b := b) (l := l) r)
    (v : Vertex a (m + 1)) (hv : v ≠ Sum.inr r) :
    (Γ.graft Δ r χ).incoming (graftOuterVertex r v) =
      (Γ.incoming v).map (graftOuterEdge qΓ qΔ) := by
  ext e
  obtain ⟨e, rfl⟩ := (graftEdgeEquiv qΓ qΔ).symm.surjective e
  rcases e with e | e
  · change graftOuterEdge qΓ qΔ e ∈ _ ↔ graftOuterEdge qΓ qΔ e ∈ _
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      graft_target_outer, graftOuterTarget_eq_outer_iff Γ r χ e v hv,
      Finset.mem_map, graftOuterEdge_eq_iff]
    simp
  · change graftInnerEdge qΓ qΔ e ∈ _ ↔ graftInnerEdge qΓ qΔ e ∈ _
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      graft_target_inner, Finset.mem_map]
    simp [graftInnerVertex_ne_outer r v hv, graftOuterEdge_ne_inner]

@[simp] theorem incoming_graft_outer_internal (χ : Γ.GraftChoices (b := b) (l := l) r)
    (v : Fin a) :
    (Γ.graft Δ r χ).incoming (Sum.inl (Fin.castAdd b v)) =
      (Γ.incoming (Sum.inl v)).map (graftOuterEdge qΓ qΔ) :=
  Γ.incoming_graft_outer Δ r χ (Sum.inl v) (by simp)

theorem incoming_graft_outer_boundary (χ : Γ.GraftChoices (b := b) (l := l) r)
    (j : Fin (m + 1)) (hj : j ≠ r) :
    (Γ.graft Δ r χ).incoming (Sum.inr (graftOuterBoundary r j)) =
      (Γ.incoming (Sum.inr j)).map (graftOuterEdge qΓ qΔ) :=
  Γ.incoming_graft_outer Δ r χ (Sum.inr j) (by simpa)

/-- The inner graph edges and the reattached outer edges are disjoint edge colours. -/
theorem graft_incoming_parts_disjoint (χ : Γ.GraftChoices (b := b) (l := l) r)
    (w : Vertex b (l + 1)) :
    Disjoint ((Δ.incoming w).map (graftInnerEdge qΓ qΔ))
      ((Γ.graftAssignedEdges r χ w).map (graftOuterEdge qΓ qΔ)) := by
  apply Finset.disjoint_left.mpr
  intro e hi ho
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp ho
  exact graftOuterEdge_ne_inner qΓ qΔ j i hj

/-- Each inner vertex receives its original inner incoming edges together with precisely
the outer incoming edges assigned to it. The two finsets are disjoint. -/
theorem incoming_graft_inner (χ : Γ.GraftChoices (b := b) (l := l) r)
    (w : Vertex b (l + 1)) :
    (Γ.graft Δ r χ).incoming (graftInnerVertex r w) =
      (Δ.incoming w).map (graftInnerEdge qΓ qΔ) ∪
        (Γ.graftAssignedEdges r χ w).map (graftOuterEdge qΓ qΔ) := by
  ext e
  obtain ⟨e, rfl⟩ := (graftEdgeEquiv qΓ qΔ).symm.surjective e
  rcases e with e | e
  · change graftOuterEdge qΓ qΔ e ∈ _ ↔ graftOuterEdge qΓ qΔ e ∈ _
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      graft_target_outer, graftOuterTarget_eq_inner_iff, Finset.mem_union,
      Finset.mem_map, graftOuterEdge_eq_iff]
    simp [ne_comm, graftOuterEdge_ne_inner]
  · change graftInnerEdge qΓ qΔ e ∈ _ ↔ graftInnerEdge qΓ qΔ e ∈ _
    simp only [incoming, Finset.mem_filter, Finset.mem_univ, true_and,
      graft_target_inner, (graftInnerVertex_injective r).eq_iff, Finset.mem_union,
      Finset.mem_map, graftInnerEdge_eq_iff]
    simp [graftOuterEdge_ne_inner]

end Graph

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
