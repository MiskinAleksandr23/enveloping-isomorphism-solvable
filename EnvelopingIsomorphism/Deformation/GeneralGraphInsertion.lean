import EnvelopingIsomorphism.Deformation.GraphLeibnizFinset
import EnvelopingIsomorphism.Deformation.GeneralGraphExternalSplit
import EnvelopingIsomorphism.Deformation.GeneralGraphGraftConstruction
import Mathlib.Algebra.BigOperators.Fin

/-! Composition of actual polynomial graph cochains. The coefficient algebra
is handled by finite-edge Leibniz expansion before identifying the resulting
terms with admissible grafted graphs. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open MvPolynomial
open scoped BigOperators

section DerivativeComposition

variable {R σ : Type*} [CommRing R]

theorem iteratedPDeriv_append (s t : List σ) :
    iteratedPDeriv (k := R) (s ++ t) = (iteratedPDeriv s).comp (iteratedPDeriv t) := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    simp only [List.cons_append, iteratedPDeriv, ih, LinearMap.comp_assoc]

variable {α β : Type*} {d : ℕ}

theorem iteratedPDeriv_finset_map (s : Finset α) (e : α ↪ β) (lab : β → Fin d) :
    iteratedPDeriv (k := R) ((s.map e).toList.map lab) =
      iteratedPDeriv (s.toList.map (fun a ↦ lab (e a))) := by
  classical
  apply KontsevichGraph.General.iteratedPDeriv_perm
  have h : (s.map e).toList.Perm (s.toList.map e) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      ((Finset.nodup_toList _).map e.injective)).mpr
    intro b
    simp
  simpa only [List.map_map, Function.comp_def] using h.map lab

theorem iteratedPDeriv_finset_union [DecidableEq α] (s t : Finset α)
    (hst : Disjoint s t) (lab : α → Fin d) :
    iteratedPDeriv (k := R) ((s ∪ t).toList.map lab) =
      (iteratedPDeriv (s.toList.map lab)).comp (iteratedPDeriv (t.toList.map lab)) := by
  have hd : List.Disjoint s.toList t.toList := by
    simpa only [List.disjoint_left, Finset.mem_toList] using (Finset.disjoint_left.mp hst)
  have h : (s ∪ t).toList.Perm (s.toList ++ t.toList) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      ((Finset.nodup_toList _).append (Finset.nodup_toList _) hd)).mpr
    intro a
    simp
  have he := KontsevichGraph.General.iteratedPDeriv_perm (R := R) (h.map lab)
  rw [List.map_append, iteratedPDeriv_append] at he
  exact he

end DerivativeComposition

namespace KontsevichGraph.General.Graph

variable {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin n → ℕ}

/-- The actual polynomial at each vertex before its incoming derivatives act. -/
def contractionInput (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) : Vertex n m → Polynomial d R :=
  Sum.elim (fun v ↦ T v (fun a ↦ lab ⟨v, a⟩)) f

@[simp] theorem contractionInput_internal (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) (v : Fin n) :
    contractionInput lab T f (Sum.inl v) = T v (fun a ↦ lab ⟨v, a⟩) := rfl

@[simp] theorem contractionInput_external (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) (j : Fin m) :
    contractionInput lab T f (Sum.inr j) = f j := rfl

theorem cochainOperator_vertex_product (Γ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator T f = ∑ lab : Edge q → Fin d,
      ∏ v : Vertex n m, Γ.vertexDerivative lab v (contractionInput lab T f v) := by
  rw [cochainOperator_apply]
  apply Finset.sum_congr rfl
  intro lab hlab
  rw [Fintype.prod_sum_type]
  rfl

/-- Each incoming outer arrow independently differentiates one inner graph vertex.
This is the full finite expansion, retaining both internal and external factors. -/
theorem incoming_derivative_cochainOperator {α : Type*} [DecidableEq α]
    (s : Finset α) (outerLab : α → Fin d) (Δ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    iteratedPDeriv (s.toList.map outerLab) (Δ.cochainOperator T f) =
      ∑ χ : s → Vertex n m, ∑ innerLab : Edge q → Fin d,
        ∏ v : Vertex n m, iteratedPDeriv ((assignedEdges s χ v).toList.map outerLab)
          (Δ.vertexDerivative innerLab v (contractionInput innerLab T f v)) := by
  classical
  rw [cochainOperator_vertex_product, map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro innerLab hLab
  exact iteratedPDeriv_edge_prod s outerLab
    (fun v ↦ Δ.vertexDerivative innerLab v (contractionInput innerLab T f v))

/-- Factors of an outer graph which do not depend on the slot being substituted. -/
def insertionOuterFactor (Γ : Graph q m) (r : Fin m) (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) : Polynomial d R :=
  (∏ v : Fin n, Γ.vertexDerivative lab (Sum.inl v) (T v (fun a ↦ lab ⟨v, a⟩))) *
    ∏ j ∈ Finset.univ.erase r, Γ.vertexDerivative lab (Sum.inr j) (f j)

theorem cochainOperator_update_factor (Γ : Graph q m) (r : Fin m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) (p : Polynomial d R) :
    Γ.cochainOperator T (Function.update f r p) = ∑ lab : Edge q → Fin d,
      Γ.insertionOuterFactor r lab T f * Γ.vertexDerivative lab (Sum.inr r) p := by
  classical
  rw [cochainOperator_apply]
  apply Finset.sum_congr rfl
  intro lab hlab
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), Function.update_self]
  have hrest : (∏ j ∈ Finset.univ.erase r, Γ.vertexDerivative lab (Sum.inr j) (Function.update f r p j)) =
      ∏ j ∈ Finset.univ.erase r, Γ.vertexDerivative lab (Sum.inr j) (f j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hrest]
  simp only [insertionOuterFactor]
  ring

/-- The complete labelled expansion of a graph cochain inserted into one outer slot.
Each incoming outer arrow is assigned to one actual inner vertex. -/
theorem cochainOperator_insertion_expansion {b l : ℕ} {q' : Fin b → ℕ}
    (Γ : Graph q m) (r : Fin m) (Δ : Graph q' l)
    (T : (v : Fin n) → Tensor (q v) d R) (U : (v : Fin b) → Tensor (q' v) d R)
    (f : Fin m → Polynomial d R) (g : Fin l → Polynomial d R) :
    Γ.cochainOperator T (Function.update f r (Δ.cochainOperator U g)) =
      ∑ χ : Γ.incoming (Sum.inr r) → Vertex b l,
        ∑ outerLab : Edge q → Fin d, ∑ innerLab : Edge q' → Fin d,
          Γ.insertionOuterFactor r outerLab T f *
            ∏ v : Vertex b l,
              iteratedPDeriv ((assignedEdges (Γ.incoming (Sum.inr r)) χ v).toList.map outerLab)
                (Δ.vertexDerivative innerLab v (contractionInput innerLab U g v)) := by
  classical
  rw [cochainOperator_update_factor]
  simp only [vertexDerivative, incoming_derivative_cochainOperator, Finset.mul_sum]
  rw [Finset.sum_comm]

end KontsevichGraph.General.Graph

namespace KontsevichGraph.General.Graph

variable {R : Type*} [CommRing R] {a b m l d : ℕ}
variable {qΓ : Fin a → ℕ} {qΔ : Fin b → ℕ}
variable (Γ : Graph qΓ (m + 1)) (Δ : Graph qΔ (l + 1)) (r : Fin (m + 1))

def graftChoicesEquiv : Γ.GraftChoices (b := b) (l := l) r ≃
    (Γ.incoming (Sum.inr r) → Vertex b (l + 1)) :=
  Equiv.arrowCongr (Γ.incomingSubtypeEquiv r).symm (Equiv.refl _)

theorem assignedEdges_graftChoicesEquiv (χ : Γ.GraftChoices (b := b) (l := l) r)
    (v : Vertex b (l + 1)) :
    assignedEdges (Γ.incoming (Sum.inr r)) (Γ.graftChoicesEquiv r χ) v = Γ.graftAssignedEdges r χ v := by
  classical
  ext e
  rw [mem_assignedEdges, mem_graftAssignedEdges]
  constructor
  · rintro ⟨he, hc⟩
    have hh : Γ.target e = Sum.inr r := (Γ.incomingSubtypeEquiv r ⟨e, he⟩).property
    refine ⟨hh, ?_⟩
    rw [graftChoice_of_hit Γ r χ e hh]
    exact hc
  · rintro ⟨hh, hc⟩
    have he : e ∈ Γ.incoming (Sum.inr r) := by simp [incoming, hh]
    refine ⟨he, ?_⟩
    rw [graftChoice_of_hit Γ r χ e hh] at hc
    exact hc

theorem vertexDerivative_graft_outer (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d)
    (v : Vertex a (m + 1)) (hv : v ≠ Sum.inr r) :
    (Γ.graft Δ r χ).vertexDerivative (R := R) lab (graftOuterVertex r v) =
      Γ.vertexDerivative (graftLabelEquiv qΓ qΔ d lab).1 v := by
  rw [vertexDerivative, incoming_graft_outer Γ Δ r χ v hv, iteratedPDeriv_finset_map]
  rfl

theorem vertexDerivative_graft_inner (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d) (v : Vertex b (l + 1)) :
    (Γ.graft Δ r χ).vertexDerivative (R := R) lab (graftInnerVertex r v) =
      (iteratedPDeriv ((Γ.graftAssignedEdges r χ v).toList.map (graftLabelEquiv qΓ qΔ d lab).1)).comp
        (Δ.vertexDerivative (graftLabelEquiv qΓ qΔ d lab).2 v) := by
  rw [vertexDerivative, incoming_graft_inner, Finset.union_comm,
    iteratedPDeriv_finset_union _ _ (Γ.graft_incoming_parts_disjoint Δ r χ v).symm,
    iteratedPDeriv_finset_map, iteratedPDeriv_finset_map]
  rfl

def graftInnerFactor (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d)
    (U : (v : Fin b) → Tensor (qΔ v) d R) (f : Fin (m + l + 1) → Polynomial d R)
    (v : Vertex b (l + 1)) : Polynomial d R :=
  iteratedPDeriv ((Γ.graftAssignedEdges r χ v).toList.map (graftLabelEquiv qΓ qΔ d lab).1)
    (Δ.vertexDerivative (graftLabelEquiv qΓ qΔ d lab).2 v
      (contractionInput (graftLabelEquiv qΓ qΔ d lab).2 U (fun j ↦ f (graftInnerBoundary r j)) v))

theorem graft_internal_product (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R)
    (f : Fin (m + l + 1) → Polynomial d R) :
    (∏ v : Fin (a + b), (Γ.graft Δ r χ).vertexDerivative lab (Sum.inl v)
      (graftTensors qΓ qΔ T U v (fun j ↦ lab ⟨v, j⟩))) =
      (∏ v : Fin a, Γ.vertexDerivative (graftLabelEquiv qΓ qΔ d lab).1 (Sum.inl v)
        (T v (fun j ↦ (graftLabelEquiv qΓ qΔ d lab).1 ⟨v, j⟩))) *
        ∏ v : Fin b, Γ.graftInnerFactor Δ r χ lab U f (Sum.inl v) := by
  rw [Fin.prod_univ_add]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v hv
    rw [graftTensors_outer_labels]
    change (Γ.graft Δ r χ).vertexDerivative lab (graftOuterVertex r (Sum.inl v)) _ = _
    rw [vertexDerivative_graft_outer Γ Δ r χ lab (Sum.inl v) (by simp)]
    rfl
  · apply Finset.prod_congr rfl
    intro v hv
    rw [graftTensors_inner_labels]
    change (Γ.graft Δ r χ).vertexDerivative lab (graftInnerVertex r (Sum.inl v)) _ = _
    rw [vertexDerivative_graft_inner]
    rfl

theorem graft_external_product (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d)
    (U : (v : Fin b) → Tensor (qΔ v) d R) (f : Fin (m + l + 1) → Polynomial d R) :
    (∏ j : Fin (m + l + 1), (Γ.graft Δ r χ).vertexDerivative lab (Sum.inr j) (f j)) =
      (∏ j : Fin (l + 1), Γ.graftInnerFactor Δ r χ lab U f (Sum.inr j)) *
        ∏ j ∈ Finset.univ.erase r,
          Γ.vertexDerivative (graftLabelEquiv qΓ qΔ d lab).1 (Sum.inr j) (f (graftOuterBoundary r j)) := by
  classical
  let F : Fin (m + l + 1) → Polynomial d R := fun j ↦
    (Γ.graft Δ r χ).vertexDerivative lab (Sum.inr j) (f j)
  calc
    (∏ j, F j) = ∏ z : Fin (l + 1) ⊕ {j : Fin (m + 1) // j ≠ r},
        F ((graftBoundaryEquiv r).symm z) := by
      apply Fintype.prod_equiv (graftBoundaryEquiv r)
      intro j
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [graftBoundaryEquiv_symm_inner, graftBoundaryEquiv_symm_outer]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro j hj
        change (Γ.graft Δ r χ).vertexDerivative lab (graftInnerVertex r (Sum.inr j)) _ = _
        rw [vertexDerivative_graft_inner]
        rfl
      · rw [← Finset.prod_subtype (Finset.univ.erase r) (by intro j; simp)
          (fun j ↦ F (graftOuterBoundary r j))]
        apply Finset.prod_congr rfl
        intro j hj
        change (Γ.graft Δ r χ).vertexDerivative lab (graftOuterVertex r (Sum.inr j)) _ = _
        rw [vertexDerivative_graft_outer Γ Δ r χ lab (Sum.inr j)
          (by simpa using (Finset.mem_erase.mp hj).1)]

theorem graft_contraction_product (χ : Γ.GraftChoices (b := b) (l := l) r)
    (lab : Edge (graftArity qΓ qΔ) → Fin d)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R)
    (f : Fin (m + l + 1) → Polynomial d R) :
    ((∏ v : Fin (a + b), (Γ.graft Δ r χ).vertexDerivative lab (Sum.inl v)
        (graftTensors qΓ qΔ T U v (fun j ↦ lab ⟨v, j⟩))) *
      ∏ j : Fin (m + l + 1), (Γ.graft Δ r χ).vertexDerivative lab (Sum.inr j) (f j)) =
      Γ.insertionOuterFactor r (graftLabelEquiv qΓ qΔ d lab).1 T (fun j ↦ f (graftOuterBoundary r j)) *
        ∏ v : Vertex b (l + 1), Γ.graftInnerFactor Δ r χ lab U f v := by
  rw [graft_internal_product Γ Δ r χ lab T U f, graft_external_product Γ Δ r χ lab U f,
    Fintype.prod_sum_type]
  simp only [insertionOuterFactor]
  ring

/-- Reindexing the actual labels of a grafted graph separates the two original
label families, with all derivative assignments still explicit. -/
theorem cochainOperator_graft_expansion (χ : Γ.GraftChoices (b := b) (l := l) r)
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R)
    (f : Fin (m + l + 1) → Polynomial d R) :
    (Γ.graft Δ r χ).cochainOperator (graftTensors qΓ qΔ T U) f =
      ∑ outerLab : Edge qΓ → Fin d, ∑ innerLab : Edge qΔ → Fin d,
        Γ.insertionOuterFactor r outerLab T (fun j ↦ f (graftOuterBoundary r j)) *
          ∏ v : Vertex b (l + 1),
            iteratedPDeriv ((Γ.graftAssignedEdges r χ v).toList.map outerLab)
              (Δ.vertexDerivative innerLab v
                (contractionInput innerLab U (fun j ↦ f (graftInnerBoundary r j)) v)) := by
  classical
  rw [cochainOperator_apply]
  let F : (Edge qΓ → Fin d) × (Edge qΔ → Fin d) → Polynomial d R := fun p ↦
    Γ.insertionOuterFactor r p.1 T (fun j ↦ f (graftOuterBoundary r j)) *
      ∏ v : Vertex b (l + 1),
        iteratedPDeriv ((Γ.graftAssignedEdges r χ v).toList.map p.1)
          (Δ.vertexDerivative p.2 v
            (contractionInput p.2 U (fun j ↦ f (graftInnerBoundary r j)) v))
  calc
    _ = ∑ p, F p := by
      apply Fintype.sum_equiv (graftLabelEquiv qΓ qΔ d)
      intro lab
      exact graft_contraction_product Γ Δ r χ lab T U f
    _ = _ := Fintype.sum_prod_type F

/-- Actual graph-cochain insertion is the finite sum of actual admissible
grafts. Both external arities are positive; internal outgoing arities and
numbers of internal vertices are arbitrary. No weight identity is assumed. -/
theorem cochainOperator_graft
    (T : (v : Fin a) → Tensor (qΓ v) d R) (U : (v : Fin b) → Tensor (qΔ v) d R)
    (f : Fin (m + l + 1) → Polynomial d R) :
    Γ.cochainOperator T
        (Function.update (fun j ↦ f (graftOuterBoundary r j)) r
          (Δ.cochainOperator U (fun j ↦ f (graftInnerBoundary r j)))) =
      ∑ χ : Γ.GraftChoices (b := b) (l := l) r,
        (Γ.graft Δ r χ).cochainOperator (graftTensors qΓ qΔ T U) f := by
  classical
  rw [cochainOperator_insertion_expansion]
  symm
  apply Fintype.sum_equiv (Γ.graftChoicesEquiv r)
  intro χ
  rw [cochainOperator_graft_expansion]
  simp only [assignedEdges_graftChoicesEquiv]

end KontsevichGraph.General.Graph

end EnvelopingIsomorphism.Deformation
