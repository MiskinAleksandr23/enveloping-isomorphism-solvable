import EnvelopingIsomorphism.Deformation.GeneralGraphOperators

/-! Targeted constant-input vanishing for actual graph operators, and conditional weighted unit laws. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

/-- A nonempty actual list of formal partial derivatives kills every constant polynomial. -/
theorem iteratedPDeriv_C_of_ne_nil (ds : List σ) (r : R) (hds : ds ≠ []) :
    iteratedPDeriv ds (C r) = 0 := by
  induction ds with
  | nil => exact (hds rfl).elim
  | cons i ds ih =>
    by_cases htail : ds = []
    · subst ds
      simp only [iteratedPDeriv_cons, iteratedPDeriv_nil, pderiv_C]
    · rw [iteratedPDeriv_cons, ih htail, map_zero]

namespace KontsevichGraph.General

variable {n m d : ℕ} {q : Fin n → ℕ}

namespace Graph

theorem vertexDerivative_C_eq_zero (Γ : Graph q m) (lab : Edge q → Fin d) (v : Vertex n m)
    (h : (Γ.incoming v).Nonempty) (r : R) : Γ.vertexDerivative lab v (C r) = 0 := by
  apply iteratedPDeriv_C_of_ne_nil
  intro heq
  have hc : (Γ.incoming v).card = 0 := by
    simpa only [List.length_map, Finset.length_toList, List.length_nil] using congrArg List.length heq
  exact Finset.card_ne_zero.mpr h hc

/-- A labelled graph term vanishes on a constant exterior input when an edge hits that slot. -/
theorem labelledOperator_C_external (Γ : Graph q m) (lab : Edge q → Fin d)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (j : Fin m) (r : R) (hin : (Γ.incoming (.inr j)).Nonempty) (hf : f j = C r) :
    (Γ.labelledOperator lab).currySum T f = 0 := by
  rw [MultilinearMap.currySum_apply, labelledOperator_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ (.inr j))
  change Γ.vertexDerivative lab (.inr j) (f j) = 0
  rw [hf]
  exact vertexDerivative_C_eq_zero Γ lab (.inr j) hin r

/-- The complete actual graph operator has the same targeted constant-input vanishing. -/
theorem cochainOperator_C_external (Γ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (j : Fin m) (r : R) (hin : (Γ.incoming (.inr j)).Nonempty) (hf : f j = C r) :
    Γ.cochainOperator T f = 0 := by
  rw [cochainOperator, MultilinearMap.currySum_apply, operator, sum_apply]
  apply Finset.sum_eq_zero
  intro lab hlab
  exact labelledOperator_C_external Γ lab T f j r hin hf

theorem cochainOperator_one_external (Γ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (j : Fin m) (hin : (Γ.incoming (.inr j)).Nonempty) (hf : f j = 1) :
    Γ.cochainOperator T f = 0 :=
  cochainOperator_C_external Γ T f j 1 hin (by simpa using hf)

theorem cochainOperator_update_C (Γ : Graph q m)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (j : Fin m) (r : R) (hin : (Γ.incoming (.inr j)).Nonempty) :
    Γ.cochainOperator T (Function.update f j (C r)) = 0 :=
  cochainOperator_C_external Γ T _ j r hin (Function.update_self ..)

end Graph

/-- An actual finite scalar-weighted sum, with multilinearity inherited from the graph maps. -/
def weightedCochainOperator (s : Finset (Graph q m)) (weight : Graph q m → R) :
    MultilinearMap R (fun v : Fin n ↦ Tensor (q v) d R)
      (Cochain R (Polynomial d R) m) :=
  ∑ Γ ∈ s, weight Γ • Γ.cochainOperator

@[simp] theorem weightedCochainOperator_apply (s : Finset (Graph q m)) (weight : Graph q m → R)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    weightedCochainOperator s weight T f = ∑ Γ ∈ s, weight Γ • Γ.cochainOperator T f := by
  simp [weightedCochainOperator]

/-- For the weighted sum, untargeted graphs must be removed by their actual weights.
No vanishing assertion is made for an individual graph that misses the constant slot. -/
theorem weightedCochainOperator_C_external (s : Finset (Graph q m)) (weight : Graph q m → R)
    (j : Fin m) (hweight : ∀ Γ ∈ s, Γ.incoming (.inr j) = ∅ → weight Γ = 0)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (r : R) (hf : f j = C r) : weightedCochainOperator s weight T f = 0 := by
  classical
  rw [weightedCochainOperator_apply]
  apply Finset.sum_eq_zero
  intro Γ hΓ
  by_cases hin : (Γ.incoming (.inr j)).Nonempty
  · rw [Graph.cochainOperator_C_external Γ T f j r hin hf, smul_zero]
  · rw [hweight Γ hΓ (Finset.not_nonempty_iff_eq_empty.mp hin), zero_smul]

theorem weightedCochainOperator_one_external (s : Finset (Graph q m)) (weight : Graph q m → R)
    (j : Fin m) (hweight : ∀ Γ ∈ s, Γ.incoming (.inr j) = ∅ → weight Γ = 0)
    (T : (v : Fin n) → Tensor (q v) d R) (f : Fin m → Polynomial d R)
    (hf : f j = 1) : weightedCochainOperator s weight T f = 0 :=
  weightedCochainOperator_C_external s weight j hweight T f 1 (by simpa using hf)

theorem ofBinary_incoming_nonempty (Γ : KontsevichGraph n) (v : KontsevichGraph.Vertex n)
    (h : (Γ.incoming v).Nonempty) : ((ofBinary Γ).incoming v).Nonempty := by
  obtain ⟨e, he⟩ := h
  refine ⟨⟨e.1, e.2⟩, ?_⟩
  simpa only [Graph.incoming, KontsevichGraph.incoming, Finset.mem_filter, Finset.mem_univ,
    true_and, ofBinary] using he

/-- The legacy linear-bivector formula inherits the same actual targeted-slot vanishing. -/
theorem legacy_operator_C_external (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d R) (f : Fin 2 → Polynomial d R)
    (j : Fin 2) (r : R) (hin : (Γ.incoming (.inr j)).Nonempty) (hf : f j = C r) :
    Γ.operator c (f 0) (f 1) = 0 := by
  rw [← cochainOperator_ofBinary_apply Γ c f]
  exact Graph.cochainOperator_C_external (ofBinary Γ) (linearBivectorTensors c) f j r
    (ofBinary_incoming_nonempty Γ (.inr j) hin) hf

theorem legacy_weightedOperator_C_external (s : Finset (KontsevichGraph n))
    (weight : KontsevichGraph n → R) (j : Fin 2)
    (hweight : ∀ Γ ∈ s, Γ.incoming (.inr j) = ∅ → weight Γ = 0)
    (c : KontsevichGraph.Coefficients n d R) (f : Fin 2 → Polynomial d R)
    (r : R) (hf : f j = C r) : KontsevichGraph.weightedOperator s weight c (f 0) (f 1) = 0 := by
  classical
  rw [KontsevichGraph.weightedOperator_apply]
  apply Finset.sum_eq_zero
  intro Γ hΓ
  by_cases hin : (Γ.incoming (.inr j)).Nonempty
  · rw [legacy_operator_C_external Γ c f j r hin hf, smul_zero]
  · rw [hweight Γ hΓ (Finset.not_nonempty_iff_eq_empty.mp hin), zero_smul]

/-- Higher graph corrections vanish on a unit slot if the weights of graphs missing
that slot vanish. The order-zero ordinary product is retained. -/
theorem finiteStarOperator_unit_slot (N : ℕ)
    (s : (l : ℕ) → Finset (KontsevichGraph (l + 1)))
    (weight : (l : ℕ) → KontsevichGraph (l + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (f : Fin 2 → Polynomial d R) (j : Fin 2)
    (hf : f j = 1)
    (hweight : ∀ l ∈ Finset.range N, ∀ Γ ∈ s l, Γ.incoming (.inr j) = ∅ → weight l Γ = 0) :
    KontsevichGraph.finiteStarOperator N s weight c (f 0) (f 1) = f 0 * f 1 := by
  have h := KontsevichGraph.finiteStarOperator_sub_mul N s weight c (f 0) (f 1)
  have hz : (∑ l ∈ Finset.range N,
      KontsevichGraph.weightedOperator (s l) (weight l) (fun _ ↦ c) (f 0) (f 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    exact legacy_weightedOperator_C_external (s l) (weight l) j (hweight l hl) (fun _ ↦ c)
      f 1 (by simpa using hf)
  rw [hz, sub_eq_zero] at h
  exact h

theorem finiteStarOperator_one_left (N : ℕ)
    (s : (l : ℕ) → Finset (KontsevichGraph (l + 1)))
    (weight : (l : ℕ) → KontsevichGraph (l + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (f : Polynomial d R)
    (hweight : ∀ l ∈ Finset.range N, ∀ Γ ∈ s l, Γ.incoming (.inr 0) = ∅ → weight l Γ = 0) :
    KontsevichGraph.finiteStarOperator N s weight c 1 f = f := by
  simpa using finiteStarOperator_unit_slot N s weight c ![1, f] 0 rfl hweight

theorem finiteStarOperator_one_right (N : ℕ)
    (s : (l : ℕ) → Finset (KontsevichGraph (l + 1)))
    (weight : (l : ℕ) → KontsevichGraph (l + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (f : Polynomial d R)
    (hweight : ∀ l ∈ Finset.range N, ∀ Γ ∈ s l, Γ.incoming (.inr 1) = ∅ → weight l Γ = 0) :
    KontsevichGraph.finiteStarOperator N s weight c f 1 = f := by
  simpa using finiteStarOperator_unit_slot N s weight c ![f, 1] 1 rfl hweight

end KontsevichGraph.General

end EnvelopingIsomorphism.Deformation
