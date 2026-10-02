import EnvelopingIsomorphism.Deformation.GraphDegree
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Pi

/-! Genuine polynomial Kontsevich graph operators with arbitrary ordered outgoing arities. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

open MvPolynomial
open scoped BigOperators

abbrev Polynomial (d : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin d) R

/-- Polynomial coordinate tensors, before restricting to alternating tensors. -/
abbrev Tensor (q d : ℕ) (R : Type*) [CommRing R] :=
  (Fin q → Fin d) → Polynomial d R

abbrev Edge {n : ℕ} (q : Fin n → ℕ) := (v : Fin n) × Fin (q v)
abbrev Vertex (n m : ℕ) := Fin n ⊕ Fin m

/-- An admissible graph with individually specified ordered outgoing edges. -/
structure Graph {n : ℕ} (q : Fin n → ℕ) (m : ℕ) where
  target : Edge q → Vertex n m
  noLoops : ∀ v a, target ⟨v, a⟩ ≠ Sum.inl v
  distinctTargets : ∀ v, Function.Injective (fun a ↦ target ⟨v, a⟩)

/-- Heterogeneous input family: one coordinate tensor at each interior vertex,
and one actual polynomial at each exterior vertex. -/
abbrev Input {n : ℕ} (q : Fin n → ℕ) (m d : ℕ) (R : Type*) [CommRing R] :
    Vertex n m → Type _
  | .inl v => Tensor (q v) d R
  | .inr _ => Polynomial d R

@[reducible] instance inputAddCommMonoid {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin n → ℕ}
    : (v : Vertex n m) → AddCommMonoid (Input q m d R v)
  | .inl v => inferInstanceAs (AddCommMonoid (Tensor (q v) d R))
  | .inr _ => inferInstanceAs (AddCommMonoid (Polynomial d R))

@[reducible] instance inputModule {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin n → ℕ}
    : (v : Vertex n m) → Module R (Input q m d R v)
  | .inl v => inferInstanceAs (Module R (Tensor (q v) d R))
  | .inr _ => inferInstanceAs (Module R (Polynomial d R))

namespace Graph

variable {R : Type*} [CommRing R] {n m d : ℕ} {q : Fin n → ℕ}

@[ext] theorem ext {Γ Δ : Graph q m} (h : Γ.target = Δ.target) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h
  rfl

instance : Fintype (Graph q m) :=
  Fintype.ofInjective Graph.target (fun _ _ h ↦ ext h)

/-- Incoming edges determine the actual iterated coordinate derivatives. -/
def incoming (Γ : Graph q m) (v : Vertex n m) : Finset (Edge q) :=
  Finset.univ.filter (fun e ↦ Γ.target e = v)

theorem sum_card_incoming (Γ : Graph q m) :
    ∑ v, (Γ.incoming v).card = ∑ v : Fin n, q v := by
  classical
  simpa [incoming, Fintype.card_sigma] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Edge q)) (Finset.univ : Finset (Vertex n m)) Γ.target

def vertexDerivative (Γ : Graph q m) (lab : Edge q → Fin d) (v : Vertex n m) :
    Module.End R (Polynomial d R) :=
  EnvelopingIsomorphism.Deformation.iteratedPDeriv ((Γ.incoming v).toList.map lab)

/-- Select the ordered tensor coefficient at an internal vertex, or the exterior input. -/
def vertexEvaluation (lab : Edge q → Fin d) :
    (v : Vertex n m) → Input q m d R v →ₗ[R] Polynomial d R
  | .inl v => LinearMap.proj (fun a ↦ lab ⟨v, a⟩)
  | .inr _ => LinearMap.id

@[simp] theorem vertexEvaluation_inl (lab : Edge q → Fin d) (v : Fin n)
    (T : Tensor (q v) d R) :
    vertexEvaluation (m := m) lab (.inl v) T = T (fun a ↦ lab ⟨v, a⟩) := rfl

@[simp] theorem vertexEvaluation_inr (lab : Edge q → Fin d) (j : Fin m)
    (f : Polynomial d R) : vertexEvaluation lab (.inr j) f = f := rfl

/-- One edge-labelling term, proved multilinear simultaneously in every tensor and exterior input. -/
def labelledOperator (Γ : Graph q m) (lab : Edge q → Fin d) :
    MultilinearMap R (Input q m d R) (Polynomial d R) :=
  (MultilinearMap.mkPiAlgebra R (Vertex n m) (Polynomial d R)).compLinearMap
    (fun v ↦ (Γ.vertexDerivative lab v).comp (vertexEvaluation lab v))

@[simp] theorem labelledOperator_apply (Γ : Graph q m) (lab : Edge q → Fin d)
    (x : (v : Vertex n m) → Input q m d R v) :
    Γ.labelledOperator lab x =
      ∏ v, Γ.vertexDerivative lab v (vertexEvaluation lab v (x v)) := by
  simp [labelledOperator]

/-- The actual finite sum over all coordinate labels on all edges. No graph weight is included. -/
def operator (Γ : Graph q m) : MultilinearMap R (Input q m d R) (Polynomial d R) :=
  ∑ lab : Edge q → Fin d, Γ.labelledOperator lab

@[simp] theorem operator_apply (Γ : Graph q m)
    (x : (v : Vertex n m) → Input q m d R v) :
    Γ.operator x = ∑ lab : Edge q → Fin d,
      ∏ v, Γ.vertexDerivative lab v (vertexEvaluation lab v (x v)) := by
  simp [operator]

/-- The same operation as a multilinear map from interior tensors to the existing full
Hochschild cochain space of exterior arity `m`, including `m=0`. -/
def cochainOperator (Γ : Graph q m) :
    MultilinearMap R (fun v : Fin n ↦ Tensor (q v) d R)
      (EnvelopingIsomorphism.Deformation.Cochain R (Polynomial d R) m) :=
  (Γ.operator (R := R) (d := d)).currySum

theorem cochainOperator_apply (Γ : Graph q m) (T : (v : Fin n) → Tensor (q v) d R)
    (f : Fin m → Polynomial d R) :
    Γ.cochainOperator T f = ∑ lab : Edge q → Fin d,
      (∏ v : Fin n, Γ.vertexDerivative lab (.inl v) (T v (fun a ↦ lab ⟨v, a⟩))) *
        ∏ j : Fin m, Γ.vertexDerivative lab (.inr j) (f j) := by
  rw [cochainOperator, MultilinearMap.currySum_apply, operator_apply]
  simp only [Fintype.prod_sum_type]
  rfl

/-- Arity zero retains the actual polynomial value of the labelled graph contraction. -/
theorem cochainOperator_arity_zero (Γ : Graph q 0) (T : (v : Fin n) → Tensor (q v) d R)
    (f : Fin 0 → Polynomial d R) :
    Γ.cochainOperator T f = ∑ lab : Edge q → Fin d,
      ∏ v : Fin n, Γ.vertexDerivative lab (.inl v) (T v (fun a ↦ lab ⟨v, a⟩)) := by
  simp [cochainOperator_apply]

/-- With no internal vertices there are no edges, and the operator is ordinary multiplication
of all exterior inputs; for no inputs at all this is the unit polynomial. -/
theorem cochainOperator_no_internal {q : Fin 0 → ℕ} (Γ : Graph q m)
    (T : (v : Fin 0) → Tensor (q v) d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator T f = ∏ j, f j := by
  simp [cochainOperator_apply, vertexDerivative, incoming, EnvelopingIsomorphism.Deformation.iteratedPDeriv]

/-- Zero-ary internal tensors are retained as polynomial functions, even when all outgoing
arities vanish. There is then no differentiation or coordinate-label multiplicity. -/
theorem cochainOperator_zero_outgoing (Γ : Graph (fun _ : Fin n ↦ 0) m)
    (T : (v : Fin n) → Tensor 0 d R) (f : Fin m → Polynomial d R) :
    Γ.cochainOperator T f = (∏ v, T v Fin.elim0) * ∏ j, f j := by
  classical
  haveI : IsEmpty (Edge (fun _ : Fin n ↦ 0)) := ⟨fun e ↦ Fin.elim0 e.2⟩
  have heval (lab : Edge (fun _ : Fin n ↦ 0) → Fin d) (v : Fin n) :
      T v (fun a ↦ lab ⟨v, a⟩) = T v Fin.elim0 :=
    congrArg (T v) (Subsingleton.elim _ _)
  simp [cochainOperator_apply, vertexDerivative, incoming, EnvelopingIsomorphism.Deformation.iteratedPDeriv,
    heval]

end Graph

section BinaryCompatibility

variable {R : Type*} [CommRing R] {n d : ℕ}

theorem pderiv_commute (i j : Fin d) (p : Polynomial d R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  ext a
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
    if_false, add_zero]
  rw [show a + Finsupp.single i 1 + Finsupp.single j 1 =
    a + Finsupp.single j 1 + Finsupp.single i 1 by abel]
  ring

/-- Incoming-edge order does not affect the actual iterated polynomial derivative. -/
theorem iteratedPDeriv_perm {s t : List (Fin d)} (h : s.Perm t) :
    EnvelopingIsomorphism.Deformation.iteratedPDeriv (k := R) s =
      EnvelopingIsomorphism.Deformation.iteratedPDeriv t := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [EnvelopingIsomorphism.Deformation.iteratedPDeriv, ih]
  | swap i j s =>
    apply LinearMap.ext
    intro p
    exact pderiv_commute j i (EnvelopingIsomorphism.Deformation.iteratedPDeriv s p)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def bivectorEdgeEquiv : Edge (fun _ : Fin n ↦ 2) ≃ KontsevichGraph.Edge n where
  toFun e := (e.1, e.2)
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The existing two-output bivector graphs are genuine special cases of the general graphs. -/
def ofBinary (Γ : KontsevichGraph n) : Graph (fun _ : Fin n ↦ 2) 2 where
  target e := Γ.target (e.1, e.2)
  noLoops := Γ.noLoops
  distinctTargets v := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact (Γ.distinctTargets v h).elim
    · exact (Γ.distinctTargets v h.symm).elim
    · rfl

def bivectorLabelEquiv : (Edge (fun _ : Fin n ↦ 2) → Fin d) ≃ (KontsevichGraph.Edge n → Fin d) where
  toFun lab e := lab ⟨e.1, e.2⟩
  invFun lab e := lab (e.1, e.2)
  left_inv lab := by funext e; cases e; rfl
  right_inv lab := by funext e; cases e; rfl

theorem incoming_binary_perm (Γ : KontsevichGraph n) (v : KontsevichGraph.Vertex n) :
    (((ofBinary Γ).incoming v).toList.map bivectorEdgeEquiv).Perm (Γ.incoming v).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map bivectorEdgeEquiv.injective) (Finset.nodup_toList _)).mpr
  intro e
  simp only [List.mem_map, Finset.mem_toList, Graph.incoming, KontsevichGraph.incoming,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, heq⟩
    change Γ.target (a.1, a.2) = v at ha
    change (a.1, a.2) = e at heq
    exact heq ▸ ha
  · intro he
    exact ⟨⟨e.1, e.2⟩, he, rfl⟩

theorem vertexDerivative_ofBinary (Γ : KontsevichGraph n)
    (lab : Edge (fun _ : Fin n ↦ 2) → Fin d) (v : KontsevichGraph.Vertex n) :
    (ofBinary Γ).vertexDerivative (R := R) lab v =
      Γ.vertexDerivative (bivectorLabelEquiv lab) v := by
  apply iteratedPDeriv_perm
  have h := (incoming_binary_perm Γ v).map (bivectorLabelEquiv lab)
  rw [List.map_map] at h
  have hcomp : (bivectorLabelEquiv lab) ∘ bivectorEdgeEquiv = lab := by
    funext e
    cases e
    rfl
  rw [hcomp] at h
  exact h

/-- The previous linear-coefficient bivectors as actual polynomial coordinate tensors. -/
def linearBivectorTensors (c : KontsevichGraph.Coefficients n d R) :
    (v : Fin n) → Tensor 2 d R :=
  fun v a ↦ KontsevichGraph.linearCoefficient (c v (a 0) (a 1))

theorem labelledOperator_ofBinary_apply (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d R) (lab : Edge (fun _ : Fin n ↦ 2) → Fin d)
    (f : Fin 2 → Polynomial d R) :
    ((ofBinary Γ).labelledOperator lab).currySum (linearBivectorTensors c) f =
      Γ.labelledOperator c (bivectorLabelEquiv lab) (f 0) (f 1) := by
  rw [MultilinearMap.currySum_apply, Graph.labelledOperator_apply, KontsevichGraph.labelledOperator_apply]
  apply Finset.prod_congr rfl
  intro v hv
  rw [vertexDerivative_ofBinary]
  cases v with
  | inl v => rfl
  | inr j => fin_cases j <;> rfl

/-- Specializing to bivectors with linear coefficients and two exterior inputs recovers
the existing graph operator exactly, including its incoming derivative order. -/
theorem cochainOperator_ofBinary_apply (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d R) (f : Fin 2 → Polynomial d R) :
    (ofBinary Γ).cochainOperator (linearBivectorTensors c) f = Γ.operator c (f 0) (f 1) := by
  classical
  calc
    _ = ∑ lab : Edge (fun _ : Fin n ↦ 2) → Fin d,
        ((ofBinary Γ).labelledOperator lab).currySum (linearBivectorTensors c) f := by
      simp only [Graph.cochainOperator, Graph.operator, MultilinearMap.currySum_apply,
        sum_apply]
    _ = ∑ lab : KontsevichGraph.Edge n → Fin d, Γ.labelledOperator c lab (f 0) (f 1) := by
      apply Fintype.sum_equiv bivectorLabelEquiv
      intro lab
      exact labelledOperator_ofBinary_apply Γ c lab f
    _ = _ := (KontsevichGraph.operator_apply Γ c (f 0) (f 1)).symm

theorem cochainOperator_ofBinary (Γ : KontsevichGraph n)
    (c : KontsevichGraph.Coefficients n d R) :
    (ofBinary Γ).cochainOperator (linearBivectorTensors c) = Γ.cochain c := by
  apply MultilinearMap.ext
  intro f
  exact (cochainOperator_ofBinary_apply Γ c f).trans (KontsevichGraph.cochain_apply Γ c f).symm

end BinaryCompatibility

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
