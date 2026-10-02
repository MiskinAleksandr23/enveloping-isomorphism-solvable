import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin
import EnvelopingIsomorphism.Deformation.Cochains

/-!
# Polynomial degree of linear-Poisson graph operators

The graph formula is evaluated using actual iterated partial derivatives. Its
degree estimate is independent of graph weights, Jacobi, and formality.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators
open MvPolynomial

variable {k : Type*} [CommRing k] {σ : Type*}

/-- A nonzero partial derivative lowers total degree by at least one. -/
theorem totalDegree_pderiv_add_one_le (i : σ) (p : MvPolynomial σ k)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (MvPolynomial.support_nonempty.mpr h) (fun m => m.sum fun _ e => e)
  have hc : coeff (m + Finsupp.single i 1) p ≠ 0 := by
    apply left_ne_zero_of_mul
    simpa only [coeff_pderiv] using MvPolynomial.mem_support_iff.mp hm
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  change (pderiv i p).totalDegree = m.sum (fun _ e => e) at heq
  rw [heq]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)] at hd
  exact hd

/-- Iterated formal partial derivatives, with the listed order fixed explicitly. -/
def iteratedPDeriv : List σ → Module.End k (MvPolynomial σ k)
  | [] => LinearMap.id
  | i :: is => (pderiv i).toLinearMap.comp (iteratedPDeriv is)

@[simp] theorem iteratedPDeriv_nil (p : MvPolynomial σ k) : iteratedPDeriv [] p = p := rfl

@[simp] theorem iteratedPDeriv_cons (i : σ) (is : List σ) (p : MvPolynomial σ k) :
    iteratedPDeriv (i :: is) p = pderiv i (iteratedPDeriv is p) := rfl

/-- The number of derivatives is charged even when the input is constant. -/
theorem totalDegree_iteratedPDeriv_add_length_le (is : List σ) (p : MvPolynomial σ k)
    (h : iteratedPDeriv is p ≠ 0) :
    (iteratedPDeriv is p).totalDegree + is.length ≤ p.totalDegree := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hn : iteratedPDeriv is p ≠ 0 := by
      intro hz
      simp only [iteratedPDeriv_cons, hz, map_zero, ne_eq, not_true_eq_false] at h
    have h₁ := totalDegree_pderiv_add_one_le i (iteratedPDeriv is p) h
    have h₂ := ih hn
    simp only [List.length_cons, iteratedPDeriv_cons]
    omega

/-- A finite sum retains a common degree budget; nonzero output is essential. -/
theorem totalDegree_finsetSum_add_le {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ k) (D r : ℕ)
    (hp : ∀ i ∈ s, p i ≠ 0 → (p i).totalDegree + r ≤ D)
    (hs : ∑ i ∈ s, p i ≠ 0) : (∑ i ∈ s, p i).totalDegree + r ≤ D := by
  by_cases hr : r ≤ D
  · have hb : ∀ i ∈ s, (p i).totalDegree ≤ D - r := by
      intro i hi
      by_cases hz : p i = 0
      · simp [hz]
      · have h := hp i hi hz
        omega
    have hd := (MvPolynomial.totalDegree_finsetSum s p).trans (Finset.sup_le hb)
    change (∑ i ∈ s, p i).totalDegree ≤ D - r at hd
    omega
  · have hz : ∀ i ∈ s, p i = 0 := by
      intro i hi
      by_contra hn
      have h := hp i hi hn
      omega
    exact False.elim (hs (Finset.sum_eq_zero hz))

/-- A finite graph with two ordered outgoing edges at each internal vertex. -/
structure KontsevichGraph (n : ℕ) where
  target : (Fin n × Fin 2) → (Fin n ⊕ Fin 2)
  noLoops : ∀ v a, target (v, a) ≠ Sum.inl v
  distinctTargets : ∀ v, target (v, 0) ≠ target (v, 1)

namespace KontsevichGraph

abbrev Edge (n : ℕ) := Fin n × Fin 2
abbrev Vertex (n : ℕ) := Fin n ⊕ Fin 2
abbrev Polynomial (d : ℕ) (k : Type*) [CommRing k] := MvPolynomial (Fin d) k

variable {n d : ℕ}

@[ext] theorem ext {Γ Δ : KontsevichGraph n} (h : Γ.target = Δ.target) : Γ = Δ := by
  cases Γ
  cases Δ
  cases h
  rfl

instance : Fintype (KontsevichGraph n) :=
  Fintype.ofInjective KontsevichGraph.target (fun _ _ h => ext h)

/-- Edges differentiating the coefficient or input attached to a vertex. -/
def incoming (Γ : KontsevichGraph n) (v : Vertex n) : Finset (Edge n) :=
  Finset.univ.filter (fun e => Γ.target e = v)

/-- Each of the `2n` edges contributes exactly one derivative. -/
theorem sum_card_incoming (Γ : KontsevichGraph n) :
    ∑ v, (Γ.incoming v).card = 2 * n := by
  classical
  simpa [incoming, Fintype.card_prod, Nat.mul_comm] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Edge n)) (Finset.univ : Finset (Vertex n)) Γ.target

/-- A homogeneous linear polynomial, specified by its coefficients. -/
def linearCoefficient (c : Fin d → k) : Polynomial d k :=
  ∑ r, C (c r) * X r

theorem totalDegree_linearCoefficient_le [Nontrivial k] (c : Fin d → k) :
    (linearCoefficient c).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro r hr
  simpa using MvPolynomial.totalDegree_mul (C (c r) : Polynomial d k) (X r)

/-- The coordinate differential operator at one vertex for an edge labelling. -/
def vertexDerivative (Γ : KontsevichGraph n) (lab : Edge n → Fin d) (v : Vertex n) :
    Module.End k (Polynomial d k) :=
  iteratedPDeriv ((Γ.incoming v).toList.map lab)

theorem totalDegree_vertexDerivative_add_card_le (Γ : KontsevichGraph n)
    (lab : Edge n → Fin d) (v : Vertex n) (p : Polynomial d k)
    (h : Γ.vertexDerivative lab v p ≠ 0) :
    (Γ.vertexDerivative lab v p).totalDegree + (Γ.incoming v).card ≤ p.totalDegree := by
  simpa only [vertexDerivative, List.length_map, Finset.length_toList] using
    totalDegree_iteratedPDeriv_add_length_le ((Γ.incoming v).toList.map lab) p h

/-- Linear bivector coefficients, allowing a different bivector at each vertex.
No skew-symmetry or Jacobi assumption is needed for the degree theorem. -/
abbrev Coefficients (n d : ℕ) (k : Type*) := Fin n → Fin d → Fin d → Fin d → k

/-- The polynomial differentiated at a vertex in a labelled graph term. -/
def vertexInput (α : Coefficients n d k) (lab : Edge n → Fin d)
    (f g : Polynomial d k) : Vertex n → Polynomial d k
  | Sum.inl v => linearCoefficient (α v (lab (v, 0)) (lab (v, 1)))
  | Sum.inr j => if j = 0 then f else g

/-- One edge-labelling summand of the actual graph formula, as a bilinear map. -/
def labelledOperator (Γ : KontsevichGraph n) (α : Coefficients n d k)
    (lab : Edge n → Fin d) : Binary k (Polynomial d k) :=
  ((LinearMap.mul k (Polynomial d k)).compl₁₂
    (Γ.vertexDerivative lab (Sum.inr 0))
    (Γ.vertexDerivative lab (Sum.inr 1))).compr₂
      (LinearMap.mulLeft k (∏ v : Fin n, Γ.vertexDerivative lab (Sum.inl v)
        (linearCoefficient (α v (lab (v, 0)) (lab (v, 1))))))

theorem labelledOperator_apply (Γ : KontsevichGraph n) (α : Coefficients n d k)
    (lab : Edge n → Fin d) (f g : Polynomial d k) :
    Γ.labelledOperator α lab f g =
      ∏ v : Vertex n, Γ.vertexDerivative lab v (vertexInput α lab f g v) := by
  simp [labelledOperator, Fintype.prod_sum_type, Fin.prod_univ_two, vertexInput]

/-- Sum over every assignment of coordinate indices to the graph's edges. -/
def operator (Γ : KontsevichGraph n) (α : Coefficients n d k) :
    Binary k (Polynomial d k) :=
  ∑ lab : Edge n → Fin d, Γ.labelledOperator α lab

/-- The same graph operator in the project's full Hochschild cochain space. -/
def cochain (Γ : KontsevichGraph n) (α : Coefficients n d k) :
    Cochain k (Polynomial d k) 2 :=
  (cochainTwoEquiv k (Polynomial d k)).symm (Γ.operator α)

@[simp] theorem cochain_apply (Γ : KontsevichGraph n) (α : Coefficients n d k)
    (x : Fin 2 → Polynomial d k) : Γ.cochain α x = Γ.operator α (x 0) (x 1) := rfl

theorem operator_apply (Γ : KontsevichGraph n) (α : Coefficients n d k)
    (f g : Polynomial d k) :
    Γ.operator α f g = ∑ lab : Edge n → Fin d, Γ.labelledOperator α lab f g := by
  simp [operator, LinearMap.sum_apply]

/-- A nonzero labelled graph term loses at least one degree per internal vertex. -/
theorem totalDegree_labelledOperator_add_le [Nontrivial k]
    (Γ : KontsevichGraph n) (α : Coefficients n d k) (lab : Edge n → Fin d)
    (f g : Polynomial d k) (h : Γ.labelledOperator α lab f g ≠ 0) :
    (Γ.labelledOperator α lab f g).totalDegree + n ≤ f.totalDegree + g.totalDegree := by
  classical
  let p : Vertex n → Polynomial d k :=
    fun v => Γ.vertexDerivative lab v (vertexInput α lab f g v)
  let b : Vertex n → ℕ := Sum.elim (fun _ => 1)
    (fun j => if j = 0 then f.totalDegree else g.totalDegree)
  have hprod : ∏ v, p v ≠ 0 := by simpa only [labelledOperator_apply] using h
  have hne (v : Vertex n) : p v ≠ 0 := by
    intro hz
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) hz)
  have hb (v : Vertex n) : (p v).totalDegree + (Γ.incoming v).card ≤ b v := by
    apply (Γ.totalDegree_vertexDerivative_add_card_le lab v _ (hne v)).trans
    cases v with
    | inl v => exact totalDegree_linearCoefficient_le _
    | inr j => simp only [vertexInput, b, Sum.elim_inr]; split <;> exact le_rfl
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hb v)
  have hbsum : ∑ v, b v = n + (f.totalDegree + g.totalDegree) := by
    simp [b, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [Finset.sum_add_distrib, Γ.sum_card_incoming, hbsum] at hsum
  have hd := MvPolynomial.totalDegree_finsetProd Finset.univ p
  change (∏ v, p v).totalDegree ≤ ∑ v, (p v).totalDegree at hd
  rw [labelledOperator_apply]
  change (∏ v, p v).totalDegree + n ≤ _
  omega

/-- The full coordinate sum has the same degree estimate. -/
theorem totalDegree_operator_add_le [Nontrivial k]
    (Γ : KontsevichGraph n) (α : Coefficients n d k) (f g : Polynomial d k)
    (h : Γ.operator α f g ≠ 0) :
    (Γ.operator α f g).totalDegree + n ≤ f.totalDegree + g.totalDegree := by
  rw [operator_apply] at h ⊢
  exact totalDegree_finsetSum_add_le Finset.univ _ _ _
    (fun lab _ hn => Γ.totalDegree_labelledOperator_add_le α lab f g hn) h

/-- More internal vertices than the total input degree gives the zero operator value. -/
theorem operator_eq_zero_of_degree_lt [Nontrivial k]
    (Γ : KontsevichGraph n) (α : Coefficients n d k) (f g : Polynomial d k)
    (h : f.totalDegree + g.totalDegree < n) : Γ.operator α f g = 0 := by
  by_contra hn
  have hd := Γ.totalDegree_operator_add_le α f g hn
  omega

/-- An unconditional total-degree bound, including zero output. -/
theorem totalDegree_operator_le [Nontrivial k]
    (Γ : KontsevichGraph n) (α : Coefficients n d k) (f g : Polynomial d k) :
    (Γ.operator α f g).totalDegree ≤ f.totalDegree + g.totalDegree - n := by
  by_cases h : Γ.operator α f g = 0
  · simp [h]
  · have hd := Γ.totalDegree_operator_add_le α f g h
    omega

/-- Positive graph orders contribute strictly below the ordinary product degree. -/
theorem totalDegree_operator_lt [Nontrivial k]
    (Γ : KontsevichGraph n) (α : Coefficients n d k) (f g : Polynomial d k)
    (hn : 0 < n) (h : Γ.operator α f g ≠ 0) :
    (Γ.operator α f g).totalDegree < f.totalDegree + g.totalDegree := by
  have hd := Γ.totalDegree_operator_add_le α f g h
  omega

/-- The graph with no internal vertices evaluates to ordinary multiplication. -/
theorem operator_zero (Γ : KontsevichGraph 0) (α : Coefficients 0 d k) :
    Γ.operator α = LinearMap.mul k (Polynomial d k) := by
  ext f g
  simp [operator_apply, labelledOperator, vertexDerivative, incoming, iteratedPDeriv]

/-- Any finite weighted sum of graphs of the same order. The weights are arbitrary. -/
def weightedOperator (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k)
    (α : Coefficients n d k) : Binary k (Polynomial d k) :=
  ∑ Γ ∈ s, w Γ • Γ.operator α

theorem weightedOperator_apply (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k)
    (α : Coefficients n d k) (f g : Polynomial d k) :
    weightedOperator s w α f g = ∑ Γ ∈ s, w Γ • Γ.operator α f g := by
  simp [weightedOperator, LinearMap.sum_apply]

/-- Degree lowering survives arbitrary scalar graph weights and finite sums. -/
theorem totalDegree_weightedOperator_add_le [Nontrivial k]
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k)
    (α : Coefficients n d k) (f g : Polynomial d k)
    (h : weightedOperator s w α f g ≠ 0) :
    (weightedOperator s w α f g).totalDegree + n ≤ f.totalDegree + g.totalDegree := by
  rw [weightedOperator_apply] at h ⊢
  apply totalDegree_finsetSum_add_le s _ _ _ _ h
  intro Γ hΓ hn
  have hp : Γ.operator α f g ≠ 0 := by
    intro hz
    exact hn (by rw [hz, smul_zero])
  have hd := Γ.totalDegree_operator_add_le α f g hp
  have hs := MvPolynomial.totalDegree_smul_le (w Γ) (Γ.operator α f g)
  omega

/-- The finite weighted graph expansion terminates at total input degree. -/
theorem weightedOperator_eq_zero_of_degree_lt [Nontrivial k]
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k)
    (α : Coefficients n d k) (f g : Polynomial d k)
    (h : f.totalDegree + g.totalDegree < n) : weightedOperator s w α f g = 0 := by
  by_contra hn
  have hd := totalDegree_weightedOperator_add_le s w α f g hn
  omega

/-- Normalizing the weight at order zero gives ordinary multiplication. -/
theorem weightedOperator_zero (s : Finset (KontsevichGraph 0)) (w : KontsevichGraph 0 → k)
    (α : Coefficients 0 d k) (hw : ∑ Γ ∈ s, w Γ = 1) :
    weightedOperator s w α = LinearMap.mul k (Polynomial d k) := by
  simp only [weightedOperator, operator_zero, ← Finset.sum_smul, hw, one_smul]

/-- A finite graph expansion with its order-zero multiplication normalized.
The coefficient ring may itself contain a central formal parameter; its powers
can be included in `w`. This definition makes no associativity assertion. -/
def finiteStarOperator (N : ℕ) (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) : Binary k (Polynomial d k) :=
  LinearMap.mul k (Polynomial d k) +
    ∑ j ∈ Finset.range N, weightedOperator (s j) (w j) (fun _ => c)

theorem finiteStarOperator_sub_mul (N : ℕ)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    finiteStarOperator N s w c f g - f * g =
      ∑ j ∈ Finset.range N, weightedOperator (s j) (w j) (fun _ => c) f g := by
  simp [finiteStarOperator, LinearMap.sum_apply]

/-- The entire correction to ordinary multiplication has strictly smaller degree. -/
theorem totalDegree_finiteStarOperator_sub_mul_add_one_le [Nontrivial k] (N : ℕ)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k)
    (h : finiteStarOperator N s w c f g - f * g ≠ 0) :
    (finiteStarOperator N s w c f g - f * g).totalDegree + 1 ≤
      f.totalDegree + g.totalDegree := by
  rw [finiteStarOperator_sub_mul] at h ⊢
  apply totalDegree_finsetSum_add_le (Finset.range N) _ _ _ _ h
  intro j hj hn
  have hd := totalDegree_weightedOperator_add_le (s j) (w j) (fun _ => c) f g hn
  omega

/-- Consequently, the finite graph expansion preserves the ordinary degree filtration. -/
theorem totalDegree_finiteStarOperator_le [Nontrivial k] (N : ℕ)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    (finiteStarOperator N s w c f g).totalDegree ≤ f.totalDegree + g.totalDegree := by
  let q := finiteStarOperator N s w c f g - f * g
  have hq : q.totalDegree ≤ f.totalDegree + g.totalDegree := by
    by_cases h : q = 0
    · simp [h]
    · have hd := totalDegree_finiteStarOperator_sub_mul_add_one_le N s w c f g h
      change q.totalDegree + 1 ≤ _ at hd
      omega
  have heq : finiteStarOperator N s w c f g = f * g + q := by dsimp [q]; abel
  rw [heq]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (MvPolynomial.totalDegree_mul f g) hq)

end KontsevichGraph

end EnvelopingIsomorphism.Deformation
