import EnvelopingIsomorphism.Deformation.GraphLinearCommutator

/-!
# The two one-vertex graph operators

The actual coordinate graph formula is evaluated for the two admissible
one-vertex graphs. Rational weights are specified explicitly; no assertion
about configuration-space integrals is used here.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open KontsevichGraph MvPolynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The first outgoing edge goes to the first argument, the second to the second. -/
def forwardGraph : KontsevichGraph 1 where
  target e := Sum.inr e.2
  noLoops := by intro v a; simp
  distinctTargets := by intro v; simp

/-- Reversing the ordered outgoing edges reverses their external targets. -/
def reverseGraph : KontsevichGraph 1 where
  target e := Sum.inr (Equiv.swap 0 1 e.2)
  noLoops := by intro v a; simp
  distinctTargets := by intro v; simp

theorem forwardGraph_ne_reverseGraph : forwardGraph ≠ reverseGraph := by
  intro h
  have he := congrArg (fun Γ : KontsevichGraph 1 => Γ.target (0, 0)) h
  simp [forwardGraph, reverseGraph] at he

private theorem classify_one_vertex_targets :
    ∀ t : Edge 1 → Vertex 1,
      (∀ v a, t (v, a) ≠ Sum.inl v) →
      (∀ v, t (v, 0) ≠ t (v, 1)) →
      t = forwardGraph.target ∨ t = reverseGraph.target := by decide

/-- There are exactly two admissible graphs with one internal vertex and two external vertices. -/
theorem oneVertex_graph_cases (Γ : KontsevichGraph 1) :
    Γ = forwardGraph ∨ Γ = reverseGraph := by
  rcases classify_one_vertex_targets Γ.target Γ.noLoops Γ.distinctTargets with h | h
  · exact Or.inl (KontsevichGraph.ext h)
  · exact Or.inr (KontsevichGraph.ext h)

local instance : DecidableEq (KontsevichGraph 1) := Classical.decEq _

theorem oneVertex_graph_univ : (Finset.univ : Finset (KontsevichGraph 1)) =
    {forwardGraph, reverseGraph} := by
  classical
  ext Γ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact oneVertex_graph_cases Γ

@[simp] theorem forwardGraph_incoming_internal (v : Fin 1) :
    forwardGraph.incoming (Sum.inl v) = ∅ := by
  ext e
  simp [incoming, forwardGraph]

@[simp] theorem forwardGraph_incoming_external (j : Fin 2) :
    forwardGraph.incoming (Sum.inr j) = {(0, j)} := by
  ext e
  rcases e with ⟨v, a⟩
  rw [Fin.eq_zero v]
  simp [incoming, forwardGraph]

@[simp] theorem reverseGraph_incoming_internal (v : Fin 1) :
    reverseGraph.incoming (Sum.inl v) = ∅ := by
  ext e
  simp [incoming, reverseGraph]

@[simp] theorem reverseGraph_incoming_external (j : Fin 2) :
    reverseGraph.incoming (Sum.inr j) = {(0, Equiv.swap 0 1 j)} := by
  ext e
  rcases e with ⟨v, a⟩
  fin_cases v
  fin_cases a <;> fin_cases j <;> simp [incoming, reverseGraph]

variable {k : Type*} [CommRing k] {d : ℕ}

/-- Coordinate labellings of the two outgoing edges are exactly pairs of coordinate indices. -/
def oneVertexLabelEquiv : (Edge 1 → Fin d) ≃ Fin d × Fin d where
  toFun lab := (lab (0, 0), lab (0, 1))
  invFun p e := if e.2 = 0 then p.1 else p.2
  left_inv lab := by
    funext e
    rcases e with ⟨v, a⟩
    fin_cases v
    fin_cases a <;> simp
  right_inv p := by ext <;> simp

theorem forwardGraph_labelled_apply (c : Fin d → Fin d → Fin d → k)
    (lab : Edge 1 → Fin d) (f g : Polynomial d k) :
    forwardGraph.labelledOperator (fun _ => c) lab f g =
      linearCoefficient (c (lab (0, 0)) (lab (0, 1))) *
        (pderiv (lab (0, 0)) f * pderiv (lab (0, 1)) g) := by
  simp [labelledOperator, vertexDerivative]

theorem reverseGraph_labelled_apply (c : Fin d → Fin d → Fin d → k)
    (lab : Edge 1 → Fin d) (f g : Polynomial d k) :
    reverseGraph.labelledOperator (fun _ => c) lab f g =
      linearCoefficient (c (lab (0, 0)) (lab (0, 1))) *
        (pderiv (lab (0, 1)) f * pderiv (lab (0, 0)) g) := by
  simp [labelledOperator, vertexDerivative]

/-- The forward coordinate graph sum, with every edge labelling included exactly once. -/
theorem forwardGraph_operator_apply (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    forwardGraph.operator (fun _ => c) f g =
      ∑ i : Fin d, ∑ j : Fin d, linearCoefficient (c i j) * (pderiv i f * pderiv j g) := by
  rw [operator_apply]
  simp only [forwardGraph_labelled_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin d × Fin d =>
    linearCoefficient (c p.1 p.2) * (pderiv p.1 f * pderiv p.2 g))]
  apply Fintype.sum_equiv oneVertexLabelEquiv
  intro lab
  rfl

theorem reverseGraph_operator_apply (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    reverseGraph.operator (fun _ => c) f g =
      ∑ i : Fin d, ∑ j : Fin d, linearCoefficient (c i j) * (pderiv j f * pderiv i g) := by
  rw [operator_apply]
  simp only [reverseGraph_labelled_apply]
  rw [← Fintype.sum_prod_type (fun p : Fin d × Fin d =>
    linearCoefficient (c p.1 p.2) * (pderiv p.2 f * pderiv p.1 g))]
  apply Fintype.sum_equiv oneVertexLabelEquiv
  intro lab
  rfl

/-- The pre-existing coordinate linear Poisson formula, bundled as a bilinear map. -/
def linearPoissonBinary (c : Fin d → Fin d → Fin d → k) : Binary k (Polynomial d k) :=
  LinearMap.mk₂ k (EnvelopingIsomorphism.Poisson.linearBracket c)
    (by intros; simp [EnvelopingIsomorphism.Poisson.linearBracket, add_mul, mul_add, Finset.sum_add_distrib])
    (by intros; simp [EnvelopingIsomorphism.Poisson.linearBracket, Finset.smul_sum])
    (by intros; simp [EnvelopingIsomorphism.Poisson.linearBracket, mul_add, Finset.sum_add_distrib])
    (by intros; simp [EnvelopingIsomorphism.Poisson.linearBracket, Finset.smul_sum])

@[simp] theorem linearPoissonBinary_apply (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    linearPoissonBinary c f g = EnvelopingIsomorphism.Poisson.linearBracket c f g := rfl

theorem forwardGraph_operator_eq_linearBracket (c : Fin d → Fin d → Fin d → k)
    (f g : Polynomial d k) :
    forwardGraph.operator (fun _ => c) f g = EnvelopingIsomorphism.Poisson.linearBracket c f g := by
  rw [forwardGraph_operator_apply, EnvelopingIsomorphism.Poisson.linearBracket]
  simp only [linearCoefficient, Finset.sum_mul, mul_assoc]

/-- No normalization factor occurs in the raw forward graph operator. -/
theorem forwardGraph_operator_eq_linearPoissonBinary (c : Fin d → Fin d → Fin d → k) :
    forwardGraph.operator (fun _ => c) = linearPoissonBinary c := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  exact forwardGraph_operator_eq_linearBracket c f g

theorem reverseGraph_operator_eq_swapped (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    reverseGraph.operator (fun _ => c) f g = forwardGraph.operator (fun _ => c) g f := by
  rw [reverseGraph_operator_apply, forwardGraph_operator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm (pderiv j f) (pderiv i g)]

/-- Reversing the two edges changes the sign for a skew bivector. -/
theorem reverseGraph_operator_eq_neg (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c) :
    reverseGraph.operator (fun _ => c) = -forwardGraph.operator (fun _ => c) := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change reverseGraph.operator (fun _ => c) f g = -forwardGraph.operator (fun _ => c) f g
  rw [reverseGraph_operator_eq_swapped, forwardGraph_operator_eq_linearBracket,
    forwardGraph_operator_eq_linearBracket, linearBracket_skew c hc]

section RationalWeights

variable {K : Type*} [Field K] [CharZero K]

/-- The rational values attached to the two ordered one-vertex graphs. -/
def oneVertexRationalWeight (Γ : KontsevichGraph 1) : K :=
  if Γ = forwardGraph then 1 / 4 else -1 / 4

omit [CharZero K] in
@[simp] theorem oneVertexRationalWeight_forward : oneVertexRationalWeight (K := K) forwardGraph = 1 / 4 :=
  if_pos rfl

omit [CharZero K] in
@[simp] theorem oneVertexRationalWeight_reverse : oneVertexRationalWeight (K := K) reverseGraph = -1 / 4 :=
  if_neg (Ne.symm forwardGraph_ne_reverseGraph)

/-- The two rationally weighted actual graph operators have exactly the HKR factor `1/2`. -/
theorem oneVertex_weighted_pair (c : Fin d → Fin d → Fin d → K) (hc : IsSkew c) :
    (1 / 4 : K) • forwardGraph.operator (fun _ => c) +
      (-1 / 4 : K) • reverseGraph.operator (fun _ => c) = (1 / 2 : K) • linearPoissonBinary c := by
  rw [reverseGraph_operator_eq_neg c hc, forwardGraph_operator_eq_linearPoissonBinary]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change (1 / 4 : K) • linearPoissonBinary c f g +
    (-1 / 4 : K) • (-linearPoissonBinary c f g) = (1 / 2 : K) • linearPoissonBinary c f g
  rw [smul_neg, ← neg_smul, ← add_smul]
  congr 1
  norm_num

/-- The same identity summed over the full finite set of admissible one-vertex graphs. -/
theorem weightedOperator_oneVertex_rational (c : Fin d → Fin d → Fin d → K) (hc : IsSkew c) :
    weightedOperator Finset.univ oneVertexRationalWeight (fun _ => c) =
      (1 / 2 : K) • linearPoissonBinary c := by
  rw [oneVertex_graph_univ, weightedOperator, Finset.sum_pair forwardGraph_ne_reverseGraph,
    oneVertexRationalWeight_forward, oneVertexRationalWeight_reverse]
  exact oneVertex_weighted_pair c hc

/-- An arbitrary weight assignment is determined by the two explicitly identified graph values. -/
theorem weightedOperator_oneVertex_of_values (w : KontsevichGraph 1 → K)
    (hwf : w forwardGraph = 1 / 4) (hwr : w reverseGraph = -1 / 4)
    (c : Fin d → Fin d → Fin d → K) (hc : IsSkew c) :
    weightedOperator Finset.univ w (fun _ => c) = (1 / 2 : K) • linearPoissonBinary c := by
  rw [oneVertex_graph_univ, weightedOperator, Finset.sum_pair forwardGraph_ne_reverseGraph, hwf, hwr]
  exact oneVertex_weighted_pair c hc

/-- The normalized first coefficient in the exact unbundled form consumed by graph-star lemmas. -/
theorem weightedOperator_oneVertex_first (c : Fin d → Fin d → Fin d → K) (hc : IsSkew c)
    (f g : Polynomial d K) :
    weightedOperator Finset.univ oneVertexRationalWeight (fun _ => c) f g =
      (2 : K)⁻¹ • EnvelopingIsomorphism.Poisson.linearBracket c f g := by
  rw [weightedOperator_oneVertex_rational c hc]
  change (1 / 2 : K) • EnvelopingIsomorphism.Poisson.linearBracket c f g = _
  rw [one_div]

end RationalWeights

end EnvelopingIsomorphism.Deformation.Kontsevich
