import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexNormalization

/-! The geometric normalization and exact linear commutator over parameter
algebras. The coefficient ring need not itself be a field. -/

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators

namespace KontsevichGraph

variable {R : Type*} [CommRing R] [Nontrivial R] {d : ℕ}

/-- The finite linear commutator only needs a normalized first coefficient;
inverting two in the entire coefficient ring is unnecessary. -/
theorem finiteStarOperator_linear_commutator_of_normalization
    (N : ℕ) (hN : 0 < N)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (hc : IsSkew c)
    (q h : R) (hq : q + q = h)
    (hfirst : ∀ p p' : Polynomial d R,
      weightedOperator (s 0) (w 0) (fun _ ↦ c) p p' =
        q • EnvelopingIsomorphism.Poisson.linearBracket c p p')
    (f g : Polynomial d R) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    finiteStarOperator N s w c f g - finiteStarOperator N s w c g f =
      h • EnvelopingIsomorphism.Poisson.linearBracket c f g := by
  rw [finiteStarOperator_commutator_first N hN s w c hc f g hf hg,
    hfirst, hfirst, linearBracket_skew c hc f g,
    smul_neg, sub_neg_eq_add, ← add_smul, hq]

/-- The formal linear commutator is valid over any parameter algebra with
a first graph coefficient whose double is the Poisson bracket. -/
theorem graphStarSeries_linear_commutator_of_normalization
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
    (c : Fin d → Fin d → Fin d → R) (hc : IsSkew c)
    (q : R) (hq : q + q = 1)
    (hfirst : ∀ p p' : Polynomial d R,
      weightedOperator (s 0) (w 0) (fun _ ↦ c) p p' =
        q • EnvelopingIsomorphism.Poisson.linearBracket c p p')
    (f g : Polynomial d R) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    graphStarSeries s w c f g - graphStarSeries s w c g f =
      PowerSeries.X * PowerSeries.C (EnvelopingIsomorphism.Poisson.linearBracket c f g) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [map_sub, coeff_graphStarSeries_zero, coeff_graphStarSeries_zero,
      PowerSeries.coeff_zero_X_mul]
    ring
  | succ n =>
    cases n with
    | zero =>
      simp only [map_sub, coeff_graphStarSeries_succ, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C]
      rw [hfirst, hfirst, linearBracket_skew c hc f g,
        smul_neg, sub_neg_eq_add, ← add_smul, hq, one_smul]
      simp only [if_true]
    | succ n =>
      rw [map_sub, coeff_graphStarSeries_succ, coeff_graphStarSeries_succ,
        weightedOperator_higher_symmetric (s (n + 1)) (w (n + 1)) (by omega) c hc f g hf hg,
        sub_self]
      simp [PowerSeries.coeff_mul_C, PowerSeries.coeff_X]

end KontsevichGraph

namespace Kontsevich

open KontsevichGraph

variable {R : Type*} [CommRing R] [Algebra ℝ R] {d : ℕ}

/-- The actual integral weights supply the first coefficient over any real
parameter algebra, including polynomial coefficient rings. -/
theorem weightedOperator_oneVertex_geometric_over_algebra
    (c : Fin d → Fin d → Fin d → R) (hc : IsSkew c) :
    weightedOperator Finset.univ
      (fun Γ ↦ algebraMap ℝ R (geometricOneVertexGraphWeight Γ)) (fun _ ↦ c) =
      algebraMap ℝ R (1 / 2) • linearPoissonBinary c := by
  classical
  rw [oneVertex_graph_univ, weightedOperator, Finset.sum_pair forwardGraph_ne_reverseGraph,
    geometricOneVertexGraphWeight_forward, geometricOneVertexGraphWeight_reverse,
    reverseGraph_operator_eq_neg c hc, forwardGraph_operator_eq_linearPoissonBinary]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change algebraMap ℝ R (1 / 4) • linearPoissonBinary c f g +
    algebraMap ℝ R (-1 / 4) • (-linearPoissonBinary c f g) =
      algebraMap ℝ R (1 / 2) • linearPoissonBinary c f g
  rw [smul_neg, ← neg_smul, ← add_smul, ← map_neg, ← map_add]
  congr 1
  norm_num

theorem geometric_half_add_self :
    algebraMap ℝ R (1 / 2) + algebraMap ℝ R (1 / 2) = 1 := by
  rw [← map_add]
  norm_num

end Kontsevich

end EnvelopingIsomorphism.Deformation
