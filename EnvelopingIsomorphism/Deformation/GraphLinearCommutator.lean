import EnvelopingIsomorphism.Deformation.GraphDegree
import Mathlib.Tactic.FinCases
import EnvelopingIsomorphism.Poisson.FirstJet
import EnvelopingIsomorphism.Deformation.HKRCocycle
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Higher graph terms have zero commutator on linear inputs

The same linear skew bivector is inserted at every internal vertex. At order
two, a nonzero graph on linear inputs has one incoming edge at every vertex;
it is a two-cycle with one spoke to each input. Its coordinate sum is a
symmetric trace form. No graph-weight identity or associativity is assumed.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph

open MvPolynomial
open scoped BigOperators

section Ring

variable {k : Type*} [CommRing k] {d : ℕ}

@[simp] theorem pderiv_linearCoefficient (c : Fin d → k) (i : Fin d) :
    pderiv i (linearCoefficient c) = C (c i) := by
  simp [linearCoefficient, Pi.single_apply]

private def flipBit (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

private def flipBitEquiv : Fin 2 ≃ Fin 2 where
  toFun := flipBit
  invFun := flipBit
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The cycle edge at vertex zero has slot `p`, and the one at vertex one
has slot `q`. The remaining edge at vertex zero ends at external vertex `r`. -/
private def cycleTarget (p q r : Fin 2) : Edge 2 → Vertex 2 := fun e ↦
  if e.1 = 0 then
    if e.2 = p then Sum.inl 1 else Sum.inr r
  else
    if e.2 = q then Sum.inl 0 else Sum.inr (flipBit r)

private def cycleSource (p q r : Fin 2) : Vertex 2 → Edge 2
  | Sum.inl v => if v = 0 then (1, q) else (0, p)
  | Sum.inr v => if v = r then (0, flipBit p) else (1, flipBit q)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem classify_two_cycle :
    ∀ t : Edge 2 → Vertex 2,
      (∀ v a, t (v, a) ≠ Sum.inl v) →
      (∀ v, t (v, 0) ≠ t (v, 1)) → Function.Injective t →
      ∃ p q r, t = cycleTarget p q r := by
  decide

set_option maxRecDepth 4096 in
private theorem cycle_incoming_table : ∀ p q r v,
    (Finset.univ.filter (fun e : Edge 2 ↦ cycleTarget p q r e = v)) =
      {cycleSource p q r v} := by
  decide

private theorem incoming_of_cycle (Γ : KontsevichGraph 2) (p q r : Fin 2)
    (h : Γ.target = cycleTarget p q r) (v : Vertex 2) :
    Γ.incoming v = {cycleSource p q r v} := by
  change Finset.univ.filter (fun e ↦ Γ.target e = v) = _
  rw [h]
  exact cycle_incoming_table p q r v

/-- A nonzero order-two summand on degree-one inputs has injective edge target. -/
theorem target_injective_of_labelled_ne_zero [Nontrivial k]
    (Γ : KontsevichGraph 2) (α : Coefficients 2 d k) (lab : Edge 2 → Fin d)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1)
    (hne : Γ.labelledOperator α lab f g ≠ 0) : Function.Injective Γ.target := by
  have hprod : ∏ v : Vertex 2, Γ.vertexDerivative lab v (vertexInput α lab f g v) ≠ 0 := by
    simpa only [labelledOperator_apply] using hne
  have hcard (v : Vertex 2) : (Γ.incoming v).card ≤ 1 := by
    have hv : Γ.vertexDerivative lab v (vertexInput α lab f g v) ≠ 0 := by
      intro hz
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ v) hz)
    have hd := Γ.totalDegree_vertexDerivative_add_card_le lab v _ hv
    have hi : (vertexInput α lab f g v).totalDegree ≤ 1 := by
      cases v with
      | inl v => exact totalDegree_linearCoefficient_le _
      | inr j =>
        by_cases hj : j = 0
        · simpa [vertexInput, hj] using hf
        · simpa [vertexInput, hj] using hg
    omega
  intro e e' he
  apply Finset.card_le_one.mp (hcard (Γ.target e))
  · simp [incoming]
  · simp [incoming, he]

theorem operator_eq_zero_of_not_injective [Nontrivial k]
    (Γ : KontsevichGraph 2) (hΓ : ¬ Function.Injective Γ.target)
    (α : Coefficients 2 d k) (f g : Polynomial d k)
    (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) : Γ.operator α f g = 0 := by
  rw [operator_apply]
  apply Finset.sum_eq_zero
  intro lab _
  by_contra h
  exact hΓ (target_injective_of_labelled_ne_zero Γ α lab f g hf hg h)

private def cycleLabelled (c : Fin d → Fin d → Fin d → k) (p q r : Fin 2)
    (lab : Edge 2 → Fin d) (f g : Polynomial d k) : Polynomial d k :=
  C (c (lab (0, 0)) (lab (0, 1)) (lab (cycleSource p q r (Sum.inl 0)))) *
    C (c (lab (1, 0)) (lab (1, 1)) (lab (cycleSource p q r (Sum.inl 1)))) *
    (pderiv (lab (cycleSource p q r (Sum.inr 0))) f *
      pderiv (lab (cycleSource p q r (Sum.inr 1))) g)

private theorem labelledOperator_cycle (Γ : KontsevichGraph 2)
    (c : Fin d → Fin d → Fin d → k) (p q r : Fin 2)
    (h : Γ.target = cycleTarget p q r) (lab : Edge 2 → Fin d) (f g : Polynomial d k) :
    Γ.labelledOperator (fun _ ↦ c) lab f g = cycleLabelled c p q r lab f g := by
  rw [labelledOperator_apply]
  simp [Fintype.prod_sum_type, Fin.prod_univ_two, vertexDerivative,
    incoming_of_cycle Γ p q r h, vertexInput, cycleLabelled]

private def labelFlip (p q : Fin 2) : (Edge 2 → Fin d) ≃ (Edge 2 → Fin d) :=
  Equiv.arrowCongr
    (Equiv.prodCongr flipBitEquiv (if p = q then Equiv.refl _ else flipBitEquiv))
    (Equiv.refl _)

private theorem labelFlip_apply (p q : Fin 2) (lab : Edge 2 → Fin d) (e : Edge 2) :
    labelFlip p q lab e = lab (flipBit e.1, if p = q then e.2 else flipBit e.2) := by
  rcases e with ⟨v, s⟩
  by_cases h : p = q <;> simp [labelFlip, h, flipBitEquiv]

/-- Skew-symmetry of the bivector's two coordinate slots. -/
def IsSkew (c : Fin d → Fin d → Fin d → k) : Prop :=
  ∀ i j r, c j i r = -c i j r

private theorem skewProduct_reverse (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (a b r e f s : Fin d) :
    (C (c a b r) : Polynomial d k) * C (c e f s) = C (c f e s) * C (c b a r) := by
  rw [hc e f s, hc a b r]
  simp only [map_neg, neg_mul_neg]
  exact mul_comm _ _

private theorem cycleLabelled_flip (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (p q r : Fin 2) (lab : Edge 2 → Fin d) (f g : Polynomial d k) :
    cycleLabelled c p q r lab f g = cycleLabelled c p q r (labelFlip p q lab) g f := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;>
    simp [cycleLabelled, labelFlip_apply, cycleSource, flipBit]
  all_goals
    first
    | ac_rfl
    | rw [skewProduct_reverse c hc]
      ac_rfl

/-- Every two-cycle graph is separately symmetric, for arbitrary polynomial inputs.
The same linear bivector must be inserted at both internal vertices. -/
theorem operator_two_cycle_symmetric (Γ : KontsevichGraph 2)
    (hΓ : Function.Injective Γ.target) (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (f g : Polynomial d k) : Γ.operator (fun _ ↦ c) f g = Γ.operator (fun _ ↦ c) g f := by
  obtain ⟨p, q, r, h⟩ := classify_two_cycle Γ.target Γ.noLoops Γ.distinctTargets hΓ
  rw [operator_apply, operator_apply]
  apply Fintype.sum_equiv (labelFlip p q)
  intro lab
  rw [labelledOperator_cycle Γ c p q r h, labelledOperator_cycle Γ c p q r h]
  exact cycleLabelled_flip c hc p q r lab f g

/-- All order-two graph contributions have zero commutator on affine-linear inputs. -/
theorem operator_two_symmetric [Nontrivial k] (Γ : KontsevichGraph 2)
    (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c) (f g : Polynomial d k)
    (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    Γ.operator (fun _ ↦ c) f g = Γ.operator (fun _ ↦ c) g f := by
  by_cases hΓ : Function.Injective Γ.target
  · exact operator_two_cycle_symmetric Γ hΓ c hc f g
  · rw [operator_eq_zero_of_not_injective Γ hΓ _ f g hf hg,
      operator_eq_zero_of_not_injective Γ hΓ _ g f hg hf]

/-- Every graph of order at least two has zero commutator on affine-linear inputs. -/
theorem operator_higher_symmetric [Nontrivial k] {n : ℕ} (Γ : KontsevichGraph n)
    (hn : 2 ≤ n) (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    Γ.operator (fun _ ↦ c) f g = Γ.operator (fun _ ↦ c) g f := by
  by_cases h₂ : n = 2
  · subst n
    exact operator_two_symmetric Γ c hc f g hf hg
  · have hfg : f.totalDegree + g.totalDegree < n := by omega
    have hgf : g.totalDegree + f.totalDegree < n := by omega
    rw [operator_eq_zero_of_degree_lt Γ _ f g hfg,
      operator_eq_zero_of_degree_lt Γ _ g f hgf]

/-- Arbitrary graph weights preserve the vanishing higher commutator. -/
theorem weightedOperator_higher_symmetric [Nontrivial k] {n : ℕ}
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → k) (hn : 2 ≤ n)
    (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    weightedOperator s w (fun _ ↦ c) f g = weightedOperator s w (fun _ ↦ c) g f := by
  rw [weightedOperator_apply, weightedOperator_apply]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [operator_higher_symmetric Γ hn c hc f g hf hg]

/-- The commutator of any finite weighted graph expansion on linear inputs
is exactly its order-one commutator. No identities among higher weights are used. -/
theorem finiteStarOperator_commutator_first [Nontrivial k] (N : ℕ) (hN : 0 < N)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    finiteStarOperator N s w c f g - finiteStarOperator N s w c g f =
      weightedOperator (s 0) (w 0) (fun _ ↦ c) f g -
        weightedOperator (s 0) (w 0) (fun _ ↦ c) g f := by
  calc
    _ = (finiteStarOperator N s w c f g - f * g) -
        (finiteStarOperator N s w c g f - g * f) := by ring
    _ = ∑ j ∈ Finset.range N,
        (weightedOperator (s j) (w j) (fun _ ↦ c) f g -
          weightedOperator (s j) (w j) (fun _ ↦ c) g f) := by
      rw [finiteStarOperator_sub_mul, finiteStarOperator_sub_mul, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_eq_single 0
      · intro j hj hj₀
        rw [weightedOperator_higher_symmetric (s j) (w j) (by omega) c hc f g hf hg,
          sub_self]
      · intro h
        exact False.elim (h (Finset.mem_range.mpr hN))

/-- The coordinate-linear bracket is skew when its bivector coefficients are skew. -/
theorem linearBracket_skew (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (f g : Polynomial d k) :
    EnvelopingIsomorphism.Poisson.linearBracket c g f = -EnvelopingIsomorphism.Poisson.linearBracket c f g := by
  unfold EnvelopingIsomorphism.Poisson.linearBracket
  simp only [← Finset.sum_neg_distrib]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  rw [hc i j r, map_neg]
  ring

end Ring

section NormalizedFirstTerm

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

/-- The actual factorial-normalized HKR bivector cochain has the expected
antisymmetric part; normalization is consumed exactly once. -/
theorem normalizedHkr_two_commutator {A : Type*} [CommRing A] [Algebra k A]
    (b : A) (D : Fin 2 → Derivation k A A) (f g : A) :
    hkrCochain b D (Fin.cons f (Fin.cons g Fin.elim0)) -
      hkrCochain b D (Fin.cons g (Fin.cons f Fin.elim0)) =
        b * (D 0 f * D 1 g - D 1 f * D 0 g) := by
  rw [hkrCochain_apply, hkrCochain_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  change (Nat.factorial 2 : k)⁻¹ • (b * (D 0 f * D 1 g - D 1 f * D 0 g)) -
    (Nat.factorial 2 : k)⁻¹ • (b * (D 0 g * D 1 f - D 1 g * D 0 f)) = _
  have hswap : b * (D 0 g * D 1 f - D 1 g * D 0 f) =
      -(b * (D 0 f * D 1 g - D 1 f * D 0 g)) := by ring
  rw [hswap, smul_neg, sub_neg_eq_add, ← smul_add, ← two_smul k, smul_smul]
  norm_num

/-- With the normalized HKR first term, the exact linear commutator is `h` times
the original linear bracket. The first-order normalization is stated explicitly;
no analytic value for any graph weight is claimed here. -/
theorem finiteStarOperator_linear_commutator (N : ℕ) (hN : 0 < N)
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c) (h : k)
    (hfirst : ∀ p q : Polynomial d k,
      weightedOperator (s 0) (w 0) (fun _ ↦ c) p q =
        (h * (2 : k)⁻¹) • EnvelopingIsomorphism.Poisson.linearBracket c p q)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
    finiteStarOperator N s w c f g - finiteStarOperator N s w c g f =
      h • EnvelopingIsomorphism.Poisson.linearBracket c f g := by
  rw [finiteStarOperator_commutator_first N hN s w c hc f g hf hg,
    hfirst, hfirst, linearBracket_skew c hc f g]
  rw [smul_neg, sub_neg_eq_add, ← smul_add, ← two_smul k, smul_smul]
  congr 1
  simp

end NormalizedFirstTerm

section FormalGraphSeries

variable {k : Type*} [CommRing k] {d : ℕ}

/-- The actual formal graph expansion, with ordinary multiplication at order zero.
Its definition makes no associativity assertion. -/
def graphStarSeries (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) : PowerSeries (Polynomial d k) :=
  PowerSeries.mk (fun n ↦ match n with
    | 0 => f * g
    | j + 1 => weightedOperator (s j) (w j) (fun _ ↦ c) f g)

@[simp] theorem coeff_graphStarSeries_zero
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) :
    PowerSeries.coeff 0 (graphStarSeries s w c f g) = f * g := by
  rw [graphStarSeries, PowerSeries.coeff_mk]

@[simp] theorem coeff_graphStarSeries_succ
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (f g : Polynomial d k) (j : ℕ) :
    PowerSeries.coeff (j + 1) (graphStarSeries s w c f g) =
      weightedOperator (s j) (w j) (fun _ ↦ c) f g := by
  rw [graphStarSeries, PowerSeries.coeff_mk]

end FormalGraphSeries

section NormalizedFirstTerm

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

/-- The full formal graph expansion has the exact linear commutator `h {f,g}`.
Only the normalized first Taylor coefficient is an input; every higher graph
commutator vanishes individually. -/
theorem graphStarSeries_linear_commutator
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → k)
    (c : Fin d → Fin d → Fin d → k) (hc : IsSkew c)
    (hfirst : ∀ p q : Polynomial d k,
      weightedOperator (s 0) (w 0) (fun _ ↦ c) p q =
        (2 : k)⁻¹ • EnvelopingIsomorphism.Poisson.linearBracket c p q)
    (f g : Polynomial d k) (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) :
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
        smul_neg, sub_neg_eq_add, ← smul_add, ← two_smul k, smul_smul]
      norm_num
    | succ n =>
      rw [map_sub, coeff_graphStarSeries_succ, coeff_graphStarSeries_succ,
        weightedOperator_higher_symmetric (s (n + 1)) (w (n + 1)) (by omega) c hc f g hf hg,
        sub_self]
      simp [PowerSeries.coeff_mul_C, PowerSeries.coeff_X]

end NormalizedFirstTerm

end EnvelopingIsomorphism.Deformation.KontsevichGraph
