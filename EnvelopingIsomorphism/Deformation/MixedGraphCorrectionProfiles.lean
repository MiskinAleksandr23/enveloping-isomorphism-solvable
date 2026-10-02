import EnvelopingIsomorphism.Deformation.GeneralGraphTwoOddProfiles
import EnvelopingIsomorphism.Deformation.MixedGraphProfileCarrier
import EnvelopingIsomorphism.Deformation.UniformCurvatureSplits

/-! The two-odd source correction for the mixed path identity. Quotient graphs
have one vector, one trivector and n independent binary vertices. Their six
actual splits lie in the common one-vector carrier with n+2 binary vertices.
The X-before-Q placement sign and the raw curvature factor one-half are explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles

open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open SchoutenGraphContraction MixedGraphProfileCarrier GraphCoefficientProfiles
open scoped BigOperators Classical

variable {n : ℕ}

abbrev Placement (n : ℕ) := (i : Fin (n + 2)) × {j : Fin (n + 2) // j ≠ i}
abbrev QuotientGraph (p : Placement n) := Graph (twoOddArity p.1 p.2) 2
abbrev CorrectionGraph (n : ℕ) := (p : Placement n) × QuotientGraph p

theorem edgeCount (p : Placement n) :
    ∑ v, twoOddArity p.1 p.2 v = Kontsevich.GraphForms.dimension (n + 1) 2 := by
  rw [twoOddArity_sum p.1 p.2 p.2.property]
  unfold Kontsevich.GraphForms.dimension
  omega

def expandedVector (p : Placement n) : Fin (n + 3) := vertexSplitOldEmbedding p.2 p.1

theorem splitArity (p : Placement n) :
    vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2 =
      Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (expandedVector p) := by
  funext v
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv p.2.val).symm.surjective v
  cases s with
  | inl w =>
    have he : vertexSplitOldEmbedding p.2.val w.val = expandedVector p ↔ w.val = p.1 :=
      (splitExternalEmbedding_injective p.2.val).eq_iff
    simp only [vertexSplitSourceEquiv_symm_old, vertexSplitArity_old _ _ _ _ w.property,
      Gauge.PlacedMixedGraphTaylorCoefficients.arities, he, twoOddArity, if_neg w.property]
  | inr c =>
    have he : vertexSplitChild p.2.val c ≠ expandedVector p :=
      (vertexSplitOld_ne_child p.2.val p.1 p.2.property.symm c).symm
    simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities, he, bivectorArity]

theorem selectedArity (p : Placement n) : 3 = twoOddArity p.1 p.2 p.2 :=
  (twoOddArity_trivector p.1 p.2 p.2.property).symm

abbrev SplitChoices (p : Placement n) (Θ : QuotientGraph p) := Θ.VertexSplitChoices p.2

def splitForward (p : Placement n) (Θ : QuotientGraph p) (c : Fin 3) (χ : SplitChoices p Θ) :
    VectorGraph (n + 2) 2 :=
  ofProfile (expandedVector p) (splitArity p)
    (Θ.vertexSplit (bivectorForward (cyclicPermutation c)) p.2 (selectedArity p).symm χ)

def splitReverse (p : Placement n) (Θ : QuotientGraph p) (c : Fin 3) (χ : SplitChoices p Θ) :
    VectorGraph (n + 2) 2 :=
  ofProfile (expandedVector p) (splitArity p)
    (Θ.vertexSplit (bivectorReverse (cyclicPermutation c)) p.2 (selectedArity p).symm χ)

@[simp] theorem splitForward_vertex (p : Placement n) (Θ : QuotientGraph p) (c : Fin 3)
    (χ : SplitChoices p Θ) : (splitForward p Θ c χ).vertex = expandedVector p := rfl

@[simp] theorem splitReverse_vertex (p : Placement n) (Θ : QuotientGraph p) (c : Fin 3)
    (χ : SplitChoices p Θ) : (splitReverse p Θ c χ).vertex = expandedVector p := rfl

variable {k : Type*} [Field k] [CharZero k] {d : ℕ}

abbrev Trivector := Multiderivation k (MvPolynomial (Fin d) k) 3

def quotientTensors (p : Placement n) (B : Fin (n + 2) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) (Q : Trivector (k := k) (d := d)) :=
  twoOddTensors p.1 p.2 p.2.property (rawTensor X) (rawTensor Q) (fun v => rawTensor (B v))

def quotientValue (p : Placement n) (Θ : QuotientGraph p)
    (B : Fin (n + 2) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) (Q : Trivector (k := k) (d := d)) :
    Cochain k (MvPolynomial (Fin d) k) 2 := Θ.cochainOperator (quotientTensors p B X Q)

omit [CharZero k] in
private theorem tensorCast_heq {a b : ℕ} (h : a = b) (T : Tensor a d k) : HEq (tensorCast h T) T := by
  subst b
  rfl

omit [CharZero k] in
private theorem castTensors_heq {l : ℕ} {q q' : Fin l → ℕ} (h : q = q')
    (T : (v : Fin l) → Tensor (q v) d k) (v : Fin l) :
    HEq (UniformBinaryGraphs.castTensors h T v) (T v) := by
  subst q'
  rfl

omit [CharZero k] in
private theorem cast_linear_apply_heq {A : Type*} [AddCommGroup A] [Module k A]
    {p q : ℕ} (h : p = q) (L : A →ₗ[k] Tensor p d k) (a : A) :
    HEq ((cast (congrArg (fun r => A →ₗ[k] Tensor r d k) h) L) a) (L a) := by
  cases h
  rfl

omit [CharZero k] in
theorem rawTensors_vector_heq (i : Fin (n + 1))
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    HEq (rawTensors i B X i) (rawTensor X) := by
  simp only [rawTensors, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor,
    dite_true, ite_true]
  exact cast_linear_apply_heq (by simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities]) _ _

omit [CharZero k] in
theorem rawTensors_binary_heq (i v : Fin (n + 1)) (hvi : v ≠ i)
    (B : Fin (n + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    HEq (rawTensors i B X v) (rawTensor (B v)) := by
  simp only [rawTensors, if_neg hvi, Gauge.PlacedMixedGraphTaylorCoefficients.vertexTensor, dif_neg hvi]
  exact cast_linear_apply_heq (by simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities, hvi]) _ _

def splitTensors (p : Placement n)
    (T : (v : Fin (n + 2)) → Tensor (twoOddArity p.1 p.2 v) d k)
    (U : Fin 2 → Tensor 2 d k) :=
  UniformBinaryGraphs.castTensors (splitArity p)
    (vertexSplitTensors (twoOddArity p.1 p.2) bivectorArity p.2 T U)

/-- Each old coefficient and each of the two independent children is retained
by the actual split tensor transport; the vector tensor remains at its genuine image. -/
theorem splitTensors_independent (p : Placement n)
    (B : Fin (n + 3) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    splitTensors p (quotientTensors p (B ∘ vertexSplitOldEmbedding p.2) X 0)
      (bivectorPairTensors (B (vertexSplitChild p.2 0)) (B (vertexSplitChild p.2 1))) =
      rawTensors (expandedVector p) B X := by
  funext v
  apply eq_of_heq
  refine (castTensors_heq (splitArity p) _ v).trans ?_
  obtain ⟨s, rfl⟩ := (vertexSplitSourceEquiv p.2.val).symm.surjective v
  cases s with
  | inl w =>
    rw [vertexSplitSourceEquiv_symm_old]
    refine (vertexSplitTensors_old_heq _ _ _ _ _ w.val w.property).trans ?_
    by_cases hw : w.val = p.1
    · rw [hw]
      exact (twoOddTensors_vector_heq _ _ _ _ _ _).trans (rawTensors_vector_heq _ B X).symm
    · have he : vertexSplitOldEmbedding p.2.val w.val ≠ expandedVector p :=
        fun h => hw (splitExternalEmbedding_injective p.2.val h)
      exact (twoOddTensors_binary_heq _ _ _ _ _ _ w.val hw w.property).trans
        (rawTensors_binary_heq _ _ he B X).symm
  | inr c =>
    rw [vertexSplitSourceEquiv_symm_child]
    refine (vertexSplitTensors_child_heq _ _ _ _ _ c).trans ?_
    have he : vertexSplitChild p.2.val c ≠ expandedVector p :=
      (vertexSplitOld_ne_child p.2.val p.1 p.2.property.symm c).symm
    fin_cases c <;> exact (rawTensors_binary_heq _ _ he B X).symm

theorem quotientTensors_eq_update (p : Placement n)
    (B : Fin (n + 2) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) (Q : Trivector (k := k) (d := d)) :
    quotientTensors p B X Q = Function.update (quotientTensors p B X 0) p.2
      (tensorCast (selectedArity p) (rawTensor Q)) := by
  funext v
  by_cases hvj : v = p.2.val
  · subst v
    rw [Function.update_self]
    exact eq_of_heq ((twoOddTensors_trivector_heq _ _ _ _ _ _).trans (tensorCast_heq _ _).symm)
  · rw [Function.update_of_ne hvj]
    by_cases hvi : v = p.1
    · subst v
      exact eq_of_heq ((twoOddTensors_vector_heq _ _ _ _ _ _).trans
        (twoOddTensors_vector_heq _ _ _ _ _ _).symm)
    · exact eq_of_heq ((twoOddTensors_binary_heq _ _ _ _ _ _ v hvi hvj).trans
        (twoOddTensors_binary_heq p.1 p.2 p.2.property (rawTensor X) (rawTensor 0)
          (fun v => rawTensor (B v)) v hvi hvj).symm)

/-- An arbitrary independent pair F,G replaces the trivector by the actual
six joined graph families. Incoming-arrow choices are all retained. -/
theorem quotientValue_bracket (p : Placement n) (Θ : QuotientGraph p)
    (B : Fin (n + 3) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    quotientValue p Θ (B ∘ vertexSplitOldEmbedding p.2) X
      (schoutenBracket k d 1 1 (B (vertexSplitChild p.2 0)) (B (vertexSplitChild p.2 1))) =
      ∑ c : Fin 3, ∑ χ : SplitChoices p Θ,
        (rawValue (splitForward p Θ c χ) B X + rawValue (splitReverse p Θ c χ) B X) := by
  unfold quotientValue
  rw [quotientTensors_eq_update]
  apply MultilinearMap.ext
  intro f
  rw [cochainOperator_bivector_bracket_vertexSplit]
  simp only [sum_apply, add_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro χ _
  · change _ = (UniformBinaryGraphs.castGraph (splitArity p)
      (Θ.vertexSplit (bivectorForward (cyclicPermutation c)) p.2 (selectedArity p).symm χ)).cochainOperator
        (rawTensors (expandedVector p) B X) f
    rw [← splitTensors_independent p B X]
    exact congrArg (fun C => C f) (UniformBinaryGraphs.cochainOperator_castGraph (splitArity p) _ _).symm
  · change _ = (UniformBinaryGraphs.castGraph (splitArity p)
      (Θ.vertexSplit (bivectorReverse (cyclicPermutation c)) p.2 (selectedArity p).symm χ)).cochainOperator
        (rawTensors (expandedVector p) B X) f
    rw [← splitTensors_independent p B X]
    exact congrArg (fun C => C f) (UniformBinaryGraphs.cochainOperator_castGraph (splitArity p) _ _).symm

def splitProfile (p : Placement n) (Θ : QuotientGraph p) : VectorGraph (n + 2) 2 → k :=
  ∑ c : Fin 3, (pushforward (splitForward p Θ c) (fun _ => 1) +
    pushforward (splitReverse p Θ c) (fun _ => 1))

theorem evaluation_splitProfile (p : Placement n) (Θ : QuotientGraph p)
    (B : Fin (n + 3) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun Γ => rawValue Γ B X) (splitProfile (k := k) p Θ) =
      quotientValue p Θ (B ∘ vertexSplitOldEmbedding p.2) X
        (schoutenBracket k d 1 1 (B (vertexSplitChild p.2 0)) (B (vertexSplitChild p.2 1))) := by
  rw [quotientValue_bracket]
  simp only [splitProfile, map_sum, map_add, evaluation_pushforward, one_smul,
    Finset.sum_add_distrib]

/-- This is the fixed ordered-argument sign X,Q,B..., not an unsigned placement sum. -/
def placementSign (p : Placement n) : k := (twoOddPlacementSign p.1 p.2 : k)

theorem placementSign_eq (p : Placement n) :
    placementSign (k := k) p = if p.1 < p.2.val then 1 else -1 := by
  unfold placementSign twoOddPlacementSign
  split_ifs <;> simp

/-- The scalar correction retains every quotient placement, every actual incoming
assignment, all six source graphs, and the explicit curvature coefficient one-half. -/
def correctionProfile (w : CorrectionGraph n → k) : VectorGraph (n + 2) 2 → k :=
  (1 / 2 : k) • ∑ p : Placement n, ∑ Θ : QuotientGraph p,
    (placementSign p * w ⟨p, Θ⟩) • splitProfile p Θ

theorem splitProfile_apply (p : Placement n) (Θ : QuotientGraph p) (H : VectorGraph (n + 2) 2) :
    splitProfile (k := k) p Θ H = ∑ c : Fin 3, ∑ χ : SplitChoices p Θ,
      ((if splitForward p Θ c χ = H then 1 else 0) + (if splitReverse p Θ c χ = H then 1 else 0)) := by
  simp only [splitProfile, Finset.sum_apply, Pi.add_apply, pushforward_apply, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro c _ <;>
    apply Finset.sum_congr rfl <;> intro χ _ <;> split_ifs <;> rfl

theorem correctionProfile_apply (w : CorrectionGraph n → k) (H : VectorGraph (n + 2) 2) :
    correctionProfile w H = (1 / 2 : k) * ∑ p : Placement n, ∑ Θ : QuotientGraph p,
      (if p.1 < p.2.val then 1 else -1) * w ⟨p, Θ⟩ *
        ∑ c : Fin 3, ∑ χ : SplitChoices p Θ,
          ((if splitForward p Θ c χ = H then 1 else 0) + (if splitReverse p Θ c χ = H then 1 else 0)) := by
  simp only [correctionProfile, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    placementSign_eq, splitProfile_apply]

/-- The pure scalar correction has this exact independent-input evaluation.
The selected bracket pair is read from its actual two children at each placement. -/
theorem evaluation_correctionProfile (w : CorrectionGraph n → k)
    (B : Fin (n + 3) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun Γ => rawValue Γ B X) (correctionProfile w) =
      (1 / 2 : k) • ∑ p : Placement n, ∑ Θ : QuotientGraph p,
        (placementSign p * w ⟨p, Θ⟩) • quotientValue p Θ (B ∘ vertexSplitOldEmbedding p.2) X
          (schoutenBracket k d 1 1 (B (vertexSplitChild p.2 0)) (B (vertexSplitChild p.2 1))) := by
  simp only [correctionProfile, map_smul, map_sum, evaluation_splitProfile]

section Canonical

variable [Algebra ℝ k]

def canonicalQuotientWeight (Γ : CorrectionGraph n) : k :=
  algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalEffectiveWeight Γ.2 (edgeCount Γ.1))

/-- Quotient MC normalization is exactly its total (n+2)-vertex factorial. -/
theorem canonicalQuotientWeight_factorial (Γ : CorrectionGraph n) :
    canonicalQuotientWeight (k := k) Γ = ((n + 2).factorial : ℚ)⁻¹ •
      algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalWeight Γ.2 (edgeCount Γ.1)) :=
  Kontsevich.map_effectiveMCWeight (algebraMap ℝ k).toAddMonoidHom (n + 2) _

/-- The actual canonical scalar correction includes the two-odd placement sign,
one-half, and the quotient factorial before any operator evaluation. -/
theorem canonical_correctionProfile_apply (H : VectorGraph (n + 2) 2) :
    correctionProfile (canonicalQuotientWeight (k := k)) H =
      (1 / 2 : k) * ∑ p : Placement n, ∑ Θ : QuotientGraph p,
        (if p.1 < p.2.val then 1 else -1) *
          (((n + 2).factorial : ℚ)⁻¹ • algebraMap ℝ k
            (Kontsevich.GeometricWeights.canonicalWeight Θ (edgeCount p))) *
          ∑ c : Fin 3, ∑ χ : SplitChoices p Θ,
            ((if splitForward p Θ c χ = H then 1 else 0) + (if splitReverse p Θ c χ = H then 1 else 0)) := by
  rw [correctionProfile_apply]
  simp only [canonicalQuotientWeight_factorial]

end Canonical

end EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles
