import EnvelopingIsomorphism.Deformation.MixedGraphTargetEvaluation
import EnvelopingIsomorphism.Deformation.SymmetrizedGraphInsertion
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationPath
import EnvelopingIsomorphism.FormalSeries.LaurentGroupedMultilinear

/-! Exact ordered independent-input evaluation of the one-vector graft carrier,
followed by genuine multilinear grouping and background symmetrization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles

open MixedGraphProfileCarrier MixedGraphAveraging GraphCoefficientProfiles UniformBinaryGraphs
open EnvelopingIsomorphism.FormalSeries
open scoped BigOperators Classical

variable {a b n d : ℕ}

theorem placementEquiv_inl_succAbove (i : Fin (n + 1)) (j : Fin n) :
    placementEquiv i (Sum.inl j) = i.succAbove j := by
  change ({i}ᶜ : Finset (Fin (n + 1))).orderEmbOfFin (by simp [Finset.card_compl]) j = _
  rw [Finset.orderEmbOfFin_compl_singleton_apply]
  rfl

/-- The old increasing vector-graph complement is the first block of the new complement. -/
theorem placement_vectorEmbedding (i : Fin (a + 1)) (j : Fin a) :
    vectorEmbedding a b (placementEquiv i (Sum.inl j)) =
      placementEquiv (vectorEmbedding a b i) (Sum.inl (Fin.castAdd b j)) := by
  rw [placementEquiv_inl_succAbove, placementEquiv_inl_succAbove]
  apply Fin.ext
  simp only [Fin.succAbove, vectorEmbedding, outputVertexEquiv,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply,
    Fin.castAddEmb_apply, Fin.val_cast, Fin.val_castAdd, Fin.lt_def, Fin.val_castSucc,
    apply_ite, Fin.val_succ]
  split_ifs <;> rfl

/-- Every binary-graph vertex is the second block of the new increasing complement. -/
theorem placement_binaryEmbedding (i : Fin (a + 1)) (j : Fin b) :
    binaryEmbedding a b j =
      placementEquiv (vectorEmbedding a b i) (Sum.inl (Fin.natAdd a j)) := by
  rw [placementEquiv_inl_succAbove]
  apply Fin.ext
  have hi := i.isLt
  simp only [Fin.succAbove, vectorEmbedding, binaryEmbedding, outputVertexEquiv,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply,
    Fin.castAddEmb_apply, Fin.natAddEmb_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    Fin.lt_def, Fin.val_castSucc, apply_ite, Fin.val_succ]
  split_ifs <;> omega

variable {k : Type*} [Field k]

theorem fillBackground_vectorEmbedding (i : Fin (a + 1))
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (j : Fin a) :
    fillBackground (vectorEmbedding a b i) R (vectorEmbedding a b (placementEquiv i (Sum.inl j))) =
      R (Fin.castAdd b j) := by
  rw [placement_vectorEmbedding, fillBackground_placement]

theorem fillBackground_binaryEmbedding (i : Fin (a + 1))
    (R : Fin (a + b) → Bivector (k := k) (d := d)) :
    fillBackground (vectorEmbedding a b i) R ∘ binaryEmbedding a b = fun j => R (Fin.natAdd a j) := by
  funext j
  simp only [Function.comp_apply, placement_binaryEmbedding i j, fillBackground_placement]

theorem rawUnary_filled_block (Γ : VectorGraph a 1)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawUnary Γ (fillBackground (vectorEmbedding a b Γ.vertex) R ∘ vectorEmbedding a b) X =
      unaryValue Γ (fun j => R (Fin.castAdd b j)) X := by
  have h := operator_eq_rawValue Γ
    (fillBackground (vectorEmbedding a b Γ.vertex) R ∘ vectorEmbedding a b) X
  simp only [Function.comp_apply, fillBackground_vectorEmbedding] at h
  exact congrArg (cochainOneEquiv k (MvPolynomial (Fin d) k)) h.symm

theorem binaryValue_eq_raw_filled (Γ : VectorGraph n 2)
    (R : Fin n → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    binaryValue Γ R X = rawBinaryValue Γ (fillBackground Γ.vertex R) X :=
  congrArg (cochainTwoEquiv k (MvPolynomial (Fin d) k)) (operator_eq_filled Γ R X)

theorem sum_outputGraft_ordered (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    (∑ χ : OutputChoices (b := b) Γ, binaryValue (outputGraft Γ Δ χ) R X) =
      (independentBinary Δ (fun j => R (Fin.natAdd a j))).compr₂
        (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  have h := sum_outputGraft_raw Γ Δ (fillBackground (vectorEmbedding a b Γ.vertex) R) X
  rw [map_sum] at h
  change (∑ χ, rawBinaryValue (outputGraft Γ Δ χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X) = _ at h
  have he (χ : OutputChoices (b := b) Γ) :
      rawBinaryValue (outputGraft Γ Δ χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X =
        binaryValue (outputGraft Γ Δ χ) R X := (binaryValue_eq_raw_filled _ R X).symm
  simp_rw [he] at h
  rw [fillBackground_binaryEmbedding, rawUnary_filled_block] at h
  exact h

theorem sum_inputGraft_ordered_left (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    (∑ χ : InputChoices (a := a) Δ 0, binaryValue (inputGraft Γ Δ 0 χ) R X) =
      (independentBinary Δ (fun j => R (Fin.natAdd a j))).comp
        (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  have h := sum_inputGraft_raw_left Γ Δ (fillBackground (vectorEmbedding a b Γ.vertex) R) X
  rw [map_sum] at h
  change (∑ χ, rawBinaryValue (inputGraft Γ Δ 0 χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X) = _ at h
  have he (χ : InputChoices (a := a) Δ 0) :
      rawBinaryValue (inputGraft Γ Δ 0 χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X =
        binaryValue (inputGraft Γ Δ 0 χ) R X := (binaryValue_eq_raw_filled _ R X).symm
  simp_rw [he] at h
  rw [fillBackground_binaryEmbedding, rawUnary_filled_block] at h
  exact h

theorem sum_inputGraft_ordered_right (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    (∑ χ : InputChoices (a := a) Δ 1, binaryValue (inputGraft Γ Δ 1 χ) R X) =
      (independentBinary Δ (fun j => R (Fin.natAdd a j))).compl₂
        (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  have h := sum_inputGraft_raw_right Γ Δ (fillBackground (vectorEmbedding a b Γ.vertex) R) X
  rw [map_sum] at h
  change (∑ χ, rawBinaryValue (inputGraft Γ Δ 1 χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X) = _ at h
  have he (χ : InputChoices (a := a) Δ 1) :
      rawBinaryValue (inputGraft Γ Δ 1 χ) (fillBackground (vectorEmbedding a b Γ.vertex) R) X =
        binaryValue (inputGraft Γ Δ 1 χ) R X := (binaryValue_eq_raw_filled _ R X).symm
  simp_rw [he] at h
  rw [fillBackground_binaryEmbedding, rawUnary_filled_block] at h
  exact h

theorem evaluation_outputProfile_ordered (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (outputProfile w v) R X =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        (independentBinary Δ (fun j => R (Fin.natAdd a j))).compr₂
          (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  rw [outputProfile, evaluation_pushforward]
  simp only [sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  dsimp only
  rw [← Finset.smul_sum, sum_outputGraft_ordered]

theorem evaluation_inputProfile_ordered_left (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (inputProfile 0 w v) R X =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        (independentBinary Δ (fun j => R (Fin.natAdd a j))).comp
          (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  rw [inputProfile, evaluation_pushforward]
  simp only [sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  dsimp only
  rw [← Finset.smul_sum, sum_inputGraft_ordered_left]

theorem evaluation_inputProfile_ordered_right (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (inputProfile 1 w v) R X =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        (independentBinary Δ (fun j => R (Fin.natAdd a j))).compl₂
          (unaryValue Γ (fun j => R (Fin.castAdd b j)) X) := by
  rw [inputProfile, evaluation_pushforward]
  simp only [sum_apply, smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  dsimp only
  rw [← Finset.smul_sum, sum_inputGraft_ordered_right]

/-- The genuine ordered independent carrier evaluation gives the original weighted action sum. -/
theorem evaluation_actionProfile_ordered (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (R : Fin (a + b) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (binaryValue (k := k) (d := d)) (actionProfile w v) R X =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        unaryAction (unaryValue Γ (fun j => R (Fin.castAdd b j)) X)
          (independentBinary Δ (fun j => R (Fin.natAdd a j))) := by
  rw [actionProfile, map_sub, map_sub]
  simp only [sub_apply, LinearMap.sub_apply, evaluation_outputProfile_ordered,
    evaluation_inputProfile_ordered_left, evaluation_inputProfile_ordered_right,
    unaryAction, smul_sub, Finset.sum_sub_distrib]

/-- Actual bilinear target action, retaining the vector input as a linear slot. -/
def actionBilinear :
    (Vector (k := k) (d := d) →ₗ[k] Unary k (MvPolynomial (Fin d) k)) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k]
        (Vector (k := k) (d := d) →ₗ[k] Binary k (MvPolynomial (Fin d) k)) where
  toFun H := ((Gauge.unaryActionLinear (k := k) (V := MvPolynomial (Fin d) k)).comp H).flip
  map_add' H K := by ext C X f g; simp
  map_smul' c H := by ext C X f g; simp

@[simp] theorem actionBilinear_apply
    (H : Vector (k := k) (d := d) →ₗ[k] Unary k (MvPolynomial (Fin d) k))
    (C : Binary k (MvPolynomial (Fin d) k)) (X : Vector (k := k) (d := d)) :
    actionBilinear H C X = unaryAction (H X) C := rfl

/-- Literal whole-map identification with disjoint-group multilinear composition;
no diagonal restriction or polarization argument is used. -/
theorem evaluation_actionProfile_grouped (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    evaluation (binaryValue (k := k) (d := d)) (actionProfile w v) =
      LaurentModule.groupedBilinear actionBilinear (weightedVelocity w) (SymmetrizedGraphInsertion.binaryMap v) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  rw [evaluation_actionProfile_ordered, LaurentModule.groupedBilinear_apply]
  simp only [weightedVelocity, evaluation_apply, sum_apply, smul_apply,
    SymmetrizedGraphInsertion.binaryMap_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  simp only [actionBilinear_apply, independentBinary]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Scalar evaluation commutes with the actual finite background symmetrization. -/
theorem evaluation_symmetrizedMap (c : VectorGraph n 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) c =
      symmetrize (evaluation (binaryValue (k := k) (d := d)) c) := by
  simp only [evaluation_apply, symmetrizedBinaryValue, map_sum, map_smul]

/-- Whole symmetric multilinear target-action identity on independent background inputs. -/
theorem evaluation_actionProfile_symmetrized (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (actionProfile w v) =
      symmetrize (LaurentModule.groupedBilinear actionBilinear
        (weightedVelocity w) (SymmetrizedGraphInsertion.binaryMap v)) := by
  rw [evaluation_symmetrizedMap, evaluation_actionProfile_grouped]

/-- Equality of actual background counts transports a full mixed multilinear map. -/
def castMixedMap {N : ℕ} (h : n = N) (F : MixedMap k d n) : MixedMap k d N := h ▸ F

theorem evaluation_castProfile_ordered {N : ℕ} (h : n = N) (c : VectorGraph n 2 → k) :
    evaluation (binaryValue (k := k) (d := d)) (castProfile h c) =
      castMixedMap h (evaluation (binaryValue (k := k) (d := d)) c) := by subst N; rfl

theorem symmetrize_castMixedMap {N : ℕ} (h : n = N) (F : MixedMap k d n) :
    symmetrize (castMixedMap h F) = castMixedMap h (symmetrize F) := by subst N; rfl

/-- All degree splittings give the exact total ordered multilinear target map. -/
theorem evaluation_targetActionProfile_grouped (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k) :
    evaluation (binaryValue (k := k) (d := d)) (targetActionProfile N w v) =
      ∑ a : Fin (N + 1), castMixedMap (splitDegree N a)
        (LaurentModule.groupedBilinear actionBilinear (weightedVelocity (w a))
          (SymmetrizedGraphInsertion.binaryMap (v (N - a)))) := by
  rw [targetActionProfile, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [evaluation_castProfile_ordered, evaluation_actionProfile_grouped]

/-- The full averaged carrier identity is available before any Laurent or t-series evaluation. -/
theorem evaluation_targetActionProfile_symmetrized (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k) :
    evaluation (symmetrizedBinaryValue (k := k) (d := d)) (targetActionProfile N w v) =
      ∑ a : Fin (N + 1), castMixedMap (splitDegree N a)
        (symmetrize (LaurentModule.groupedBilinear actionBilinear (weightedVelocity (w a))
          (SymmetrizedGraphInsertion.binaryMap (v (N - a))))) := by
  rw [evaluation_symmetrizedMap, evaluation_targetActionProfile_grouped, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [symmetrize_castMixedMap]

end EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
