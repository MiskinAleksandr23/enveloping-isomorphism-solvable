import EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft
import EnvelopingIsomorphism.Deformation.MixedGraphProfileTensors
import EnvelopingIsomorphism.Deformation.GraphWeightedInsertion

/-! Actual one-vector carrier grafts and their scalar target-action profiles.
All input tensor slots and all incoming-edge assignments are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles

open KontsevichGraph.General MixedGraphProfileCarrier GraphCoefficientProfiles
open UniformBinaryGraphs SchoutenGraphContraction
open scoped BigOperators Classical

variable {a b m n N : ℕ}

/-- Relabel actual vertices through a finite equivalence, with only the proved size cast. -/
def transportGraph {q : Fin n → ℕ} (h : n = N) (e : Fin n ≃ Fin N) (Γ : Graph q m) :
    Graph (fun v => q (e.symm v)) m := by
  subst N
  exact Γ.permuteProfile e

def transportEdgeEquiv (q : Fin n → ℕ) (e : Fin n ≃ Fin N) :
    Edge q ≃ Edge (fun v => q (e.symm v)) :=
  (Equiv.sigmaCongrLeft (β := fun v => Fin (q v)) e.symm).symm

theorem transportGraph_target {q : Fin n → ℕ} (h : n = N) (e : Fin n ≃ Fin N)
    (Γ : Graph q m) (x : Edge q) :
    (transportGraph h e Γ).target (transportEdgeEquiv q e x) = Sum.map e id (Γ.target x) := by
  subst N
  exact Γ.permuteProfile_target e x

theorem outputCount (a b : ℕ) : (a + 1) + b = (a + b) + 1 := by omega

theorem inputCount (a b : ℕ) : b + (a + 1) = (a + b) + 1 := by omega

/-- The common target order places all original vector-graph vertices first. -/
def outputVertexEquiv (a b : ℕ) : Fin ((a + 1) + b) ≃ Fin ((a + b) + 1) :=
  finCongr (outputCount a b)

/-- Input grafts use the actual block exchange to reach the same target label convention. -/
def inputVertexEquiv (a b : ℕ) : Fin (b + (a + 1)) ≃ Fin ((a + b) + 1) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin b) (Fin (a + 1))).trans
    (finSumFinEquiv.trans (outputVertexEquiv a b)))

def vectorEmbedding (a b : ℕ) : Fin (a + 1) ↪ Fin ((a + b) + 1) :=
  (Fin.castAddEmb b).trans (outputVertexEquiv a b).toEmbedding

def binaryEmbedding (a b : ℕ) : Fin b ↪ Fin ((a + b) + 1) :=
  (Fin.natAddEmb (a + 1)).trans (outputVertexEquiv a b).toEmbedding

@[simp] theorem outputVertexEquiv_outer (v : Fin (a + 1)) :
    outputVertexEquiv a b (Fin.castAdd b v) = vectorEmbedding a b v := rfl

@[simp] theorem outputVertexEquiv_inner (v : Fin b) :
    outputVertexEquiv a b (Fin.natAdd (a + 1) v) = binaryEmbedding a b v := rfl

@[simp] theorem inputVertexEquiv_outer (v : Fin b) :
    inputVertexEquiv a b (Fin.castAdd (a + 1) v) = binaryEmbedding a b v := by
  change inputVertexEquiv a b (finSumFinEquiv (Sum.inl v)) = _
  simp only [inputVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem inputVertexEquiv_inner (v : Fin (a + 1)) :
    inputVertexEquiv a b (Fin.natAdd b v) = vectorEmbedding a b v := by
  change inputVertexEquiv a b (finSumFinEquiv (Sum.inr v)) = _
  simp only [inputVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem binaryEmbedding_ne_vector (v : Fin b) (i : Fin (a + 1)) :
    binaryEmbedding a b v ≠ vectorEmbedding a b i := by
  intro h
  have he := (outputVertexEquiv a b).injective h
  have hv := congrArg Fin.val he
  change (a + 1) + v.val = i.val at hv
  omega

abbrev vectorArity (i : Fin (a + 1)) := Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i

theorem outputArity (i : Fin (a + 1)) :
    (fun v => graftArity (vectorArity i) (fun _ : Fin b => 2) ((outputVertexEquiv a b).symm v)) =
      vectorArity (vectorEmbedding a b i) := by
  funext v
  obtain ⟨v, rfl⟩ := (outputVertexEquiv a b).surjective v
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · simp [vectorArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities]
  · simp [vectorArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, binaryEmbedding_ne_vector]

theorem inputArity (i : Fin (a + 1)) :
    (fun v => graftArity (fun _ : Fin b => 2) (vectorArity i) ((inputVertexEquiv a b).symm v)) =
      vectorArity (vectorEmbedding a b i) := by
  funext v
  obtain ⟨v, rfl⟩ := (inputVertexEquiv a b).surjective v
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · simp [vectorArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, binaryEmbedding_ne_vector]
  · simp [vectorArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities]

abbrev OutputChoices (Γ : VectorGraph a 1) := Γ.graph.GraftChoices (b := b) (l := 1) 0
abbrev InputChoices (Δ : BinaryGraph b 2) (r : Fin 2) := Δ.GraftChoices (b := a + 1) (l := 0) r

/-- Unary output graft in the genuine common one-vector carrier. -/
def outputGraft (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2) (χ : OutputChoices (b := b) Γ) :
    VectorGraph (a + b) 2 :=
  ofProfile (vectorEmbedding a b Γ.vertex) (outputArity Γ.vertex)
    (transportGraph (outputCount a b) (outputVertexEquiv a b) (Γ.graph.graft Δ 0 χ))

/-- A binary input graft, with the actual block exchange retaining common labels. -/
def inputGraft (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2) (r : Fin 2)
    (χ : InputChoices (a := a) Δ r) : VectorGraph (a + b) 2 :=
  ofProfile (vectorEmbedding a b Γ.vertex) (inputArity Γ.vertex)
    (transportGraph (inputCount a b) (inputVertexEquiv a b) (Δ.graft Γ.graph r χ))

section Tensors

variable {k : Type*} [Field k] {d : ℕ}

theorem cochainOperator_transportGraph {q : Fin n → ℕ} (h : n = N) (e : Fin n ≃ Fin N)
    (Γ : Graph q m) (T : (v : Fin n) → Tensor (q v) d k) :
    (transportGraph h e Γ).cochainOperator (fun v => T (e.symm v)) = Γ.cochainOperator T := by
  subst N
  exact Γ.cochainOperator_permuteProfile e T

private theorem castTensors_heq {q q' : Fin n → ℕ} (h : q = q')
    (T : (v : Fin n) → Tensor (q v) d k) (v : Fin n) :
    HEq (castTensors h T v) (T v) := by subst q'; rfl

private theorem tensorDomain_heq {r s : ℕ} (h : r = s) (T : Tensor r d k) :
    HEq (fun lab : Fin s → Fin d => T (fun j => lab (Fin.cast h j))) T := by
  subst s
  rfl

private theorem graftTensors_outer_heq {r s : ℕ} (q : Fin r → ℕ) (p : Fin s → ℕ)
    (T : (v : Fin r) → Tensor (q v) d k) (U : (v : Fin s) → Tensor (p v) d k) (v : Fin r) :
    HEq (graftTensors q p T U (Fin.castAdd s v)) (T v) := by
  have he : graftTensors q p T U (Fin.castAdd s v) =
      fun lab => T v (fun j => lab (Fin.cast (graftArity_outer q p v).symm j)) := by
    funext lab
    exact graftTensors_outer q p T U v lab
  rw [he]
  exact tensorDomain_heq _ _

private theorem graftTensors_inner_heq {r s : ℕ} (q : Fin r → ℕ) (p : Fin s → ℕ)
    (T : (v : Fin r) → Tensor (q v) d k) (U : (v : Fin s) → Tensor (p v) d k) (v : Fin s) :
    HEq (graftTensors q p T U (Fin.natAdd r v)) (U v) := by
  have he : graftTensors q p T U (Fin.natAdd r v) =
      fun lab => U v (fun j => lab (Fin.cast (graftArity_inner q p v).symm j)) := by
    funext lab
    exact graftTensors_inner q p T U v lab
  rw [he]
  exact tensorDomain_heq _ _

def outputTensors (i : Fin (a + 1))
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :=
  castTensors (outputArity (b := b) i) (fun v =>
    graftTensors (vectorArity i) (fun _ : Fin b => 2)
      (rawTensors i (B ∘ vectorEmbedding a b) X)
      (fun u => rawTensor (B (binaryEmbedding a b u))) ((outputVertexEquiv a b).symm v))

def inputTensors (i : Fin (a + 1))
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :=
  castTensors (inputArity (b := b) i) (fun v =>
    graftTensors (fun _ : Fin b => 2) (vectorArity i)
      (fun u => rawTensor (B (binaryEmbedding a b u)))
      (rawTensors i (B ∘ vectorEmbedding a b) X) ((inputVertexEquiv a b).symm v))

/-- Every independently chosen bivector is read at its actual image label. -/
theorem outputTensors_independent (i : Fin (a + 1))
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    outputTensors i B X = rawTensors (vectorEmbedding a b i) B X := by
  funext v
  apply eq_of_heq
  refine (castTensors_heq (outputArity i) _ v).trans ?_
  obtain ⟨v, rfl⟩ := (outputVertexEquiv a b).surjective v
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · refine (graftTensors_outer_heq _ _ _ _ u).trans ?_
    by_cases hu : u = i
    · subst u
      exact (rawTensors_root_heq i _ X).trans (rawTensors_root_heq (vectorEmbedding a b i) B X).symm
    · exact (rawTensors_other_heq i u hu _ X).trans
        (rawTensors_other_heq (vectorEmbedding a b i) (vectorEmbedding a b u)
          ((vectorEmbedding a b).injective.ne hu) B X).symm
  · exact (graftTensors_inner_heq _ _ _ _ u).trans
      (rawTensors_other_heq (vectorEmbedding a b i) (binaryEmbedding a b u)
        (binaryEmbedding_ne_vector u i) B X).symm

/-- The swapped input-graft blocks recover exactly the same final independent tensor family. -/
theorem inputTensors_independent (i : Fin (a + 1))
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    inputTensors i B X = rawTensors (vectorEmbedding a b i) B X := by
  funext v
  apply eq_of_heq
  refine (castTensors_heq (inputArity i) _ v).trans ?_
  obtain ⟨v, rfl⟩ := (inputVertexEquiv a b).surjective v
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · rw [inputVertexEquiv_outer]
    exact (graftTensors_outer_heq _ _ _ _ u).trans
      (rawTensors_other_heq (vectorEmbedding a b i) (binaryEmbedding a b u)
        (binaryEmbedding_ne_vector u i) B X).symm
  · rw [inputVertexEquiv_inner]
    refine (graftTensors_inner_heq _ _ _ _ u).trans ?_
    by_cases hu : u = i
    · subst u
      exact (rawTensors_root_heq i _ X).trans (rawTensors_root_heq (vectorEmbedding a b i) B X).symm
    · exact (rawTensors_other_heq i u hu _ X).trans
        (rawTensors_other_heq (vectorEmbedding a b i) (vectorEmbedding a b u)
          ((vectorEmbedding a b).injective.ne hu) B X).symm

/-- Actual output carrier evaluation is exactly the original native graft evaluation. -/
theorem rawValue_outputGraft (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (χ : OutputChoices (b := b) Γ)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawValue (outputGraft Γ Δ χ) B X =
      (Γ.graph.graft Δ 0 χ).cochainOperator
        (graftTensors (vectorArity Γ.vertex) (fun _ : Fin b => 2)
          (rawTensors Γ.vertex (B ∘ vectorEmbedding a b) X)
          (fun u => rawTensor (B (binaryEmbedding a b u)))) := by
  change (castGraph (outputArity Γ.vertex) _).cochainOperator
    (rawTensors (vectorEmbedding a b Γ.vertex) B X) = _
  rw [← outputTensors_independent Γ.vertex B X]
  exact (cochainOperator_castGraph (outputArity Γ.vertex) _ _).trans
    (cochainOperator_transportGraph (outputCount a b) (outputVertexEquiv a b) _ _)

/-- The actual block relabelling of an input graft introduces no assumed operator identity. -/
theorem rawValue_inputGraft (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2) (r : Fin 2)
    (χ : InputChoices (a := a) Δ r)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    rawValue (inputGraft Γ Δ r χ) B X =
      (Δ.graft Γ.graph r χ).cochainOperator
        (graftTensors (fun _ : Fin b => 2) (vectorArity Γ.vertex)
          (fun u => rawTensor (B (binaryEmbedding a b u)))
          (rawTensors Γ.vertex (B ∘ vectorEmbedding a b) X)) := by
  change (castGraph (inputArity Γ.vertex) _).cochainOperator
    (rawTensors (vectorEmbedding a b Γ.vertex) B X) = _
  rw [← inputTensors_independent Γ.vertex B X]
  exact (cochainOperator_castGraph (inputArity Γ.vertex) _ _).trans
    (cochainOperator_transportGraph (inputCount a b) (inputVertexEquiv a b) _ _)

def rawUnary (Γ : VectorGraph a 1) (B : Fin (a + 1) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) : Unary k (MvPolynomial (Fin d) k) :=
  cochainOneEquiv k _ (rawValue Γ B X)

def independentBinary (Δ : BinaryGraph b 2) (B : Fin b → Bivector (k := k) (d := d)) :
    Binary k (MvPolynomial (Fin d) k) := cochainTwoEquiv k _ (UniformBinaryGraphs.operator Δ B)

theorem sum_outputGraft_raw (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    cochainTwoEquiv k _ (∑ χ : OutputChoices (b := b) Γ, rawValue (outputGraft Γ Δ χ) B X) =
      (independentBinary Δ (B ∘ binaryEmbedding a b)).compr₂
        (rawUnary Γ (B ∘ vectorEmbedding a b) X) := by
  simp only [rawValue_outputGraft]
  exact Graph.graft_unary_output Γ.graph Δ _ _

theorem sum_inputGraft_raw_left (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    cochainTwoEquiv k _ (∑ χ : InputChoices (a := a) Δ 0, rawValue (inputGraft Γ Δ 0 χ) B X) =
      (independentBinary Δ (B ∘ binaryEmbedding a b)).comp
        (rawUnary Γ (B ∘ vectorEmbedding a b) X) := by
  simp only [rawValue_inputGraft]
  exact Graph.graft_unary_left Δ Γ.graph _ _

theorem sum_inputGraft_raw_right (Γ : VectorGraph a 1) (Δ : BinaryGraph b 2)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    cochainTwoEquiv k _ (∑ χ : InputChoices (a := a) Δ 1, rawValue (inputGraft Γ Δ 1 χ) B X) =
      (independentBinary Δ (B ∘ binaryEmbedding a b)).compl₂
        (rawUnary Γ (B ∘ vectorEmbedding a b) X) := by
  simp only [rawValue_inputGraft]
  exact Graph.graft_unary_right Δ Γ.graph _ _

end Tensors

section Profiles
variable {k : Type*} [CommRing k]

abbrev OutputIndex (a b : ℕ) :=
  (Γ : VectorGraph a 1) × (_ : BinaryGraph b 2) × OutputChoices (b := b) Γ
abbrev InputIndex (a b : ℕ) (r : Fin 2) :=
  (_ : VectorGraph a 1) × (Δ : BinaryGraph b 2) × InputChoices (a := a) Δ r

/-- Scalar weights of all actual output grafts, retaining every collision multiplicity. -/
def outputProfile (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) : VectorGraph (a + b) 2 → k :=
  pushforward (fun i : OutputIndex a b => outputGraft i.1 i.2.1 i.2.2) (fun i => w i.1 * v i.2.1)

/-- Scalar weights of all actual input grafts at the indicated binary external slot. -/
def inputProfile (r : Fin 2) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) : VectorGraph (a + b) 2 → k :=
  pushforward (fun i : InputIndex a b r => inputGraft i.1 i.2.1 r i.2.2) (fun i => w i.1 * v i.2.1)

def actionProfile (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) : VectorGraph (a + b) 2 → k :=
  outputProfile w v - inputProfile 0 w v - inputProfile 1 w v

theorem outputProfile_apply (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (H : VectorGraph (a + b) 2) :
    outputProfile w v H = ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2,
      ∑ χ : OutputChoices (b := b) Γ, if outputGraft Γ Δ χ = H then w Γ * v Δ else 0 := by
  rw [outputProfile, pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases h : outputGraft Γ Δ χ = H <;> simp [h]

theorem inputProfile_apply (r : Fin 2) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (H : VectorGraph (a + b) 2) :
    inputProfile r w v H = ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2,
      ∑ χ : InputChoices (a := a) Δ r, if inputGraft Γ Δ r χ = H then w Γ * v Δ else 0 := by
  rw [inputProfile, pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases h : inputGraft Γ Δ r χ = H <;> simp [h]

/-- Only equality of total bivector counts transports the scalar table. -/
def castProfile (h : n = N) (w : VectorGraph n 2 → k) : VectorGraph N 2 → k := h ▸ w

omit [CommRing k] in
theorem castProfile_apply (h : n = N) (w : VectorGraph n 2 → k) (H : VectorGraph N 2) :
    castProfile h w H = w (MixedGraphProfileCarrier.castVertices h.symm H) := by subst N; rfl

theorem splitDegree (N : ℕ) (a : Fin (N + 1)) : (a : ℕ) + (N - a) = N := by omega

/-- Actual unary-output minus both binary-input scalar profiles at total degree N.
The zero-bivector binary graph and every vector placement are included. -/
def targetActionProfile (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k) : VectorGraph N 2 → k :=
  ∑ a : Fin (N + 1), castProfile (splitDegree N a) (actionProfile (w a) (v (N - a)))

end Profiles

section WeightedEvaluation
variable {k : Type*} [Field k] {d : ℕ}

def rawBinaryValue (Γ : VectorGraph n 2) (B : Fin (n + 1) → Bivector (k := k) (d := d))
    (X : Vector (k := k) (d := d)) : Binary k (MvPolynomial (Fin d) k) :=
  cochainTwoEquiv k _ (rawValue Γ B X)

def weightedRawUnary (w : VectorGraph a 1 → k)
    (B : Fin (a + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    Unary k (MvPolynomial (Fin d) k) := ∑ Γ, w Γ • rawUnary Γ B X

def weightedIndependentBinary (v : BinaryGraph b 2 → k) (B : Fin b → Bivector (k := k) (d := d)) :
    Binary k (MvPolynomial (Fin d) k) := ∑ Δ, v Δ • independentBinary Δ B

theorem evaluation_outputProfile_raw_sum (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (outputProfile w v) =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        (independentBinary Δ (B ∘ binaryEmbedding a b)).compr₂ (rawUnary Γ (B ∘ vectorEmbedding a b) X) := by
  rw [outputProfile, evaluation_pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  dsimp only
  rw [← Finset.smul_sum]
  congr 1
  change (∑ χ : OutputChoices (b := b) Γ, cochainTwoEquiv k _ (rawValue (outputGraft Γ Δ χ) B X)) = _
  rw [← map_sum]
  exact sum_outputGraft_raw Γ Δ B X

theorem evaluation_inputProfile_raw_sum (r : Fin 2) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (inputProfile r w v) =
      ∑ Γ : VectorGraph a 1, ∑ Δ : BinaryGraph b 2, (w Γ * v Δ) •
        cochainTwoEquiv k _ (∑ χ : InputChoices (a := a) Δ r, rawValue (inputGraft Γ Δ r χ) B X) := by
  rw [inputProfile, evaluation_pushforward, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  dsimp only
  rw [← Finset.smul_sum, map_sum]
  rfl

/-- Pure scalar output-graft weights evaluate to the actual independent weighted postcomposition. -/
theorem evaluation_outputProfile_raw (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (outputProfile w v) =
      (weightedIndependentBinary v (B ∘ binaryEmbedding a b)).compr₂
        (weightedRawUnary w (B ∘ vectorEmbedding a b) X) := by
  rw [evaluation_outputProfile_raw_sum]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedIndependentBinary, weightedRawUnary, map_sum, map_smul,
    LinearMap.compr₂_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem evaluation_inputProfile_raw_left (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (inputProfile 0 w v) =
      (weightedIndependentBinary v (B ∘ binaryEmbedding a b)).comp
        (weightedRawUnary w (B ∘ vectorEmbedding a b) X) := by
  rw [evaluation_inputProfile_raw_sum]
  simp only [sum_inputGraft_raw_left]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedIndependentBinary, weightedRawUnary, map_sum, map_smul,
    LinearMap.comp_apply, Finset.smul_sum, smul_smul]

theorem evaluation_inputProfile_raw_right (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (inputProfile 1 w v) =
      (weightedIndependentBinary v (B ∘ binaryEmbedding a b)).compl₂
        (weightedRawUnary w (B ∘ vectorEmbedding a b) X) := by
  rw [evaluation_inputProfile_raw_sum]
  simp only [sum_inputGraft_raw_right]
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  simp [weightedIndependentBinary, weightedRawUnary, map_sum, map_smul,
    LinearMap.compl₂_apply, Finset.smul_sum, smul_smul]

/-- Actual unary action is the evaluation of output minus both input scalar profiles. -/
theorem evaluation_actionProfile_raw (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (B : Fin ((a + b) + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (actionProfile w v) =
      unaryAction (weightedRawUnary w (B ∘ vectorEmbedding a b) X)
        (weightedIndependentBinary v (B ∘ binaryEmbedding a b)) := by
  rw [actionProfile, map_sub, map_sub, evaluation_outputProfile_raw,
    evaluation_inputProfile_raw_left, evaluation_inputProfile_raw_right]
  rfl

def castVertexEquiv (h : n = N) : Fin (n + 1) ≃ Fin (N + 1) := finCongr (congrArg (fun n => n + 1) h)

theorem evaluation_castProfile_raw (h : n = N) (w : VectorGraph n 2 → k)
    (B : Fin (N + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (castProfile h w) =
      evaluation (fun H => rawBinaryValue H (B ∘ castVertexEquiv h) X) w := by subst N; rfl

/-- Every total-degree split is evaluated with its actual label embeddings and original scalar weights. -/
theorem evaluation_targetActionProfile_raw (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k)
    (B : Fin (N + 1) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H B X) (targetActionProfile N w v) =
      ∑ a : Fin (N + 1), unaryAction
        (weightedRawUnary (w a) ((B ∘ castVertexEquiv (splitDegree N a)) ∘ vectorEmbedding a (N - a)) X)
        (weightedIndependentBinary (v (N - a))
          ((B ∘ castVertexEquiv (splitDegree N a)) ∘ binaryEmbedding a (N - a))) := by
  rw [targetActionProfile, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [evaluation_castProfile_raw, evaluation_actionProfile_raw]

/-- On repeated backgrounds, the raw carrier evaluation is exactly its existing
actual weighted velocity family, including every distinguished vertex position. -/
theorem weightedRawUnary_diagonal (w : VectorGraph a 1 → k)
    (π : Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    weightedRawUnary w (fun _ => π) X = weightedVelocity w (fun _ => π) X := by
  simp only [weightedRawUnary, weightedVelocity, evaluation_apply, sum_apply, smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  congr 1
  have h := operator_eq_rawValue Γ (fun _ => π) X
  exact congrArg (cochainOneEquiv k (MvPolynomial (Fin d) k)) h.symm

theorem weightedIndependentBinary_diagonal (v : BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) :
    weightedIndependentBinary v (fun _ => π) = GraphWeightedInsertion.weightedBinary v π := rfl

/-- The total scalar table yields the genuine homogeneous weighted unary action on
repeated backgrounds, without any scalar graph relation as a premise. -/
theorem evaluation_targetActionProfile_diagonal (N : ℕ)
    (w : (a : ℕ) → VectorGraph a 1 → k) (v : (b : ℕ) → BinaryGraph b 2 → k)
    (π : Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    evaluation (fun H => rawBinaryValue H (fun _ => π) X) (targetActionProfile N w v) =
      ∑ a : Fin (N + 1), unaryAction (weightedVelocity (w a) (fun _ => π) X)
        (GraphWeightedInsertion.weightedBinary (v (N - a)) π) := by
  rw [evaluation_targetActionProfile_raw]
  apply Finset.sum_congr rfl
  intro a ha
  change unaryAction (weightedRawUnary (w a) (fun _ => π) X)
      (weightedIndependentBinary (v (N - a)) (fun _ => π)) = _
  rw [weightedRawUnary_diagonal, weightedIndependentBinary_diagonal]

end WeightedEvaluation

end EnvelopingIsomorphism.Deformation.MixedGraphTargetProfiles
