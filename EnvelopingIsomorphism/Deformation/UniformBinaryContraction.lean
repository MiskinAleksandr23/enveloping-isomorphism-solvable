import EnvelopingIsomorphism.Deformation.BinaryVertexContraction

/-! Slot normalization and actual curvature quotient extraction from a uniform
binary graph. Only target combinatorics are hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.UniformBinaryContraction
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits
open scoped Classical BigOperators
variable {n : ℕ} (i : Fin (n + 1)) (H : BinaryGraph (n + 2) 3)

abbrev Arity := Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i

def localTarget (e : Edge bivectorArity) : Vertex (n + 2) 3 :=
  H.target ⟨vertexSplitChild i e.1,e.2⟩

def UniqueInternalAt (a s : Fin 2) : Prop := ∀ e : Edge bivectorArity,
  vertexSplitCollapseVertex i (localTarget i H e) = Sum.inl i ↔ e = ⟨a,s⟩

def CoarseDistinct : Prop := ∀ (v : Fin (n + 1)) (_ : v ≠ i),
  Function.Injective (fun j : Fin 2 ↦ vertexSplitCollapseVertex i
    (H.target ⟨vertexSplitOldEmbedding i v,j⟩))

def ExitsDistinctAt (a s : Fin 2) : Prop := ∀ e f : Edge bivectorArity,
  e ≠ ⟨a,s⟩ → f ≠ ⟨a,s⟩ →
  vertexSplitCollapseVertex i (localTarget i H e) =
    vertexSplitCollapseVertex i (localTarget i H f) → e = f

/-- Exactly the permutation needed to move the actual internal arrow to slot zero. -/
def slotPermutation (a s : Fin 2) (v : Fin (n + 2)) : Equiv.Perm (Fin 2) :=
  if v = vertexSplitChild i a then Equiv.swap 0 s else Equiv.refl _

def normalized (a s : Fin 2) : BinaryGraph (n + 2) 3 :=
  H.permuteOutgoing (slotPermutation i a s)

def localEdgePermutation (a s : Fin 2) : Equiv.Perm (Edge bivectorArity) :=
  outgoingEdgePerm (fun c ↦ if c = a then Equiv.swap 0 s else Equiv.refl _)

theorem normalized_localTarget (a s : Fin 2) (e : Edge bivectorArity) :
    localTarget i (normalized i H a s) e = localTarget i H (localEdgePermutation a s e) := by
  rcases e with ⟨c,t⟩
  simp only [localTarget, normalized, Graph.permuteOutgoing, outgoingEdgePerm_apply,
    slotPermutation, (vertexSplitChild_injective i).eq_iff]
  rfl

theorem localEdgePermutation_internal_iff (a s : Fin 2) (e : Edge bivectorArity) :
    localEdgePermutation a s e = ⟨a,s⟩ ↔ e = ⟨a,0⟩ := by
  rcases e with ⟨c,t⟩
  fin_cases a <;> fin_cases s <;> fin_cases c <;> fin_cases t <;> decide

theorem normalized_outside (a s : Fin 2) (v : Fin (n + 1)) (hv : v ≠ i) (j : Fin 2) :
    (normalized i H a s).target ⟨vertexSplitOldEmbedding i v,j⟩ =
      H.target ⟨vertexSplitOldEmbedding i v,j⟩ := by
  simp [normalized, Graph.permuteOutgoing, slotPermutation, vertexSplitOld_ne_child i v hv a]

/-- Uniform graphs viewed in the native dependent split arities. -/
def splitGraph : Graph (vertexSplitArity (Arity i) bivectorArity i) 3 :=
  castGraph (vertexSplitArity_two i).symm H

theorem splitGraph_local (e : Edge bivectorArity) :
    (splitGraph i H).target (vertexSplitLocalEdge (Arity i) bivectorArity i e) = localTarget i H e := by
  let f := vertexSplitLocalEdge (Arity i) bivectorArity i e
  change (castGraph (vertexSplitArity_two i).symm H).target ⟨f.1,f.2⟩ = _
  rw [castGraph_target]
  congr 1
  apply Sigma.ext (vertexSplitLocalEdge_source (Arity i) bivectorArity i e)
  apply heq_of_eq
  apply Fin.ext
  exact vertexSplitLocalEdge_slot_val (Arity i) bivectorArity i e

theorem splitGraph_outside (e : VertexSplitOutsideEdge (Arity i) i) :
    (splitGraph i H).target (vertexSplitOutsideEdge (Arity i) bivectorArity i e) =
      H.target ⟨vertexSplitOldEmbedding i e.val.1,
        Fin.cast (by simp [Arity, Gauge.PlacedMixedGraphTaylorCoefficients.arities, e.property]) e.val.2⟩ := by
  let f := vertexSplitOutsideEdge (Arity i) bivectorArity i e
  change (castGraph (vertexSplitArity_two i).symm H).target ⟨f.1,f.2⟩ = _
  rw [castGraph_target]
  congr 1
  apply Sigma.ext (vertexSplitOutsideEdge_source (Arity i) bivectorArity i e)
  apply heq_of_eq
  apply Fin.ext
  exact vertexSplitOutsideEdge_slot_val (Arity i) bivectorArity i e

variable (a s : Fin 2) (hi : UniqueInternalAt i H a s)
    (hd : CoarseDistinct i H) (hx : ExitsDistinctAt i H a s)

include hi in
theorem normalized_unique : BinaryVertexContraction.UniqueInternal i
    (splitGraph i (normalized i H a s)) a := by
  intro e
  rw [splitGraph_local, normalized_localTarget, hi]
  exact localEdgePermutation_internal_iff a s e

include hd in
theorem normalized_coarse : (splitGraph i (normalized i H a s)).SplitCoarseDistinct i := by
  intro v hv j k h
  dsimp only at h
  rw [splitGraph_outside, splitGraph_outside, normalized_outside i H a s v hv,
    normalized_outside i H a s v hv] at h
  exact Fin.cast_injective _ (hd v hv h)

include hx in
theorem normalized_exits : BinaryVertexContraction.ExitsDistinct i
    (splitGraph i (normalized i H a s)) a := by
  intro e f he hf h
  rw [splitGraph_local, splitGraph_local, normalized_localTarget, normalized_localTarget] at h
  exact (localEdgePermutation a s).injective (hx _ _
    (fun hh ↦ he ((localEdgePermutation_internal_iff a s e).mp hh))
    (fun hh ↦ hf ((localEdgePermutation_internal_iff a s f).mp hh)) h)

def curvatureGraph : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i :=
  BinaryVertexContraction.quotient i (selectedArity i).symm (splitGraph i (normalized i H a s)) a
    (normalized_unique i H a s hi) (normalized_coarse i H a s hd) (normalized_exits i H a s hx)

def incomingChoices : SplitChoices i (curvatureGraph i H a s hi hd hx) :=
  BinaryVertexContraction.choices i (selectedArity i).symm (splitGraph i (normalized i H a s)) a
    (normalized_unique i H a s hi) (normalized_coarse i H a s hd) (normalized_exits i H a s hx)

private theorem castGraph_cancel {b k : ℕ} {q q' : Fin b → ℕ} (h : q = q') (G : Graph q' k) :
    castGraph h (castGraph h.symm G) = G := by
  cases h
  rfl

/-- The actual normalized binary graph is reconstructed from its genuine
curvature quotient and the incoming choices read from its original targets. -/
theorem reconstruct_normalized :
    (if a = 0 then uniformCurvatureForward i (curvatureGraph i H a s hi hd hx) 0
      (incomingChoices i H a s hi hd hx)
    else uniformCurvatureReverse i (curvatureGraph i H a s hi hd hx) 0
      (incomingChoices i H a s hi hd hx)) = normalized i H a s := by
  have hh := congrArg (castGraph (vertexSplitArity_two i))
    (BinaryVertexContraction.reconstruct i (selectedArity i).symm (splitGraph i (normalized i H a s)) a
      (normalized_unique i H a s hi) (normalized_coarse i H a s hd) (normalized_exits i H a s hx))
  have hc : castGraph (vertexSplitArity_two i) (splitGraph i (normalized i H a s)) = normalized i H a s := by
    exact castGraph_cancel (vertexSplitArity_two i) _
  rw [hc] at hh
  by_cases ha : a = 0 <;> simpa only [ha, if_pos, if_neg, if_true, if_false, BinaryVertexContraction.canonicalTemplate,
    uniformCurvatureForward, uniformCurvatureReverse, curvatureGraph, incomingChoices] using hh

/-- The source-slot normalization is an actual involution of graph targets. -/
theorem normalized_twice : normalized i (normalized i H a s) a s = H := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  by_cases hv : v = vertexSplitChild i a <;>
    simp [normalized, Graph.permuteOutgoing, slotPermutation, hv]

/-- Reconstruction retains the outgoing permutation needed for the original
ordered graph, including when its internal arrow occupied slot one. -/
theorem reconstruct_original :
    (if a = 0 then uniformCurvatureForward i (curvatureGraph i H a s hi hd hx) 0
      (incomingChoices i H a s hi hd hx)
    else uniformCurvatureReverse i (curvatureGraph i H a s hi hd hx) 0
      (incomingChoices i H a s hi hd hx)).permuteOutgoing (slotPermutation i a s) = H := by
  change normalized i _ a s = H
  rw [reconstruct_normalized, normalized_twice]

/-- The sole outgoing relabelling has the exact scalar sign determined by the
original internal-arrow slot. No orientation or factorial is absorbed. -/
theorem slotPermutation_sign {R : Type*} [CommRing R] :
    (∏ v : Fin (n + 2), permutationSign (R := R) (slotPermutation i a s v)) = (-1 : R) ^ s.val := by
  fin_cases s <;> simp [slotPermutation, permutationSign, apply_ite]

/-- The existing graph operator permutation law gives this exact normalization
sign for any alternating vertex tensors. -/
theorem normalized_cochainOperator {R : Type*} [CommRing R] {d : ℕ}
    (T : Fin (n + 2) → Tensor 2 d R) (hT : ∀ v, TensorPermutationLaw (T v)) :
    (normalized i H a s).cochainOperator T =
      ((-1 : R) ^ s.val) • H.cochainOperator T := by
  rw [normalized, Graph.cochainOperator_permuteOutgoing_sign _ _ _ hT, slotPermutation_sign]

/-- Extraction starts with an unselected unique actual internal edge. Its
source, original slot, quotient graph and incoming assignment are all found
inside the proof; reconstruction is an equality of the original graphs. -/
theorem exists_reconstruction
    (hunique : ∃! e : Edge bivectorArity,
      vertexSplitCollapseVertex i (localTarget i H e) = Sum.inl i)
    (hcoarse : CoarseDistinct i H)
    (hexit : ∀ e f : Edge bivectorArity,
      vertexSplitCollapseVertex i (localTarget i H e) ≠ Sum.inl i →
      vertexSplitCollapseVertex i (localTarget i H f) ≠ Sum.inl i →
      vertexSplitCollapseVertex i (localTarget i H e) =
        vertexSplitCollapseVertex i (localTarget i H f) → e = f) :
    ∃ (Θ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i) (a s : Fin 2)
      (χ : SplitChoices i Θ), UniqueInternalAt i H a s ∧
      (if a = 0 then uniformCurvatureForward i Θ 0 χ else uniformCurvatureReverse i Θ 0 χ).permuteOutgoing
        (slotPermutation i a s) = H := by
  obtain ⟨⟨a,s⟩,he,hu⟩ := hunique
  have hi : UniqueInternalAt i H a s := by
    intro e
    exact ⟨fun hh ↦ hu e hh, fun hh ↦ hh ▸ he⟩
  have hx : ExitsDistinctAt i H a s := by
    intro e f he hf hh
    exact hexit e f (fun h ↦ he ((hi e).mp h)) (fun h ↦ hf ((hi f).mp h)) hh
  exact ⟨curvatureGraph i H a s hi hcoarse hx, a, s,
    incomingChoices i H a s hi hcoarse hx, hi,
    reconstruct_original i H a s hi hcoarse hx⟩

end EnvelopingIsomorphism.Deformation.UniformBinaryContraction
