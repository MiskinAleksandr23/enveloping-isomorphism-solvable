import EnvelopingIsomorphism.Deformation.GeneralGraphGraftOutgoing
import EnvelopingIsomorphism.Deformation.MixedGraphClusterSums

/-! Actual outgoing transport of mixed grafts, including the arity-one row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedGraphGraftOutgoing
open scoped Classical BigOperators
open KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphBlockRelabelling UniformBinaryGraphs
variable {a b n m : ℕ}

private theorem cast_perm_val {N q : ℕ} {p : Fin N → ℕ}
    (τ : (v : Fin N) → Equiv.Perm (Fin (p v))) {u w : Fin N}
    (e : u = w) (h₁ : q = p u) (h₂ : q = p w) (j : Fin q) :
    (τ u (Fin.cast h₁ j)).val = (τ w (Fin.cast h₂ j)).val := by
  subst w
  rfl

abbrev OutgoingFamily (n : ℕ) :=
  (i v : Fin (n+1)) → Equiv.Perm (Fin (vectorArity i v))

def outgoingEquiv (τ : OutgoingFamily n) (m : ℕ) : Equiv.Perm (VectorGraph n m) :=
  Equiv.sigmaCongrRight (fun i ↦ Graph.outgoingGraphEquiv _ m (τ i))

def outputOutgoing (i : Fin (a+1)) (τ : OutgoingFamily (a+b))
    (v : Fin ((a+1)+b)) : Equiv.Perm (Fin (graftArity (vectorArity i) (fun _ : Fin b ↦ 2) v)) :=
  (finCongr (show graftArity (vectorArity i) (fun _ : Fin b ↦ 2) v =
      vectorArity (vectorEmbedding a b i) (outputVertexEquiv a b v) by
    simpa only [Equiv.symm_apply_apply] using congrFun (outputArity (b := b) i)
      (outputVertexEquiv a b v))).symm.permCongr (τ _ (outputVertexEquiv a b v))

def inputOutgoing (i : Fin (a+1)) (τ : OutgoingFamily (a+b))
    (v : Fin (b+(a+1))) : Equiv.Perm (Fin (graftArity (fun _ : Fin b ↦ 2) (vectorArity i) v)) :=
  (finCongr (show graftArity (fun _ : Fin b ↦ 2) (vectorArity i) v =
      vectorArity (vectorEmbedding a b i) (inputVertexEquiv a b v) by
    simpa only [Equiv.symm_apply_apply] using congrFun (inputArity (b := b) i)
      (inputVertexEquiv a b v))).symm.permCongr (τ _ (inputVertexEquiv a b v))

theorem outputCarrier_outgoing (i : Fin (a+1)) (τ : OutgoingFamily (a+b))
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b ↦ 2)) 2) :
    outputCarrier i (H.permuteOutgoing (outputOutgoing i τ)) =
      outgoingEquiv τ 2 (outputCarrier i H) := by
  apply congrArg (Sigma.mk (vectorEmbedding a b i))
  let F := outputCarrierRelabelling i H
  have h : ∀ v, graftArity (vectorArity i) (fun _ : Fin b ↦ 2) v =
      vectorArity (vectorEmbedding a b i) (F.vertices v) := by
    intro v
    simpa only [F, outputCarrierRelabelling_vertices, Equiv.symm_apply_apply] using
      congrFun (outputArity (b := b) i) (outputVertexEquiv a b v)
  have hp : F.pullOutgoing h (τ (vectorEmbedding a b i)) = outputOutgoing i τ := by
    funext v
    apply Equiv.ext
    intro j
    apply Fin.ext
    simp only [SlotRelabelling.pullOutgoing, Equiv.permCongr_def, Equiv.trans_apply,
      finCongr_apply, finCongr_symm, Fin.val_cast, outputOutgoing]
    exact cast_perm_val _ (congrArg (fun e ↦ e v) (outputCarrierRelabelling_vertices i H)) _ _ j
  rw [← hp]
  apply (outputCarrierRelabelling i (H.permuteOutgoing _)).graph_eq
    (F.permuteOutgoing h (τ (vectorEmbedding a b i)))
  change (outputCarrierRelabelling i _).vertices = F.vertices
  exact (outputCarrierRelabelling_vertices _ _).trans (outputCarrierRelabelling_vertices i H).symm

theorem inputCarrier_outgoing (i : Fin (a+1)) (τ : OutgoingFamily (a+b))
    (H : Graph (graftArity (fun _ : Fin b ↦ 2) (vectorArity i)) 2) :
    inputCarrier i (H.permuteOutgoing (inputOutgoing i τ)) =
      outgoingEquiv τ 2 (inputCarrier i H) := by
  apply congrArg (Sigma.mk (vectorEmbedding a b i))
  let F := inputCarrierRelabelling i H
  have h : ∀ v, graftArity (fun _ : Fin b ↦ 2) (vectorArity i) v =
      vectorArity (vectorEmbedding a b i) (F.vertices v) := by
    intro v
    simpa only [F, inputCarrierRelabelling_vertices, Equiv.symm_apply_apply] using
      congrFun (inputArity (b := b) i) (inputVertexEquiv a b v)
  have hp : F.pullOutgoing h (τ (vectorEmbedding a b i)) = inputOutgoing i τ := by
    funext v
    apply Equiv.ext
    intro j
    apply Fin.ext
    simp only [SlotRelabelling.pullOutgoing, Equiv.permCongr_def, Equiv.trans_apply,
      finCongr_apply, finCongr_symm, Fin.val_cast, inputOutgoing]
    exact cast_perm_val _ (congrArg (fun e ↦ e v) (inputCarrierRelabelling_vertices i H)) _ _ j
  rw [← hp]
  apply (inputCarrierRelabelling i (H.permuteOutgoing _)).graph_eq
    (F.permuteOutgoing h (τ (vectorEmbedding a b i)))
  change (inputCarrierRelabelling i _).vertices = F.vertices
  exact (inputCarrierRelabelling_vertices _ _).trans (inputCarrierRelabelling_vertices i H).symm

def outputData (τ : OutgoingFamily (a+b)) (D : OutputIndex a b) : OutputIndex a b :=
  let α := outerOutgoing (outputOutgoing D.1.vertex τ)
  let β := innerOutgoing (outputOutgoing D.1.vertex τ)
  ⟨⟨D.1.vertex, D.1.graph.permuteOutgoing α⟩, D.2.1.permuteOutgoing β,
    D.1.graph.outgoingGraftChoices 0 α D.2.2⟩

def inputData (r : Fin 2) (τ : OutgoingFamily (a+b)) (D : InputIndex a b r) : InputIndex a b r :=
  let α := outerOutgoing (inputOutgoing D.1.vertex τ)
  let β := innerOutgoing (inputOutgoing D.1.vertex τ)
  ⟨⟨D.1.vertex, D.1.graph.permuteOutgoing β⟩, D.2.1.permuteOutgoing α,
    D.2.1.outgoingGraftChoices r α D.2.2⟩

theorem outputGraft_outgoing (τ : OutgoingFamily (a+b)) (D : OutputIndex a b) :
    outputGraft (outputData τ D).1 (outputData τ D).2.1 (outputData τ D).2.2 =
      outgoingEquiv τ 2 (outputGraft D.1 D.2.1 D.2.2) := by
  change outputCarrier D.1.vertex
    ((D.1.graph.permuteOutgoing _).graft (D.2.1.permuteOutgoing _) 0
      (D.1.graph.outgoingGraftChoices 0 _ D.2.2)) = _
  rw [← Graph.graft_permuteOutgoing, graftOutgoing_restrict]
  exact outputCarrier_outgoing _ τ _

theorem inputGraft_outgoing (r : Fin 2) (τ : OutgoingFamily (a+b)) (D : InputIndex a b r) :
    inputGraft (inputData r τ D).1 (inputData r τ D).2.1 r (inputData r τ D).2.2 =
      outgoingEquiv τ 2 (inputGraft D.1 D.2.1 r D.2.2) := by
  change inputCarrier D.1.vertex
    ((D.2.1.permuteOutgoing _).graft (D.1.graph.permuteOutgoing _) r
      (D.2.1.outgoingGraftChoices r _ D.2.2)) = _
  rw [← Graph.graft_permuteOutgoing, graftOutgoing_restrict]
  exact inputCarrier_outgoing _ τ _

def outputDataEquiv (τ : OutgoingFamily (a+b)) : Equiv.Perm (OutputIndex a b) :=
  Equiv.ofBijective (outputData τ) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro D E h
    apply outputGraft_injective
    apply (outgoingEquiv τ 2).injective
    rw [← outputGraft_outgoing, ← outputGraft_outgoing, h], rfl⟩)

def inputDataEquiv (r : Fin 2) (τ : OutgoingFamily (a+b)) : Equiv.Perm (InputIndex a b r) :=
  Equiv.ofBijective (inputData r τ) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro D E h
    apply inputGraft_injective r
    apply (outgoingEquiv τ 2).injective
    rw [← inputGraft_outgoing, ← inputGraft_outgoing, h], rfl⟩)

/-- The actual internal relabelling transports every dependent outgoing row;
the product of its row signs is unchanged. -/
theorem exists_internal_outgoing (σ : Equiv.Perm (Fin (n+1))) (H : VectorGraph n m)
    (α : (v : Fin (n+1)) → Equiv.Perm (Fin (vectorArity H.vertex v))) :
    ∃ β : (v : Fin (n+1)) → Equiv.Perm (Fin (vectorArity (σ H.vertex) v)),
      MixedGraphAveraging.internalGraphEquiv σ m ⟨H.vertex, H.graph.permuteOutgoing α⟩ =
        ⟨σ H.vertex, (MixedGraphAveraging.internalGraphEquiv σ m H).graph.permuteOutgoing β⟩ ∧
      (∏ v, permutationSign (R := ℝ) (β v)) = ∏ v, permutationSign (R := ℝ) (α v) := by
  let F := (vectorRelabelling σ H).symm
  have h : ∀ v, vectorArity (σ H.vertex) v = vectorArity H.vertex (F.vertices v) := by
    intro v
    have hv : F.vertices v = σ.symm v :=
      congrArg (fun e ↦ e.symm v) (vectorRelabelling_vertices σ H)
    rw [hv]
    simp only [vectorArity, Gauge.PlacedMixedGraphTaylorCoefficients.arities]
    simp only [σ.symm_apply_eq]
  refine ⟨F.pullOutgoing h α, ?_, F.pullOutgoing_sign h α⟩
  symm
  apply vectorGraph_eq_internal σ (F.permuteOutgoing h α).symm
  · change (vectorRelabelling σ H).vertices.symm.symm = σ
    exact vectorRelabelling_vertices σ H
  · rfl

end EnvelopingIsomorphism.Deformation.MixedGraphGraftOutgoing
