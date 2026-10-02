import EnvelopingIsomorphism.Deformation.GeneralGraphSlotRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphGraftFibres
import EnvelopingIsomorphism.Deformation.MixedGraphAveraging

/-! Independent block relabelling for actual mixed grafts. Every dependent
one-vector arity cast preserves the original outgoing slot numbers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphBlockRelabelling
open scoped BigOperators Classical
open KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphAveraging UniformBinaryGraphs
variable {n N a b m : ℕ}

private theorem cast_vertices {q q' : Fin n → ℕ} (h : q = q') (Γ : Graph q m) :
    (Graph.slotRelabelling_castProfile Γ h).vertices = Equiv.refl _ := by
  subst q'
  rfl

def transportRelabelling {q : Fin n → ℕ} (h : n = N) (e : Fin n ≃ Fin N) (Γ : Graph q m) :
    SlotRelabelling Γ (transportGraph h e Γ) := by
  subst N
  exact Graph.slotRelabelling_permuteProfile Γ e

theorem transportRelabelling_vertices {q : Fin n → ℕ} (h : n = N)
    (e : Fin n ≃ Fin N) (Γ : Graph q m) :
    (transportRelabelling h e Γ).vertices = e := by
  subst N
  rfl

def ofProfileRelabelling {q : Fin (n + 1) → ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) (Γ : Graph q m) :
    SlotRelabelling Γ (ofProfile i h Γ).graph := by
  subst q
  exact SlotRelabelling.refl Γ

theorem ofProfileRelabelling_vertices {q : Fin (n + 1) → ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) (Γ : Graph q m) :
    (ofProfileRelabelling i h Γ).vertices = Equiv.refl _ := by subst q; rfl

def outputCarrierRelabelling (i : Fin (a + 1))
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b => 2)) 2) :
    SlotRelabelling H (outputCarrier i H).graph :=
  (transportRelabelling (outputCount a b) (outputVertexEquiv a b) H).trans
    (ofProfileRelabelling _ (outputArity i) _)

def inputCarrierRelabelling (i : Fin (a + 1))
    (H : Graph (graftArity (fun _ : Fin b => 2) (vectorArity i)) 2) :
    SlotRelabelling H (inputCarrier i H).graph :=
  (transportRelabelling (inputCount a b) (inputVertexEquiv a b) H).trans
    (ofProfileRelabelling _ (inputArity i) _)

@[simp] theorem outputCarrierRelabelling_vertices (i : Fin (a + 1))
    (H : Graph (graftArity (vectorArity i) (fun _ : Fin b => 2)) 2) :
    (outputCarrierRelabelling i H).vertices = outputVertexEquiv a b := by
  simp only [outputCarrierRelabelling, SlotRelabelling.trans, transportRelabelling_vertices,
    ofProfileRelabelling_vertices]
  rfl

@[simp] theorem inputCarrierRelabelling_vertices (i : Fin (a + 1))
    (H : Graph (graftArity (fun _ : Fin b => 2) (vectorArity i)) 2) :
    (inputCarrierRelabelling i H).vertices = inputVertexEquiv a b := by
  simp only [inputCarrierRelabelling, SlotRelabelling.trans, transportRelabelling_vertices,
    ofProfileRelabelling_vertices]
  rfl

def vectorRelabelling (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m) :
    SlotRelabelling Γ.graph (internalGraphEquiv σ m Γ).graph :=
  Graph.slotRelabelling_oneExceptional Γ.vertex 1 Γ.graph σ

@[simp] theorem vectorRelabelling_vertices (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m) :
    (vectorRelabelling σ Γ).vertices = σ := by
  simp only [vectorRelabelling, Graph.slotRelabelling_oneExceptional,
    SlotRelabelling.trans, cast_vertices]
  rfl

def binaryRelabelling (σ : Equiv.Perm (Fin n)) (Γ : BinaryGraph n m) :
    SlotRelabelling Γ (Γ.permuteInternal σ) where
  vertices := σ
  edges := internalEdgePerm 2 σ
  source _ := rfl
  slot _ := rfl
  target := Γ.permuteInternal_target σ

@[simp] theorem binaryRelabelling_vertices (σ : Equiv.Perm (Fin n)) (Γ : BinaryGraph n m) :
    (binaryRelabelling σ Γ).vertices = σ := rfl

/-- A slot-preserving incidence map with the prescribed retained vertex is
exactly the already established mixed graph relabelling. -/
theorem vectorGraph_eq_internal {Γ Δ : VectorGraph n m}
    (σ : Equiv.Perm (Fin (n + 1))) (F : SlotRelabelling Γ.graph Δ.graph)
    (hv : F.vertices = σ) (hi : Δ.vertex = σ Γ.vertex) :
    Δ = internalGraphEquiv σ m Γ := by
  rcases Γ with ⟨i, Γ⟩
  rcases Δ with ⟨j, Δ⟩
  dsimp only [VectorGraph.vertex] at hi
  subst j
  apply congrArg (Sigma.mk (σ i))
  exact F.graph_eq (vectorRelabelling σ ⟨i, Γ⟩) (hv.trans (vectorRelabelling_vertices σ ⟨i, Γ⟩).symm)

def blockPerm (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin ((a + b) + 1)) :=
  (outputVertexEquiv a b).symm.trans
    ((SlotRelabelling.blockVertices σ τ).trans (outputVertexEquiv a b))

@[simp] theorem blockPerm_vector (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (v : Fin (a + 1)) : blockPerm σ τ (vectorEmbedding a b v) = vectorEmbedding a b (σ v) := by
  change blockPerm σ τ (outputVertexEquiv a b (Fin.castAdd b v)) = _
  simp only [blockPerm, Equiv.trans_apply, Equiv.symm_apply_apply, SlotRelabelling.blockVertices_outer]
  rfl

@[simp] theorem blockPerm_binary (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (v : Fin b) : blockPerm σ τ (binaryEmbedding a b v) = binaryEmbedding a b (τ v) := by
  change blockPerm σ τ (outputVertexEquiv a b (Fin.natAdd (a + 1) v)) = _
  simp only [blockPerm, Equiv.trans_apply, Equiv.symm_apply_apply, SlotRelabelling.blockVertices_inner]
  rfl

def outputDataRelabel (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (D : OutputIndex a b) : OutputIndex a b :=
  ⟨internalGraphEquiv σ 1 D.1, D.2.1.permuteInternal τ,
    SlotRelabelling.graftChoices (vectorRelabelling σ D.1) (binaryRelabelling τ D.2.1) 0 D.2.2⟩

/-- Relabelling the actual output graft commutes with both factor labels. -/
theorem outputGraft_relabel (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (D : OutputIndex a b) :
    outputGraft (outputDataRelabel σ τ D).1 (outputDataRelabel σ τ D).2.1
      (outputDataRelabel σ τ D).2.2 =
      internalGraphEquiv (blockPerm σ τ) 2 (outputGraft D.1 D.2.1 D.2.2) := by
  let F := (outputCarrierRelabelling D.1.vertex (D.1.graph.graft D.2.1 0 D.2.2)).symm.trans
    (((vectorRelabelling σ D.1).graft (binaryRelabelling τ D.2.1) 0 D.2.2).trans
      (outputCarrierRelabelling (σ D.1.vertex) _))
  apply vectorGraph_eq_internal (blockPerm σ τ) F
  · simp only [F, SlotRelabelling.trans, SlotRelabelling.symm, SlotRelabelling.graft,
      outputCarrierRelabelling_vertices, vectorRelabelling_vertices, binaryRelabelling_vertices]
    rfl
  · exact (blockPerm_vector σ τ D.1.vertex).symm


theorem input_blockPerm (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) :
    (inputVertexEquiv a b).symm.trans
      ((SlotRelabelling.blockVertices τ σ).trans (inputVertexEquiv a b)) = blockPerm σ τ := by
  apply Equiv.ext
  intro v
  obtain ⟨v, rfl⟩ := (inputVertexEquiv a b).surjective v
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  refine Fin.addCases (fun v => ?_) (fun v => ?_) v
  · simp only [SlotRelabelling.blockVertices_outer,
      inputVertexEquiv_outer, blockPerm_binary]
  · simp only [SlotRelabelling.blockVertices_inner,
      inputVertexEquiv_inner, blockPerm_vector]

def inputDataRelabel (r : Fin 2) (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (D : InputIndex a b r) : InputIndex a b r :=
  ⟨internalGraphEquiv σ 1 D.1, D.2.1.permuteInternal τ,
    SlotRelabelling.graftChoices (binaryRelabelling τ D.2.1) (vectorRelabelling σ D.1) r D.2.2⟩

/-- The input-block exchange preserves the same actual mixed block action. -/
theorem inputGraft_relabel (r : Fin 2) (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b))
    (D : InputIndex a b r) :
    inputGraft (inputDataRelabel r σ τ D).1 (inputDataRelabel r σ τ D).2.1 r
      (inputDataRelabel r σ τ D).2.2 =
      internalGraphEquiv (blockPerm σ τ) 2 (inputGraft D.1 D.2.1 r D.2.2) := by
  let F := (inputCarrierRelabelling D.1.vertex (D.2.1.graft D.1.graph r D.2.2)).symm.trans
    (((binaryRelabelling τ D.2.1).graft (vectorRelabelling σ D.1) r D.2.2).trans
      (inputCarrierRelabelling (σ D.1.vertex) _))
  apply vectorGraph_eq_internal (blockPerm σ τ) F
  · simp only [F, SlotRelabelling.trans, SlotRelabelling.symm, SlotRelabelling.graft,
      inputCarrierRelabelling_vertices, vectorRelabelling_vertices, binaryRelabelling_vertices]
    exact input_blockPerm σ τ
  · exact (blockPerm_vector σ τ D.1.vertex).symm

theorem outputDataRelabel_injective (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) :
    Function.Injective (outputDataRelabel σ τ) := by
  intro D E h
  apply outputGraft_injective
  apply (internalGraphEquiv (blockPerm σ τ) 2).injective
  rw [← outputGraft_relabel, ← outputGraft_relabel, h]

theorem inputDataRelabel_injective (r : Fin 2) (σ : Equiv.Perm (Fin (a + 1)))
    (τ : Equiv.Perm (Fin b)) : Function.Injective (inputDataRelabel r σ τ) := by
  intro D E h
  apply inputGraft_injective r
  apply (internalGraphEquiv (blockPerm σ τ) 2).injective
  rw [← inputGraft_relabel, ← inputGraft_relabel, h]

def outputDataEquiv (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm (OutputIndex a b) :=
  Equiv.ofBijective (outputDataRelabel σ τ)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨outputDataRelabel_injective σ τ, rfl⟩)

def inputDataEquiv (r : Fin 2) (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm (InputIndex a b r) :=
  Equiv.ofBijective (inputDataRelabel r σ τ)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inputDataRelabel_injective r σ τ, rfl⟩)

variable {k : Type*} [CommRing k]

private theorem pushforward_equiv {I A : Type*} [Fintype I]
    (f : I → A) (e : Equiv.Perm I) (g : Equiv.Perm A) (w : I → k)
    (hf : ∀ i, f (e i) = g (f i)) (hw : ∀ i, w (e i) = w i) (a : A) :
    GraphCoefficientProfiles.pushforward f w (g a) = GraphCoefficientProfiles.pushforward f w a := by
  unfold GraphCoefficientProfiles.pushforward
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hw, g.injective.eq_iff]

/-- Actual mixed output fibres are invariant under independent block labels
whenever the genuine factor weights have their proven internal covariance. -/
theorem outputProfile_blockPerm (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ Γ σ, w (internalGraphEquiv σ 1 Γ) = w Γ)
    (hv : ∀ Δ τ, v (Δ.permuteInternal τ) = v Δ)
    (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) (H : VectorGraph (a + b) 2) :
    outputProfile w v (internalGraphEquiv (blockPerm σ τ) 2 H) = outputProfile w v H := by
  apply pushforward_equiv _ (outputDataEquiv σ τ) (internalGraphEquiv (blockPerm σ τ) 2)
  · exact outputGraft_relabel σ τ
  · intro D
    change w (internalGraphEquiv σ 1 D.1) * v (D.2.1.permuteInternal τ) = w D.1 * v D.2.1
    rw [hw, hv]

theorem inputProfile_blockPerm (r : Fin 2) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ Γ σ, w (internalGraphEquiv σ 1 Γ) = w Γ)
    (hv : ∀ Δ τ, v (Δ.permuteInternal τ) = v Δ)
    (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) (H : VectorGraph (a + b) 2) :
    inputProfile r w v (internalGraphEquiv (blockPerm σ τ) 2 H) = inputProfile r w v H := by
  apply pushforward_equiv _ (inputDataEquiv r σ τ) (internalGraphEquiv (blockPerm σ τ) 2)
  · exact inputGraft_relabel r σ τ
  · intro D
    change w (internalGraphEquiv σ 1 D.1) * v (D.2.1.permuteInternal τ) = w D.1 * v D.2.1
    rw [hw, hv]

theorem actionProfile_blockPerm (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ Γ σ, w (internalGraphEquiv σ 1 Γ) = w Γ)
    (hv : ∀ Δ τ, v (Δ.permuteInternal τ) = v Δ)
    (σ : Equiv.Perm (Fin (a + 1))) (τ : Equiv.Perm (Fin b)) (H : VectorGraph (a + b) 2) :
    actionProfile w v (internalGraphEquiv (blockPerm σ τ) 2 H) = actionProfile w v H := by
  simp only [actionProfile, Pi.sub_apply, outputProfile_blockPerm w v hw hv,
    inputProfile_blockPerm _ w v hw hv]

theorem internalGraphEquiv_trans (σ τ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m) :
    internalGraphEquiv τ m (internalGraphEquiv σ m Γ) = internalGraphEquiv (σ.trans τ) m Γ := by
  apply vectorGraph_eq_internal (σ.trans τ)
    ((vectorRelabelling σ Γ).trans (vectorRelabelling τ (internalGraphEquiv σ m Γ)))
  · simp only [SlotRelabelling.trans, vectorRelabelling_vertices]
  · rfl

theorem internalGraphEquiv_refl (Γ : VectorGraph n m) : internalGraphEquiv (Equiv.refl _) m Γ = Γ := by
  symm
  apply vectorGraph_eq_internal (Equiv.refl _) (SlotRelabelling.refl Γ.graph) rfl rfl

theorem internalGraphEquiv_symm_apply (σ : Equiv.Perm (Fin (n + 1))) (Γ : VectorGraph n m) :
    (internalGraphEquiv σ m).symm Γ = internalGraphEquiv σ.symm m Γ := by
  apply (internalGraphEquiv σ m).injective
  rw [Equiv.apply_symm_apply, internalGraphEquiv_trans, Equiv.symm_trans_self, internalGraphEquiv_refl]

end EnvelopingIsomorphism.Deformation.MixedGraphBlockRelabelling
