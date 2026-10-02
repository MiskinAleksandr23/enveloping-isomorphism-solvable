import EnvelopingIsomorphism.Deformation.GeneralGraphSplitSlotRelabelling
import EnvelopingIsomorphism.Deformation.GraphCurvatureOutgoingAverage
import EnvelopingIsomorphism.Deformation.BinaryAverageLinearity
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Internal relabelling covariance of the actual main curvature quotient
fibres. Both the root placement and the order of its two children may move. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureInternalRelabelling
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits UniformCurvatureTargets UniformCurvatureOutgoing
open BinaryVertexContraction GraphCurvatureProfiles GraphCurvatureOutgoingAverage
open BinaryGraphAveraging GraphCoefficientProfiles
open scoped Classical BigOperators
variable {n : ℕ}

private theorem castProfile_vertices {b m : ℕ} {q q' : Fin b → ℕ} (h : q = q') (Γ : Graph q m) :
    (slotRelabelling_castProfile Γ h).vertices = Equiv.refl _ := by
  cases h
  rfl

def quotientRelabelling (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (Γ : CurvatureGraph i) :=
  slotRelabelling_oneExceptional i 3 Γ σ

@[simp] theorem quotientRelabelling_vertices (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (Γ : CurvatureGraph i) :
    (quotientRelabelling i σ Γ).vertices = σ := by
  simp only [quotientRelabelling, slotRelabelling_oneExceptional, SlotRelabelling.trans, castProfile_vertices]
  rfl

def quotientEquiv (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    CurvatureGraph i ≃ CurvatureGraph (σ i) := oneExceptionalGraphEquiv 3 i σ 3

/-- Incoming edges and child choices are reindexed by their actual finite equivalences. -/
def dataEquiv (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) (δ : Equiv.Perm (Fin 2)) :
    CurvatureSplitData i ≃ CurvatureSplitData (σ i) :=
  Equiv.sigmaCongr (quotientEquiv i σ) (fun Γ ↦
    Equiv.arrowCongr (SlotRelabelling.splitIncomingEquiv i (σ i) (quotientRelabelling i σ Γ)
      (by rw [quotientRelabelling_vertices])) δ)

/-- Exchanging the two children exchanges forward/reverse templates while
preserving every outgoing slot and every external leg label. -/
def templateRelabelling (a : Fin 2) (δ : Equiv.Perm (Fin 2)) :
    SlotRelabelling (canonicalTemplate a) (canonicalTemplate (δ a)) where
  vertices := δ
  edges := internalEdgePerm 2 δ
  source _ := rfl
  slot _ := rfl
  target e := by
    have h : ∀ (δ : Equiv.Perm (Fin 2)) (a v s : Fin 2),
        (canonicalTemplate (δ a)).target ⟨δ v,s⟩ =
          Sum.map δ id ((canonicalTemplate a).target ⟨v,s⟩) := by decide
    exact h δ a e.1 e.2

private def castRelabelling {b m : ℕ} {q q' : Fin b → ℕ} (h : q = q') (Γ : Graph q m) :
    SlotRelabelling Γ (castGraph h Γ) := by
  cases h
  exact SlotRelabelling.refl Γ

@[simp] private theorem castRelabelling_vertices {b m : ℕ} {q q' : Fin b → ℕ}
    (h : q = q') (Γ : Graph q m) : (castRelabelling h Γ).vertices = Equiv.refl _ := by
  cases h
  rfl

private def binaryRelabelling {b m : ℕ} (H : BinaryGraph b m) (σ : Equiv.Perm (Fin b)) :
    SlotRelabelling H (H.permuteInternal σ) where
  vertices := σ
  edges := internalEdgePerm 2 σ
  source _ := rfl
  slot _ := rfl
  target e := H.permuteInternal_target σ e

/-- The native split theorem gives equality of the resulting uniform graphs,
including the exact internal permutation of the expanded child pair. -/
theorem canonicalDataGraph_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (δ : Equiv.Perm (Fin 2)) (a : Fin 2) (D : CurvatureSplitData i) :
    canonicalDataGraph (σ i) (δ a) (dataEquiv i σ δ D) =
      (canonicalDataGraph i a D).permuteInternal
        (SlotRelabelling.splitVertices i (σ i) σ rfl δ) := by
  let F := quotientRelabelling i σ D.1
  let G := templateRelabelling a δ
  have hF : F.vertices i = σ i := by rw [quotientRelabelling_vertices]
  let FS := SlotRelabelling.vertexSplit i (σ i) F G
    (selectedArity i).symm (selectedArity (σ i)).symm hF D.2
  let FU := ((castRelabelling (vertexSplitArity_two i) _).symm.trans FS).trans
    (castRelabelling (vertexSplitArity_two (σ i)) _)
  have hv : FU.vertices = SlotRelabelling.splitVertices i (σ i) σ rfl δ := by
    simp only [FU, SlotRelabelling.trans, SlotRelabelling.symm, castRelabelling_vertices]
    change (Equiv.refl _).symm.trans
      ((SlotRelabelling.splitVertices i (σ i) F.vertices hF G.vertices).trans (Equiv.refl _)) = _
    simp only [Equiv.refl_symm, Equiv.refl_trans, Equiv.trans_refl]
    simp only [F, quotientRelabelling_vertices, G, templateRelabelling]
  have hh := FU.graph_eq (binaryRelabelling (canonicalDataGraph i a D)
    (SlotRelabelling.splitVertices i (σ i) σ rfl δ)) hv
  exact hh

/-- The actual one-exceptional geometric quotient weight is internally invariant. -/
theorem canonicalWeight_quotientEquiv (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (Γ : CurvatureGraph i) : canonicalWeight (k := ℝ) (σ i) (quotientEquiv i σ Γ) = canonicalWeight i Γ := by
  unfold canonicalWeight quotientEquiv
  congr 1
  exact Kontsevich.GeometricWeights.canonicalEffectiveWeight_oneExceptionalGraphEquiv 3 i σ Γ _ _

/-- Reindexing the actual quotient/choice data proves each orientation's
scalar covariance under simultaneous root and child relabelling. -/
theorem canonicalProfile_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (δ : Equiv.Perm (Fin 2)) (a : Fin 2) (H : BinaryGraph (n + 2) 3) :
    canonicalProfile (σ i) (δ a) (H.permuteInternal
      (SlotRelabelling.splitVertices i (σ i) σ rfl δ)) = canonicalProfile i a H := by
  unfold canonicalProfile pushforward
  rw [← Equiv.sum_comp (dataEquiv i σ δ)]
  apply Finset.sum_congr rfl
  intro D _
  rw [canonicalDataGraph_internal]
  have hinj : Function.Injective (fun G : BinaryGraph (n + 2) 3 ↦
      G.permuteInternal (SlotRelabelling.splitVertices i (σ i) σ rfl δ)) :=
    (permuteInternalEquiv 2 3 (SlotRelabelling.splitVertices i (σ i) σ rfl δ)).injective
  rw [hinj.eq_iff]
  change (if _ then canonicalWeight (k := ℝ) (σ i) (quotientEquiv i σ D.1) else 0) = _
  rw [canonicalWeight_quotientEquiv]

/-- Both orientations together depend only on the physical pair, before
performing the independent signed outgoing average. -/
theorem pairProfile_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (δ : Equiv.Perm (Fin 2)) (H : BinaryGraph (n + 2) 3) :
    pairProfile (σ i) (H.permuteInternal
      (SlotRelabelling.splitVertices i (σ i) σ rfl δ)) = pairProfile i H := by
  simp only [pairProfile, Finset.sum_apply]
  rw [← Equiv.sum_comp δ]
  simp only [canonicalProfile_internal]

/-- The independent outgoing average respects the same proved physical-pair
relabelling; its index permutations are transported, not assumed invariant. -/
theorem outgoing_pairProfile_internal (i : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (δ : Equiv.Perm (Fin 2)) (H : BinaryGraph (n + 2) 3) :
    outgoingAverage (pairProfile (σ i)) (H.permuteInternal
      (SlotRelabelling.splitVertices i (σ i) σ rfl δ)) = outgoingAverage (pairProfile i) H := by
  let ρ := SlotRelabelling.splitVertices i (σ i) σ rfl δ
  rw [outgoingAverage_apply, outgoingAverage_apply]
  have hs := sum_outgoing_internal_commute (pairProfile (σ i)) H ρ.symm
  simp only [Equiv.symm_symm] at hs
  rw [← hs]
  simp only [ρ, pairProfile_internal]

end EnvelopingIsomorphism.Deformation.GraphCurvatureInternalRelabelling
