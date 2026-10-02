import EnvelopingIsomorphism.Deformation.MixedGraphInternalPairRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphPairLabelCounting
import EnvelopingIsomorphism.Deformation.MixedGraphLabelledClusterCounting

/-! Genuine mixed coefficient fibres over physical pairs with their retained
vector marker. Constancy is proved by actual quotient and child relabelling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairFibres
open scoped BigOperators Classical
open KontsevichGraph.General GraphLabelledClusterCounting GraphCurvatureLabelCounting
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphBlockRelabelling
open MixedGraphPairLabelCounting MixedGraphInternalPairRelabelling
open GeneralGraphSplitPairRelabelling MixedGraphCorrectionProfiles
variable {n : ℕ}

private theorem composed_internal_symm (σ τ : Equiv.Perm (Fin (n + 1))) (H : VectorGraph n 2) :
    internalGraphEquiv (σ.trans τ.symm) 2 ((internalGraphEquiv σ 2).symm H) =
      (internalGraphEquiv τ 2).symm H := by
  simp only [internalGraphEquiv_symm_apply, internalGraphEquiv_trans]
  have he : σ.symm.trans (σ.trans τ.symm) = τ.symm := by ext x; simp
  rw [he]

variable {k : Type*} [Field k]

theorem sourcePairProfile_same_fiber (w : UniformBinaryGraphs.BinaryGraph (n + 1) 2 → k)
    (hw : ∀ Γ σ, w (Γ.permuteInternal σ) = w Γ)
    (T : PhysicalPair n) (v : Fin (n + 2)) (D E : SourcePairLabels T v)
    (H : VectorGraph (n + 1) 2) :
    Source.pairProfile w D.1 ((internalGraphEquiv D.2.val.val 2).symm H) =
      Source.pairProfile w E.1 ((internalGraphEquiv E.2.val.val 2).symm H) := by
  let π := D.2.val.val.trans E.2.val.val.symm
  have hp : ∀ x, π x ∈ childPair E.1 ↔ x ∈ childPair D.1 := by
    intro x
    have he := E.2.val.property (E.2.val.val.symm (D.2.val.val x))
    simp only [Equiv.apply_symm_apply] at he
    exact he.symm.trans (D.2.val.property x)
  have h0 : π (vertexSplitChild D.1 0) = vertexSplitChild E.1 0 := by
    apply E.2.val.val.injective
    change E.2.val.val (E.2.val.val.symm (D.2.val.val (vertexSplitChild D.1 0))) = _
    rw [Equiv.apply_symm_apply, D.2.property, E.2.property]
  let ρ := quotient D.1 E.1 π hp
  have hr : ρ D.1 = E.1 := quotient_root D.1 E.1 π hp
  have hd := children_eq_refl_of_zero D.1 E.1 π hp h0
  have hs := splitVertices_quotient_children D.1 E.1 π hp
  rw [hd] at hs
  have h := Source.pairProfile_internal_root w hw D.1 E.1 ρ hr
    ((internalGraphEquiv D.2.val.val 2).symm H)
  rw [hs, composed_internal_symm] at h
  exact h.symm

theorem correctionPairProfile_pairRelabelling (p p' : Placement n)
    (π : Equiv.Perm (Fin (n + 3)))
    (hp : ∀ x, π x ∈ childPair p'.2.val ↔ x ∈ childPair p.2.val)
    (hvec : π (expandedVector p) = expandedVector p') (H : VectorGraph (n + 2) 2) :
    Correction.pairProfile p' (internalGraphEquiv π 2 H) = Correction.pairProfile p H := by
  let ρ : Equiv.Perm (Fin (n + 2)) := quotient p.2.val p'.2.val π hp
  let δ : Equiv.Perm (Fin 2) := children p.2.val p'.2.val π hp
  have hr : ρ p.2.val = p'.2.val := quotient_root p.2.val p'.2.val π hp
  have hv : ρ p.1 = p'.1 := by
    rw [quotient_outside p.2.val p'.2.val π hp p.1 p.2.property.symm]
    apply splitExternalEmbedding_injective p'.2.val
    exact (outside_spec p.2.val p'.2.val π hp p.1 p.2.property.symm).trans hvec
  have hs := splitVertices_quotient_children p.2.val p'.2.val π hp
  have h := Correction.pairProfile_internal_root p p' ρ δ hv hr H
  rw [hs] at h
  exact h

theorem correctionPairProfile_same_fiber (T : PhysicalPair (n + 1)) (v : Fin (n + 3))
    (D E : CorrectionPairLabels T v) (H : VectorGraph (n + 2) 2) :
    Correction.pairProfile D.1 ((internalGraphEquiv D.2.val.val 2).symm H) =
      Correction.pairProfile E.1 ((internalGraphEquiv E.2.val.val 2).symm H) := by
  let π := D.2.val.val.trans E.2.val.val.symm
  have hp : ∀ x, π x ∈ childPair E.1.2.val ↔ x ∈ childPair D.1.2.val := by
    intro x
    have he := E.2.val.property (E.2.val.val.symm (D.2.val.val x))
    simp only [Equiv.apply_symm_apply] at he
    exact he.symm.trans (D.2.val.property x)
  have hvec : π (expandedVector D.1) = expandedVector E.1 := by
    apply E.2.val.val.injective
    change E.2.val.val (E.2.val.val.symm (D.2.val.val (expandedVector D.1))) = _
    rw [Equiv.apply_symm_apply, D.2.property, E.2.property]
  have h := correctionPairProfile_pairRelabelling D.1 E.1 π hp hvec
    ((internalGraphEquiv D.2.val.val 2).symm H)
  rw [composed_internal_symm] at h
  exact h.symm

private theorem pushforward_zero_of_vertex {I : Type*} [Fintype I] {N : ℕ}
    (f : I → VectorGraph N 2) (w : I → k) (v : Fin (N + 1)) (hf : ∀ i, (f i).vertex = v)
    (H : VectorGraph N 2) (hH : H.vertex ≠ v) : GraphCoefficientProfiles.pushforward f w H = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  intro he
  exact hH ((congrArg VectorGraph.vertex he).symm.trans (hf i))

theorem sourcePairProfile_zero_of_vertex (w : UniformBinaryGraphs.BinaryGraph (n + 1) 2 → k)
    (i : Fin (n + 1)) (H : VectorGraph (n + 1) 2)
    (hH : H.vertex ≠ vertexSplitChild i 0) : Source.pairProfile w i H = 0 := by
  have hf := pushforward_zero_of_vertex (MixedGraphActionSplits.forwardDataGraph i)
    (fun D => w D.1) _ (fun _ => rfl) H hH
  have hb := pushforward_zero_of_vertex (MixedGraphActionSplits.backwardDataGraph i 1)
    (fun D => w D.1) _ (fun _ => rfl) H hH
  change MixedGraphActionSplits.forwardTemplateProfile i w H -
    (2 : k) • MixedGraphActionSplits.backwardTemplateProfile i 1 w H = 0
  unfold MixedGraphActionSplits.forwardTemplateProfile MixedGraphActionSplits.backwardTemplateProfile
  rw [hf, hb, smul_zero, sub_self]

theorem correctionPairProfile_zero_of_vertex (p : Placement n) (H : VectorGraph (n + 2) 2)
    (hH : H.vertex ≠ expandedVector p) : Correction.pairProfile p H = 0 := by
  change (∑ a : Fin 2, Correction.canonicalProfile p a H) = 0
  apply Finset.sum_eq_zero
  intro a _
  exact pushforward_zero_of_vertex (Correction.canonicalDataGraph p a) _ _ (fun _ => rfl) H hH

theorem inverse_vertex_ne_of_not_marked {N : ℕ} (σ : Equiv.Perm (Fin (N + 1)))
    (v : Fin (N + 1)) (H : VectorGraph N 2) (h : σ v ≠ H.vertex) :
    ((internalGraphEquiv σ 2).symm H).vertex ≠ v := by
  rw [MixedGraphLabelledClusterCounting.inverse_internalGraphEquiv_vertex]
  intro hv
  exact h ((congrArg σ hv).symm.trans (σ.apply_symm_apply H.vertex))

private theorem sum_eq_subtype_of_zero {I V : Type*} [Fintype I] [AddCommMonoid V]
    (p : I → Prop) [DecidablePred p] (f : I → V) (hf : ∀ i, ¬p i → f i = 0) :
    (∑ i, f i) = ∑ i : {i // p i}, f i.val := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f]
  have he : (∑ i : {i // ¬p i}, f i.val) = 0 := Finset.sum_eq_zero (fun i _ => hf i.val i.property)
  rw [he, add_zero]

/-- Regroup actual source labels by the physical pair and its required vector marker. -/
theorem sum_source_labels (v : Fin (n + 2))
    (f : (i : Fin (n + 1)) → Equiv.Perm (Fin (n + 2)) → k)
    (hf : ∀ i σ, σ (vertexSplitChild i 0) ≠ v → f i σ = 0) :
    (∑ i, ∑ σ, f i σ) = ∑ T : PhysicalPair n, ∑ D : SourcePairLabels T v, f D.1 D.2.val.val := by
  have h (i : Fin (n + 1)) : (∑ σ, f i σ) =
      ∑ T : PhysicalPair n, ∑ σ : ClusterFiber (childPair i) T.val, f i σ.val := by
    rw [← Fintype.sum_fiberwise (movedPair i) (f i)]
    apply Finset.sum_congr rfl
    intro T _
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight (fun σ => movedPair_eq_iff i σ T)) _ _ (fun _ => rfl)
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_eq_subtype_of_zero (fun σ : ClusterFiber (childPair i) T.val => σ.val (vertexSplitChild i 0) = v)
    (fun σ => f i σ.val) (fun σ hh => hf i σ.val hh)

/-- Correction regrouping retains both odd placements and fixes the exterior vector. -/
theorem sum_correction_labels (v : Fin (n + 3))
    (f : (p : Placement n) → Equiv.Perm (Fin (n + 3)) → k)
    (hf : ∀ p σ, σ (expandedVector p) ≠ v → f p σ = 0) :
    (∑ p, ∑ σ, f p σ) =
      ∑ T : PhysicalPair (n + 1), ∑ D : CorrectionPairLabels T v, f D.1 D.2.val.val := by
  have h (p : Placement n) : (∑ σ, f p σ) =
      ∑ T : PhysicalPair (n + 1), ∑ σ : ClusterFiber (childPair p.2.val) T.val, f p σ.val := by
    rw [← Fintype.sum_fiberwise (movedPair p.2.val) (f p)]
    apply Finset.sum_congr rfl
    intro T _
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight (fun σ => movedPair_eq_iff p.2.val σ T)) _ _ (fun _ => rfl)
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact sum_eq_subtype_of_zero (fun σ : ClusterFiber (childPair p.2.val) T.val => σ.val (expandedVector p) = v)
    (fun σ => f p σ.val) (fun σ hh => hf p σ.val hh)

end EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairFibres
