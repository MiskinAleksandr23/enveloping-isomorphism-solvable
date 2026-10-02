import EnvelopingIsomorphism.Deformation.VectorSplitOutgoingAverage
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
import EnvelopingIsomorphism.Deformation.GraphBinaryOutgoingClusterSums

/-! Exact source physical coefficients for all three genuine Schouten
templates. The backward factor two cancels its binary sender stabilizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedSourcePhysicalCoefficient
open scoped Classical BigOperators
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier MixedGraphAveraging MixedGraphActionSplits
open MixedGraphInternalPairRelabelling MixedGraphPairLabelCounting
open MixedGraphPhysicalPairSums MixedGraphOutgoingPairNormalization
open GraphCurvatureLabelCounting GraphCanonicalBinaryWeights UniformBinaryGraphs
open Kontsevich.MixedTwoPointTemplateWeight
variable {n : ℕ}

def sourceChildPair (i : Fin (n+1)) : PhysicalPair n := ⟨childPair i, card_childPair i⟩

private def sourceIdentityLabel (i : Fin (n+1)) :
    SourcePairLabels (sourceChildPair i) (vertexSplitChild i 0) :=
  ⟨i, ⟨⟨Equiv.refl _, fun _ ↦ Iff.rfl⟩, rfl⟩⟩

private theorem ofProfile_injective {N : ℕ} {q : Fin (N+1) → ℕ} (i : Fin (N+1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) :
    Function.Injective (ofProfile (m := 2) i h) := by
  subst q
  intro Γ Δ he
  exact (Sigma.mk.inj he).2.eq

theorem sourcePhysicalCoefficient_ofProfile (i : Fin (n+1))
    (H : Graph (vertexSplitArity (fun _ : Fin (n+1) ↦ 2) vectorBivectorArity i) 2) :
    sourcePhysicalCoefficient (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) (sourceChildPair i) =
      outgoingAverage (Source.pairProfile (rawBinaryWeight (n+1)) i)
        (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) := by
  unfold sourcePhysicalCoefficient
  rw [outgoingAverage_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  have h := rawSourcePairCoefficient_eq
    ((outgoingGraphEquiv τ 2).symm (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H))
    (sourceChildPair i) (sourceIdentityLabel i)
  simpa only [sourceIdentityLabel, MixedGraphBlockRelabelling.internalGraphEquiv_symm_apply,
    Equiv.refl_symm, MixedGraphBlockRelabelling.internalGraphEquiv_refl] using h

theorem pairProfile_ofProfile (w : BinaryGraph (n+1) 2 → ℝ) (i : Fin (n+1))
    (H : Graph (vertexSplitArity (fun _ : Fin (n+1) ↦ 2) vectorBivectorArity i) 2) :
    Source.pairProfile w i (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) =
      VectorSplitOutgoingAverage.pairProfile i rfl w H := by
  have hf : forwardTemplateProfile i w (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) =
      VectorSplitOutgoingAverage.profile i rfl w 0 H := by
    unfold forwardTemplateProfile VectorSplitOutgoingAverage.profile GraphCoefficientProfiles.pushforward
    apply Finset.sum_congr rfl
    intro D _
    have he : forwardDataGraph i D = ofProfile (vertexSplitChild i 0) (actionSplitArity i) H ↔
        VectorSplitOutgoingAverage.splitGraph i rfl 0 D = H :=
      (ofProfile_injective (vertexSplitChild i 0) (actionSplitArity i)).eq_iff
    simp only [he]
  have hb : backwardTemplateProfile i 1 w (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) =
      VectorSplitOutgoingAverage.profile i rfl w 1 H := by
    unfold backwardTemplateProfile VectorSplitOutgoingAverage.profile GraphCoefficientProfiles.pushforward
    apply Finset.sum_congr rfl
    intro D _
    have he : backwardDataGraph i 1 D = ofProfile (vertexSplitChild i 0) (actionSplitArity i) H ↔
        VectorSplitOutgoingAverage.splitGraph i rfl 1 D = H :=
      (ofProfile_injective (vertexSplitChild i 0) (actionSplitArity i)).eq_iff
    simp only [he]
  simp only [Source.pairProfile, VectorSplitOutgoingAverage.pairProfile, Pi.sub_apply,
    Pi.smul_apply, hf, hb]

theorem sourcePhysicalCoefficient_eq_nativeAverage (i : Fin (n+1))
    (H : Graph (vertexSplitArity (fun _ : Fin (n+1) ↦ 2) vectorBivectorArity i) 2) :
    sourcePhysicalCoefficient (ofProfile (vertexSplitChild i 0) (actionSplitArity i) H) (sourceChildPair i) =
      GeneralGraphOutgoingAverage.average
        (VectorSplitOutgoingAverage.pairProfile i rfl (rawBinaryWeight (n+1))) H := by
  rw [sourcePhysicalCoefficient_ofProfile, outgoingAverage_ofProfile]
  simp only [pairProfile_ofProfile]
  rfl

private theorem raw_weight_outgoing (Γ : BinaryGraph (n+1) 2)
    (τ : GeneralGraphOutgoingAverage.Group (fun _ : Fin (n+1) ↦ 2)) :
    rawBinaryWeight (n+1) (Γ.permuteOutgoing τ) =
      GeneralGraphOutgoingAverage.sign τ * rawBinaryWeight (n+1) Γ :=
  GraphBinaryOutgoingClusterSums.rawBinaryWeight_permuteOutgoing (n+1) Γ τ

theorem sourcePhysicalCoefficient_forward (i : Fin (n+1)) (D : SourceSplitData i) :
    sourcePhysicalCoefficient (forwardDataGraph i D) (sourceChildPair i) = rawBinaryWeight (n+1) D.1 := by
  change sourcePhysicalCoefficient (ofProfile (vertexSplitChild i 0) (actionSplitArity i) _) _ = _
  rw [sourcePhysicalCoefficient_eq_nativeAverage]
  exact VectorSplitOutgoingAverage.average_pairProfile_forward i rfl _ raw_weight_outgoing D

theorem sourcePhysicalCoefficient_backward (i : Fin (n+1)) (D : SourceSplitData i) :
    sourcePhysicalCoefficient (backwardDataGraph i 1 D) (sourceChildPair i) = -rawBinaryWeight (n+1) D.1 := by
  change sourcePhysicalCoefficient (ofProfile (vertexSplitChild i 0) (actionSplitArity i) _) _ = _
  rw [sourcePhysicalCoefficient_eq_nativeAverage]
  exact VectorSplitOutgoingAverage.average_pairProfile_backward i rfl _ raw_weight_outgoing D

theorem sourcePhysicalCoefficient_backward_swap (i : Fin (n+1)) (D : SourceSplitData i) :
    sourcePhysicalCoefficient (backwardDataGraph i (Equiv.swap 0 1) D) (sourceChildPair i) =
      rawBinaryWeight (n+1) D.1 := by
  rw [← MixedGraphCanonicalSplitFibres.Source.backwardDataGraph_relabel,
    sourcePhysicalCoefficient_backward]
  change -rawBinaryWeight (n+1)
    (D.1.permuteOutgoing (rootOutgoing i rfl (Equiv.swap 0 1))) = _
  rw [raw_weight_outgoing]
  have hs : GeneralGraphOutgoingAverage.sign (rootOutgoing (q := fun _ : Fin (n+1) ↦ 2)
      i rfl (Equiv.swap 0 1)) = -1 := by
    rw [GeneralGraphOutgoingAverage.sign, rootOutgoing_sign]
    simp [permutationSign]
  rw [hs, neg_one_mul, neg_neg]

/-- The three physical source coefficients are literally plus, minus, plus
the original raw quotient integral. All incoming choices are retained. -/
theorem sourcePhysicalCoefficient_split (i : Fin (n+1)) (c : Fin 3) (D : SourceSplitData i) :
    sourcePhysicalCoefficient (Source.templateDataGraph i (sourceTemplate c) D) (sourceChildPair i) =
      (if c = 1 then (-1 : ℝ) else 1) * rawBinaryWeight (n+1) D.1 := by
  fin_cases c
  · change sourcePhysicalCoefficient (forwardDataGraph i D) _ = _
    simpa using sourcePhysicalCoefficient_forward i D
  · change sourcePhysicalCoefficient (backwardDataGraph i 1 D) _ = _
    simpa using sourcePhysicalCoefficient_backward i D
  · change sourcePhysicalCoefficient (backwardDataGraph i (Equiv.swap 0 1) D) _ = _
    simpa using sourcePhysicalCoefficient_backward_swap i D

end EnvelopingIsomorphism.Deformation.MixedSourcePhysicalCoefficient
