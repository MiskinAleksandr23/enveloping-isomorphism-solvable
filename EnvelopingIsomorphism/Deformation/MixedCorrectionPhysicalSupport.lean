import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility
import EnvelopingIsomorphism.Deformation.Kontsevich.BinaryFaceAdmissibilityOutgoing

/-! Support of the actual correction coefficient consists of genuine
two-point contraction graphs, including its full outgoing average. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedCorrectionPhysicalSupport
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedGraphCorrectionProfiles MixedGraphInternalPairRelabelling
open MixedGraphOutgoingPairNormalization MixedGraphPhysicalPairSums MixedGraphPairLabelCounting
open scoped Classical BigOperators
variable {n : ℕ} (p : Placement n)

private def identityLabel : CorrectionPairLabels (correctionChildPair p) (expandedVector p) :=
  ⟨p, ⟨⟨Equiv.refl _, fun _ => Iff.rfl⟩, rfl⟩⟩

private theorem ofProfile_injective {N : ℕ} {q : Fin (N+1) → ℕ} (v : Fin (N+1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v) :
    Function.Injective (ofProfile (m := 2) v h) := by
  subst q
  intro G H he
  exact (Sigma.mk.inj he).2.eq

variable (H : Graph (vertexSplitArity (twoOddArity p.1 p.2) TwoVertexContraction.bivectorArity p.2.val) 2)

theorem coefficient_eq_average :
    correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) H) (correctionChildPair p) =
      (2 * (n+2).factorial : ℕ) * outgoingAverage (Correction.pairProfile p)
        (ofProfile (expandedVector p) (splitArity p) H) := by
  have he (τ : OutgoingGroup (n+2)) :
      rawCorrectionPairCoefficient
        ((outgoingGraphEquiv τ 2).symm (ofProfile (expandedVector p) (splitArity p) H))
        (correctionChildPair p) = ((n+2).factorial : ℝ) * Correction.pairProfile p
          ((outgoingGraphEquiv τ 2).symm (ofProfile (expandedVector p) (splitArity p) H)) := by
    have h := rawCorrectionPairCoefficient_eq_scaled
      ((outgoingGraphEquiv τ 2).symm (ofProfile (expandedVector p) (splitArity p) H))
      (correctionChildPair p) (identityLabel p)
    simpa only [identityLabel, MixedGraphBlockRelabelling.internalGraphEquiv_symm_apply,
      Equiv.refl_symm, MixedGraphBlockRelabelling.internalGraphEquiv_refl] using h
  simp only [correctionPhysicalCoefficient, he, outgoingAverage_apply, Finset.mul_sum,
    Nat.cast_mul, Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem pairProfile_zero_of_not_data (hD : ¬ TwoPointSplitFaceContraction.Data p.2.val H) :
    Correction.pairProfile p (ofProfile (expandedVector p) (splitArity p) H) = 0 := by
  unfold Correction.pairProfile
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro c _
  unfold Correction.canonicalProfile GraphCoefficientProfiles.pushforward
  apply Finset.sum_eq_zero
  intro D _
  split_ifs with he
  · have hg := ofProfile_injective (expandedVector p) (splitArity p) he
    exact (hD (hg ▸ TwoPointTemplateAdmissibility.correction_data p D.1 c D.2)).elim
  · rfl

theorem coefficient_eq_nativeAverage :
    correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) H) (correctionChildPair p) =
      (2 * (n+2).factorial : ℕ) * GeneralGraphOutgoingAverage.average
        (fun G => Correction.pairProfile p (ofProfile (expandedVector p) (splitArity p) G)) H := by
  rw [coefficient_eq_average, outgoingAverage_ofProfile]
  rfl

theorem coefficient_permuteOutgoing
    (τ : (v : Fin (n+3)) → Equiv.Perm (Fin (vertexSplitArity (twoOddArity p.1 p.2)
      TwoVertexContraction.bivectorArity p.2.val v))) :
    correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) (H.permuteOutgoing τ))
        (correctionChildPair p) =
      GeneralGraphOutgoingAverage.sign τ *
        correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) H) (correctionChildPair p) := by
  rw [coefficient_eq_nativeAverage, coefficient_eq_nativeAverage,
    GeneralGraphOutgoingAverage.average_permuteOutgoing]
  ring

theorem coefficient_zero_of_not_data (hD : ¬ TwoPointSplitFaceContraction.Data p.2.val H) :
    correctionPhysicalCoefficient (ofProfile (expandedVector p) (splitArity p) H) (correctionChildPair p) = 0 := by
  rw [coefficient_eq_nativeAverage, GeneralGraphOutgoingAverage.average]
  have hz (τ : (v : Fin (n+3)) → Equiv.Perm (Fin (vertexSplitArity (twoOddArity p.1 p.2)
      TwoVertexContraction.bivectorArity p.2.val v))) :
      Correction.pairProfile p (ofProfile (expandedVector p) (splitArity p)
        (H.permuteOutgoing (fun v => (τ v).symm))) = 0 :=
    pairProfile_zero_of_not_data p _ (fun h => hD
      ((BinaryFaceAdmissibilityOutgoing.data_permuteOutgoing_iff p.2.val (selectedArity p).symm H _).mp h))
  simp only [hz, mul_zero, Finset.sum_const_zero]

end EnvelopingIsomorphism.Deformation.MixedCorrectionPhysicalSupport
