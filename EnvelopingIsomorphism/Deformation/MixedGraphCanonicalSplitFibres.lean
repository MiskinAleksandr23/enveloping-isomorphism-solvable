import EnvelopingIsomorphism.Deformation.MixedGraphSourceFibres
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionFibres
import EnvelopingIsomorphism.Deformation.GraphCurvatureCanonicalFibres
import EnvelopingIsomorphism.Deformation.GraphCanonicalBinaryWeights

/-! Actual low-arity template multiplicities in the mixed scalar boundary.
The two backward source copies have opposite quotient-slot signs; all three
curvature cyclic copies have positive sign. Odd placement signs remain intact. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphCanonicalSplitFibres
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier SchoutenGraphContraction GraphCoefficientProfiles
open Kontsevich.GeometricWeightOutgoing
variable {n : ℕ}

private theorem pushforward_reindex_smul {k I A : Type*} [CommRing k] [Fintype I]
    (f g : I → A) (e : Equiv.Perm I) (w : I → k) (s : k)
    (hf : ∀ i, f (e i) = g i) (hw : ∀ i, w (e i) = s * w i) :
    pushforward f w = s • pushforward g w := by
  funext a
  simp only [pushforward, Pi.smul_apply, smul_eq_mul]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hw]
  split_ifs <;> simp

namespace Correction
open MixedGraphCorrectionProfiles

def cyclicDataEquiv (p : Placement n) (c : Fin 3) : Equiv.Perm (CorrectionSplitData p) :=
  Graph.splitDataOutgoingEquiv (q := twoOddArity p.1 p.2) p.2 (rootOutgoing (q := twoOddArity p.1 p.2) p.2 (selectedArity p).symm (cyclicPermutation c))

theorem forwardDataGraph_cyclic (p : Placement n) (c : Fin 3) (D : CorrectionSplitData p) :
    forwardDataGraph p 0 (cyclicDataEquiv p c D) = forwardDataGraph p c D := by
  have h := Graph.vertexSplitDataGraph_rootOutgoing (q := twoOddArity p.1 p.2) p.2 (selectedArity p).symm
    (bivectorForward (cyclicPermutation 0)) (cyclicPermutation c) D
  rw [GraphCurvatureProfiles.forward_relabelLegs] at h
  exact congrArg (ofProfile (expandedVector p) (splitArity p)) h

theorem reverseDataGraph_cyclic (p : Placement n) (c : Fin 3) (D : CorrectionSplitData p) :
    reverseDataGraph p 0 (cyclicDataEquiv p c D) = reverseDataGraph p c D := by
  have h := Graph.vertexSplitDataGraph_rootOutgoing (q := twoOddArity p.1 p.2) p.2 (selectedArity p).symm
    (bivectorReverse (cyclicPermutation 0)) (cyclicPermutation c) D
  rw [GraphCurvatureProfiles.reverse_relabelLegs] at h
  exact congrArg (ofProfile (expandedVector p) (splitArity p)) h

variable {k : Type*} [Field k] [Algebra ℝ k]

theorem canonicalQuotientWeight_root_cyclic (p : Placement n) (c : Fin 3) (Γ : QuotientGraph p) :
    canonicalQuotientWeight (k := k) ⟨p, Γ.permuteOutgoing
      (rootOutgoing p.2 (selectedArity p).symm (cyclicPermutation c))⟩ =
      canonicalQuotientWeight ⟨p, Γ⟩ := by
  unfold canonicalQuotientWeight
  rw [canonicalEffectiveWeight_permuteOutgoing, rootOutgoing_sign,
    GraphCurvatureProfiles.cyclicPermutation_sign, one_mul]

theorem signedForwardTemplateProfile_cyclic (p : Placement n) (c : Fin 3) :
    signedForwardTemplateProfile p c (canonicalQuotientWeight (k := k)) =
      signedForwardTemplateProfile p 0 canonicalQuotientWeight := by
  symm
  simpa only [one_smul, signedForwardTemplateProfile] using pushforward_reindex_smul (forwardDataGraph p 0)
    (forwardDataGraph p c) (cyclicDataEquiv p c)
    (fun (D : CorrectionSplitData p) => placementSign (k := k) p * canonicalQuotientWeight ⟨p,D.1⟩) 1
    (forwardDataGraph_cyclic p c) (fun (D : CorrectionSplitData p) => by
      change placementSign p * canonicalQuotientWeight ⟨p,D.1.permuteOutgoing _⟩ = _
      rw [canonicalQuotientWeight_root_cyclic, one_mul])

theorem signedReverseTemplateProfile_cyclic (p : Placement n) (c : Fin 3) :
    signedReverseTemplateProfile p c (canonicalQuotientWeight (k := k)) =
      signedReverseTemplateProfile p 0 canonicalQuotientWeight := by
  symm
  simpa only [one_smul, signedReverseTemplateProfile] using pushforward_reindex_smul (reverseDataGraph p 0)
    (reverseDataGraph p c) (cyclicDataEquiv p c)
    (fun (D : CorrectionSplitData p) => placementSign (k := k) p * canonicalQuotientWeight ⟨p,D.1⟩) 1
    (reverseDataGraph_cyclic p c) (fun (D : CorrectionSplitData p) => by
      change placementSign p * canonicalQuotientWeight ⟨p,D.1.permuteOutgoing _⟩ = _
      rw [canonicalQuotientWeight_root_cyclic, one_mul])

/-- Unconditional mixed six-template collapse. Each remaining canonical fibre
still carries its genuine vector/trivector placement sign. -/
theorem canonical_correctionProfile_three_halves :
    correctionProfile (canonicalQuotientWeight (k := k) (n := n)) =
      (3 / 2 : k) • ∑ p : Placement n,
        (signedForwardTemplateProfile p 0 canonicalQuotientWeight +
          signedReverseTemplateProfile p 0 canonicalQuotientWeight) := by
  rw [correctionProfile_eq_templateProfiles]
  simp only [signedForwardTemplateProfile_cyclic, signedReverseTemplateProfile_cyclic,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [← Nat.cast_smul_eq_nsmul k, ← Finset.smul_sum, smul_smul]
  congr 1
  ring

end Correction

namespace Source
open MixedGraphActionSplits UniformBinaryGraphs GraphCanonicalBinaryWeights

theorem backward_relabelLegs (ρ : Equiv.Perm (Fin 2)) :
    (vectorBivectorBackward 1).relabelLegs ρ = vectorBivectorBackward ρ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  fin_cases v <;> fin_cases j <;> rfl

def backwardDataEquiv (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2)) : Equiv.Perm (SourceSplitData i) :=
  Graph.splitDataOutgoingEquiv i (rootOutgoing i rfl ρ)

theorem backwardDataGraph_relabel (i : Fin (n + 1)) (ρ : Equiv.Perm (Fin 2)) (D : SourceSplitData i) :
    backwardDataGraph i 1 (backwardDataEquiv i ρ D) = backwardDataGraph i ρ D := by
  have h := Graph.vertexSplitDataGraph_rootOutgoing i rfl (vectorBivectorBackward 1) ρ D
  rw [backward_relabelLegs] at h
  exact congrArg (ofProfile (vertexSplitChild i 0) (actionSplitArity i)) h

theorem canonicalBinaryWeight_root_swap (i : Fin (n + 1)) (Γ : BinaryGraph (n + 1) 2) :
    GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)
      (Γ.permuteOutgoing (rootOutgoing i rfl (Equiv.swap 0 1))) =
      -GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1) Γ := by
  rw [canonicalBinaryWeight_eq_factorial, canonicalBinaryWeight_eq_factorial]
  simp only [rawBinaryWeight, canonicalWeight_permuteOutgoing, rootOutgoing_sign]
  have hs : permutationSign (R := ℝ) (Equiv.swap (0 : Fin 2) 1) = -1 := by
    simp [permutationSign]
  rw [hs]
  ring

theorem canonical_backwardTemplateProfile_swap (i : Fin (n + 1)) :
    backwardTemplateProfile i (Equiv.swap 0 1)
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) =
      -backwardTemplateProfile i 1 (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) := by
  have h := pushforward_reindex_smul (backwardDataGraph i 1) (backwardDataGraph i (Equiv.swap 0 1))
    (backwardDataEquiv i (Equiv.swap 0 1))
    (fun D => GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1) D.1) (-1)
    (backwardDataGraph_relabel i (Equiv.swap 0 1)) (fun D => by
      change GraphBoundaryProfiles.canonicalBinaryWeight (n + 1) (D.1.permuteOutgoing _) = _
      rw [canonicalBinaryWeight_root_swap, neg_one_mul])
  change backwardTemplateProfile i 1 _ = (-1 : ℝ) • backwardTemplateProfile i (Equiv.swap 0 1) _ at h
  rw [neg_one_smul] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- The signed three-term vector action is exactly forward minus twice the
canonical backward fibre; its factor two cancels the binary sender normalizer. -/
theorem canonical_sourceActionProfile_two_templates :
    sourceActionProfile (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) =
      ∑ i : Fin (n + 1), (forwardTemplateProfile i
        (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1)) -
          (2 : ℝ) • backwardTemplateProfile i 1
            (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1))) := by
  rw [sourceActionProfile_eq_templateProfiles]
  simp only [canonical_backwardTemplateProfile_swap]
  apply Finset.sum_congr rfl
  intro i _
  module

end Source
end EnvelopingIsomorphism.Deformation.MixedGraphCanonicalSplitFibres
