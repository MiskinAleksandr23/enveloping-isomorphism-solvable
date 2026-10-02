import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitFibres
import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles

/-! Exact fibres of the six curvature split templates in the mixed carrier.
The two-odd placement sign is retained in each scalar quotient weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier SchoutenGraphContraction GraphCoefficientProfiles
variable {n : ℕ}

abbrev CorrectionSplitData (p : Placement n) :=
  Graph.VertexSplitData (twoOddArity p.1 p.2) 2 p.2

def forwardDataGraph (p : Placement n) (c : Fin 3) (D : CorrectionSplitData p) :
    VectorGraph (n + 2) 2 := splitForward p D.1 c D.2

def reverseDataGraph (p : Placement n) (c : Fin 3) (D : CorrectionSplitData p) :
    VectorGraph (n + 2) 2 := splitReverse p D.1 c D.2

private theorem ofProfile_injective {q : Fin (n + 1) → ℕ} {m : ℕ} (i : Fin (n + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) :
    Function.Injective (ofProfile (m := m) i h) := by
  subst q
  intro Γ Δ he
  exact (Sigma.mk.inj he).2.eq

theorem forwardDataGraph_injective (p : Placement n) (c : Fin 3) :
    Function.Injective (forwardDataGraph p c) := by
  intro D E h
  have hleg (j : Fin 3) : (bivectorForward (cyclicPermutation c)).target
      (bivectorForwardLeg (cyclicPermutation c) j) = Sum.inr j := by
    have hm : bivectorForwardLeg (cyclicPermutation c) j ∈
        (bivectorForward (cyclicPermutation c)).incoming (Sum.inr j) := by
      rw [bivectorForward_incoming_leg]
      simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  apply Graph.vertexSplitDataGraph_injective (q := twoOddArity p.1 p.2) (m := 2) (bivectorForward (cyclicPermutation c))
    (bivectorForwardLeg (cyclicPermutation c)) hleg p.2 (selectedArity p).symm
  exact ofProfile_injective _ (splitArity p) h

theorem reverseDataGraph_injective (p : Placement n) (c : Fin 3) :
    Function.Injective (reverseDataGraph p c) := by
  intro D E h
  have hleg (j : Fin 3) : (bivectorReverse (cyclicPermutation c)).target
      (bivectorReverseLeg (cyclicPermutation c) j) = Sum.inr j := by
    have hm : bivectorReverseLeg (cyclicPermutation c) j ∈
        (bivectorReverse (cyclicPermutation c)).incoming (Sum.inr j) := by
      rw [bivectorReverse_incoming_leg]
      simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  apply Graph.vertexSplitDataGraph_injective (q := twoOddArity p.1 p.2) (m := 2) (bivectorReverse (cyclicPermutation c))
    (bivectorReverseLeg (cyclicPermutation c)) hleg p.2 (selectedArity p).symm
  exact ofProfile_injective _ (splitArity p) h

variable {k : Type*} [Field k]

def signedForwardTemplateProfile (p : Placement n) (c : Fin 3) (w : CorrectionGraph n → k) :
    VectorGraph (n + 2) 2 → k :=
  pushforward (forwardDataGraph p c) (fun D => placementSign p * w ⟨p, D.1⟩)

def signedReverseTemplateProfile (p : Placement n) (c : Fin 3) (w : CorrectionGraph n → k) :
    VectorGraph (n + 2) 2 → k :=
  pushforward (reverseDataGraph p c) (fun D => placementSign p * w ⟨p, D.1⟩)

private theorem pushforward_at_injective {I A : Type*} [Fintype I]
    (f : I → A) (hf : Function.Injective f) (w : I → k) (i : I) :
    pushforward f w (f i) = w i := by
  simp only [pushforward, hf.eq_iff]
  simp

/-- The exact forward fibre includes its original two-odd ordering sign. -/
theorem signedForwardTemplateProfile_split (p : Placement n) (c : Fin 3)
    (w : CorrectionGraph n → k) (Θ : QuotientGraph p) (χ : SplitChoices p Θ) :
    signedForwardTemplateProfile p c w (splitForward p Θ c χ) =
      placementSign p * w ⟨p, Θ⟩ :=
  pushforward_at_injective _ (forwardDataGraph_injective p c) _ ⟨Θ, χ⟩

/-- Reverse fibres have the same placement sign and true multiplicity one. -/
theorem signedReverseTemplateProfile_split (p : Placement n) (c : Fin 3)
    (w : CorrectionGraph n → k) (Θ : QuotientGraph p) (χ : SplitChoices p Θ) :
    signedReverseTemplateProfile p c w (splitReverse p Θ c χ) =
      placementSign p * w ⟨p, Θ⟩ :=
  pushforward_at_injective _ (reverseDataGraph_injective p c) _ ⟨Θ, χ⟩

/-- Finite curvature assembly retains all six template fibres, every pair
of odd placements, and the exact one-half coefficient. -/
theorem correctionProfile_eq_templateProfiles (w : CorrectionGraph n → k) :
    correctionProfile w = (1 / 2 : k) • ∑ p : Placement n, ∑ c : Fin 3,
      (signedForwardTemplateProfile p c w + signedReverseTemplateProfile p c w) := by
  funext H
  simp only [correctionProfile, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp only [splitProfile, Finset.sum_apply, Pi.add_apply,
    signedForwardTemplateProfile, signedReverseTemplateProfile, pushforward_apply,
    Fintype.sum_sigma, Finset.mul_sum, mul_add, mul_ite, mul_one, mul_zero,
    forwardDataGraph, reverseDataGraph]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]

end EnvelopingIsomorphism.Deformation.MixedGraphCorrectionProfiles
