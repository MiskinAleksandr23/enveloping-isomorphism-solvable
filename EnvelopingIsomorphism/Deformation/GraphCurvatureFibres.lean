import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitFibres
import EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles

/-! Exact finite fibres of all six actual main curvature templates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
open scoped BigOperators Classical
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits SchoutenGraphContraction GraphCoefficientProfiles
variable {n : ℕ}

abbrev CurvatureSplitData (i : Fin (n + 1)) :=
  Graph.VertexSplitData (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) 3 i

def forwardDataGraph (i : Fin (n + 1)) (c : Fin 3) (D : CurvatureSplitData i) : BinaryGraph (n + 2) 3 :=
  uniformCurvatureForward i D.1 c D.2

def reverseDataGraph (i : Fin (n + 1)) (c : Fin 3) (D : CurvatureSplitData i) : BinaryGraph (n + 2) 3 :=
  uniformCurvatureReverse i D.1 c D.2

private theorem castGraph_injective {b m : ℕ} {q q' : Fin b → ℕ} (h : q = q') :
    Function.Injective (castGraph (m := m) h) := by
  cases h
  exact Function.injective_id

theorem forwardDataGraph_injective (i : Fin (n + 1)) (c : Fin 3) : Function.Injective (forwardDataGraph i c) := by
  intro D E h
  have hleg (j : Fin 3) : (bivectorForward (cyclicPermutation c)).target
      (bivectorForwardLeg (cyclicPermutation c) j) = Sum.inr j := by
    have hm : bivectorForwardLeg (cyclicPermutation c) j ∈
        (bivectorForward (cyclicPermutation c)).incoming (Sum.inr j) := by
      rw [bivectorForward_incoming_leg]; simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  apply Graph.vertexSplitDataGraph_injective (m := 3) (bivectorForward (cyclicPermutation c))
    (bivectorForwardLeg (cyclicPermutation c)) hleg i (selectedArity i).symm
  exact castGraph_injective (vertexSplitArity_two i) h

theorem reverseDataGraph_injective (i : Fin (n + 1)) (c : Fin 3) : Function.Injective (reverseDataGraph i c) := by
  intro D E h
  have hleg (j : Fin 3) : (bivectorReverse (cyclicPermutation c)).target
      (bivectorReverseLeg (cyclicPermutation c) j) = Sum.inr j := by
    have hm : bivectorReverseLeg (cyclicPermutation c) j ∈
        (bivectorReverse (cyclicPermutation c)).incoming (Sum.inr j) := by
      rw [bivectorReverse_incoming_leg]; simp
    simpa only [Graph.incoming, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  apply Graph.vertexSplitDataGraph_injective (m := 3) (bivectorReverse (cyclicPermutation c))
    (bivectorReverseLeg (cyclicPermutation c)) hleg i (selectedArity i).symm
  exact castGraph_injective (vertexSplitArity_two i) h

variable {k : Type*} [Field k]

def forwardTemplateProfile (i : Fin (n + 1)) (c : Fin 3) (w : CurvatureGraph i → k) : BinaryGraph (n + 2) 3 → k :=
  pushforward (forwardDataGraph i c) (fun D ↦ w D.1)

def reverseTemplateProfile (i : Fin (n + 1)) (c : Fin 3) (w : CurvatureGraph i → k) : BinaryGraph (n + 2) 3 → k :=
  pushforward (reverseDataGraph i c) (fun D ↦ w D.1)

/-- Each fixed forward fibre is one genuine quotient weight. -/
theorem forwardTemplateProfile_split (i : Fin (n + 1)) (c : Fin 3)
    (w : CurvatureGraph i → k) (D : CurvatureSplitData i) :
    forwardTemplateProfile i c w (forwardDataGraph i c D) = w D.1 := by
  simp only [forwardTemplateProfile, pushforward, (forwardDataGraph_injective i c).eq_iff]
  simp

/-- Each fixed reverse fibre has the same exact multiplicity one. -/
theorem reverseTemplateProfile_split (i : Fin (n + 1)) (c : Fin 3)
    (w : CurvatureGraph i → k) (D : CurvatureSplitData i) :
    reverseTemplateProfile i c w (reverseDataGraph i c D) = w D.1 := by
  simp only [reverseTemplateProfile, pushforward, (reverseDataGraph_injective i c).eq_iff]
  simp

/-- The original all-position curvature profile is precisely the sum of its
six actual graph fibres, with its actual one-half normalization. -/
theorem curvatureProfile_eq_templateProfiles (w : (i : Fin (n + 1)) → CurvatureGraph i → k) :
    curvatureProfile w = (1 / 2 : k) • ∑ i : Fin (n + 1), ∑ c : Fin 3,
      (forwardTemplateProfile i c (w i) + reverseTemplateProfile i c (w i)) := by
  funext H
  simp only [curvatureProfile, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [splitProfile, Finset.sum_apply, Pi.add_apply,
    forwardTemplateProfile, reverseTemplateProfile, pushforward_apply,
    Fintype.sum_sigma, Finset.mul_sum, mul_add, mul_ite, mul_one, mul_zero,
    forwardDataGraph, reverseDataGraph]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]

end EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
