import EnvelopingIsomorphism.Deformation.GraphCurvatureFibres
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitLegPermutation

/-! The three cyclic templates are an actual reindexing of quotient outgoing
slots and incoming choices. This identifies their finite scalar fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open UniformBinaryGraphs UniformCurvatureSplits SchoutenGraphContraction GraphCoefficientProfiles
open scoped Classical BigOperators
variable {n : ℕ}

theorem forward_relabelLegs (ρ : Equiv.Perm (Fin 3)) :
    (bivectorForward (cyclicPermutation 0)).relabelLegs ρ = bivectorForward ρ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,s⟩
  fin_cases v <;> fin_cases s <;> rfl

theorem reverse_relabelLegs (ρ : Equiv.Perm (Fin 3)) :
    (bivectorReverse (cyclicPermutation 0)).relabelLegs ρ = bivectorReverse ρ := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,s⟩
  fin_cases v <;> fin_cases s <;> rfl

def cyclicDataEquiv (i : Fin (n + 1)) (c : Fin 3) : Equiv.Perm (CurvatureSplitData i) :=
  Graph.splitDataOutgoingEquiv i (rootOutgoing i (selectedArity i).symm (cyclicPermutation c))

theorem forwardDataGraph_cyclic (i : Fin (n + 1)) (c : Fin 3) (D : CurvatureSplitData i) :
    forwardDataGraph i 0 (cyclicDataEquiv i c D) = forwardDataGraph i c D := by
  have h := Graph.vertexSplitDataGraph_rootOutgoing i (selectedArity i).symm
    (bivectorForward (cyclicPermutation 0)) (cyclicPermutation c) D
  rw [forward_relabelLegs] at h
  exact congrArg (castGraph (vertexSplitArity_two i)) h

theorem reverseDataGraph_cyclic (i : Fin (n + 1)) (c : Fin 3) (D : CurvatureSplitData i) :
    reverseDataGraph i 0 (cyclicDataEquiv i c D) = reverseDataGraph i c D := by
  have h := Graph.vertexSplitDataGraph_rootOutgoing i (selectedArity i).symm
    (bivectorReverse (cyclicPermutation 0)) (cyclicPermutation c) D
  rw [reverse_relabelLegs] at h
  exact congrArg (castGraph (vertexSplitArity_two i)) h

variable {k : Type*} [Field k]

/-- Each cyclic forward family has the same finite scalar profile after
reindexing its actual quotient slots, when the supplied weight is invariant
under that explicit even permutation. -/
theorem forwardTemplateProfile_cyclic (i : Fin (n + 1)) (c : Fin 3) (w : CurvatureGraph i → k)
    (hw : ∀ Γ, w (Γ.permuteOutgoing (rootOutgoing i (selectedArity i).symm (cyclicPermutation c))) = w Γ) :
    forwardTemplateProfile i c w = forwardTemplateProfile i 0 w := by
  funext H
  symm
  change (∑ D : CurvatureSplitData i, if forwardDataGraph i 0 D = H then w D.1 else 0) =
    ∑ D : CurvatureSplitData i, if forwardDataGraph i c D = H then w D.1 else 0
  rw [← Equiv.sum_comp (cyclicDataEquiv i c)]
  apply Finset.sum_congr rfl
  intro D _
  rw [forwardDataGraph_cyclic]
  change (if _ then w (D.1.permuteOutgoing _) else 0) = _
  rw [hw]

theorem reverseTemplateProfile_cyclic (i : Fin (n + 1)) (c : Fin 3) (w : CurvatureGraph i → k)
    (hw : ∀ Γ, w (Γ.permuteOutgoing (rootOutgoing i (selectedArity i).symm (cyclicPermutation c))) = w Γ) :
    reverseTemplateProfile i c w = reverseTemplateProfile i 0 w := by
  funext H
  symm
  change (∑ D : CurvatureSplitData i, if reverseDataGraph i 0 D = H then w D.1 else 0) =
    ∑ D : CurvatureSplitData i, if reverseDataGraph i c D = H then w D.1 else 0
  rw [← Equiv.sum_comp (cyclicDataEquiv i c)]
  apply Finset.sum_congr rfl
  intro D _
  rw [reverseDataGraph_cyclic]
  change (if _ then w (D.1.permuteOutgoing _) else 0) = _
  rw [hw]

/-- Actual finite multiplicity: the three cyclic copies, together with the
curvature one-half, produce the exact factor three-halves. -/
theorem curvatureProfile_eq_three_halves (w : (i : Fin (n + 1)) → CurvatureGraph i → k)
    (hw : ∀ i c Γ, w i (Γ.permuteOutgoing
      (rootOutgoing i (selectedArity i).symm (cyclicPermutation c))) = w i Γ) :
    curvatureProfile w = (3 / 2 : k) • ∑ i : Fin (n + 1),
      (forwardTemplateProfile i 0 (w i) + reverseTemplateProfile i 0 (w i)) := by
  rw [curvatureProfile_eq_templateProfiles]
  have hf : ∀ i c, forwardTemplateProfile i c (w i) = forwardTemplateProfile i 0 (w i) :=
    fun i c ↦ forwardTemplateProfile_cyclic i c (w i) (hw i c)
  have hr : ∀ i c, reverseTemplateProfile i c (w i) = reverseTemplateProfile i 0 (w i) :=
    fun i c ↦ reverseTemplateProfile_cyclic i c (w i) (hw i c)
  simp only [hf, hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [← Nat.cast_smul_eq_nsmul k, ← Finset.smul_sum, smul_smul]
  congr 1
  ring

end EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
