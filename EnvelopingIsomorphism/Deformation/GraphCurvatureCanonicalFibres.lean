import EnvelopingIsomorphism.Deformation.GraphCurvatureCyclicFibres
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

/-! The actual geometric curvature weights satisfy the even cyclic covariance,
so the six scalar fibres reduce to their canonical pair with factor three-halves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
open KontsevichGraph.General UniformCurvatureSplits SchoutenGraphContraction
open Kontsevich.GeometricWeightOutgoing
open scoped Classical BigOperators
variable {n : ℕ}

theorem cyclicPermutation_sign {R : Type*} [CommRing R] (c : Fin 3) :
    permutationSign (R := R) (cyclicPermutation c) = 1 := by
  have h : Equiv.Perm.sign (cyclicPermutation c) = 1 := by
    fin_cases c <;> decide
  simp [permutationSign, h]

variable {k : Type*} [Field k] [Algebra ℝ k]

/-- The actual quotient integral, including its MC factorial, is unchanged
by a cyclic permutation of the distinguished three outgoing slots. -/
theorem canonicalWeight_root_cyclic (i : Fin (n + 1)) (c : Fin 3) (Γ : CurvatureGraph i) :
    canonicalWeight (k := k) i (Γ.permuteOutgoing
      (rootOutgoing i (selectedArity i).symm (cyclicPermutation c))) = canonicalWeight i Γ := by
  unfold canonicalWeight
  rw [canonicalEffectiveWeight_permuteOutgoing, rootOutgoing_sign, cyclicPermutation_sign, one_mul]

/-- Unconditional finite multiplicity for the genuine geometric quotient
weights: no covariance or scalar boundary relation is supplied. -/
theorem canonical_curvatureProfile_three_halves :
    curvatureProfile (canonicalWeight (k := k) (n := n)) = (3 / 2 : k) • ∑ i : Fin (n + 1),
      (forwardTemplateProfile i 0 (canonicalWeight i) + reverseTemplateProfile i 0 (canonicalWeight i)) :=
  curvatureProfile_eq_three_halves _ (fun i c Γ ↦ canonicalWeight_root_cyclic i c Γ)

/-- Every forward geometric fibre has its literal quotient integral. -/
theorem canonical_forwardTemplateProfile_split (i : Fin (n + 1)) (c : Fin 3)
    (D : CurvatureSplitData i) :
    forwardTemplateProfile i c (canonicalWeight (k := k) i) (forwardDataGraph i c D) = canonicalWeight i D.1 :=
  forwardTemplateProfile_split i c _ D

/-- Every reverse geometric fibre has the same multiplicity one. -/
theorem canonical_reverseTemplateProfile_split (i : Fin (n + 1)) (c : Fin 3)
    (D : CurvatureSplitData i) :
    reverseTemplateProfile i c (canonicalWeight (k := k) i) (reverseDataGraph i c D) = canonicalWeight i D.1 :=
  reverseTemplateProfile_split i c _ D

end EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
