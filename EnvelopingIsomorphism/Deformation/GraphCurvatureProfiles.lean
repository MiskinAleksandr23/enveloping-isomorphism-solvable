import EnvelopingIsomorphism.Deformation.GraphWeightedInsertion
import EnvelopingIsomorphism.Deformation.UniformCurvatureSplits

/-! Pure scalar profiles for the source Schouten-curvature boundary term.
All distinguished positions, six joined graph templates and the factor 1/2
remain explicit; no geometric identity or Poisson equation is assumed in the expansion. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles

open scoped BigOperators Classical
open UniformBinaryGraphs UniformCurvatureSplits GraphCoefficientProfiles

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

abbrev CurvatureGraph (i : Fin (n + 1)) := Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i

/-- The raw six-term scalar profile for one actual quotient graph. -/
def splitProfile (i : Fin (n + 1)) (Θ : CurvatureGraph i) : BinaryGraph (n + 2) 3 → k :=
  ∑ c : Fin 3,
    (pushforward (uniformCurvatureForward i Θ c) (fun _ ↦ 1) +
      pushforward (uniformCurvatureReverse i Θ c) (fun _ ↦ 1))

omit [CharZero k] in
theorem splitProfile_apply (i : Fin (n + 1)) (Θ : CurvatureGraph i) (H : BinaryGraph (n + 2) 3) :
    splitProfile (k := k) i Θ H = ∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
      ((if uniformCurvatureForward i Θ c χ = H then 1 else 0) +
        (if uniformCurvatureReverse i Θ c χ = H then 1 else 0)) := by
  simp only [splitProfile, Finset.sum_apply, Pi.add_apply, pushforward_apply, Finset.sum_add_distrib]

/-- Scalar source weights multiply the actual six-term profiles, with the
curvature normalization outside and every distinguished position retained. -/
def curvatureProfile (w : (i : Fin (n + 1)) → CurvatureGraph i → k) : BinaryGraph (n + 2) 3 → k :=
  (1/2 : k) • ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i, w i Θ • splitProfile i Θ

omit [CharZero k] in
theorem curvatureProfile_apply (w : (i : Fin (n + 1)) → CurvatureGraph i → k)
    (H : BinaryGraph (n + 2) 3) :
    curvatureProfile w H = (1/2 : k) * ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i,
      w i Θ * ∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
        ((if uniformCurvatureForward i Θ c χ = H then 1 else 0) +
          (if uniformCurvatureReverse i Θ c χ = H then 1 else 0)) := by
  simp only [curvatureProfile, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, splitProfile_apply]

omit [CharZero k] in
theorem evaluation_splitProfile (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (splitProfile (k := k) i Θ) =
      cochainThreeEquiv k _
        (∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
          (operator (uniformCurvatureForward i Θ c χ) (fun _ ↦ π) +
            operator (uniformCurvatureReverse i Θ c χ) (fun _ ↦ π))) := by
  simp only [splitProfile, map_sum, map_add, evaluation_pushforward, one_smul,
    Finset.sum_add_distrib]
  rfl

/-- The genuine weighted all-position ternary graph operator. -/
def weightedCurvature (w : (i : Fin (n + 1)) → CurvatureGraph i → k)
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (Q : Multiderivation k (MvPolynomial (Fin d) k) 3) : Ternary k (MvPolynomial (Fin d) k) :=
  ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i,
    w i Θ • cochainThreeEquiv k _
      (Gauge.PlacedMixedGraphTaylorCoefficients.graphCoefficient i Θ (fun _ ↦ π) Q)

/-- Evaluating the pure scalar profile gives exactly the actual weighted
Schouten-curvature insertion; the six terms and the 1/2 are already proved. -/
theorem evaluation_curvatureProfile
    (w : (i : Fin (n + 1)) → CurvatureGraph i → k)
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d)) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (curvatureProfile w) =
      weightedCurvature w π ((1/2 : k) • (show Multiderivation k (MvPolynomial (Fin d) k) 3 from
        schoutenBracket k d 1 1 π π)) := by
  rw [curvatureProfile, map_smul, map_sum]
  simp only [map_sum, map_smul, Finset.smul_sum, weightedCurvature]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro Θ hΘ
  rw [UniformCurvatureSplits.graphCoefficient_bracket, evaluation_splitProfile]
  simp only [Finset.sum_add_distrib, smul_smul, mul_comm]

/-- The source profile vanishes upon evaluation at a genuine Poisson bivector,
for every choice of scalar weights. -/
theorem evaluation_curvatureProfile_eq_zero
    (w : (i : Fin (n + 1)) → CurvatureGraph i → k)
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (hπ : (show Multiderivation k (MvPolynomial (Fin d) k) 3 from schoutenBracket k d 1 1 π π) = 0) :
    evaluation (GraphWeightedInsertion.ternaryValue π) (curvatureProfile w) = 0 := by
  rw [evaluation_curvatureProfile, hπ, smul_zero]
  simp [weightedCurvature]

omit [CharZero k] in
/-- This operator is exactly the existing all-position curvature family on
the full set of graphs, with the same scalar weights. -/
theorem weightedCurvature_eq_curvatureFamily
    (w : (j : ℕ) → (i : Fin (j + 1)) → Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i → k)
    (π : GraphWeightedInsertion.Bivector (k := k) (d := d))
    (Q : Multiderivation k (MvPolynomial (Fin d) k) 3) :
    weightedCurvature (w n) π Q =
      Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) w n
        (fun _ ↦ π) Q := by
  simp [weightedCurvature, Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily,
    Gauge.PlacedMixedGraphTaylorCoefficients.mapOutput,
    Gauge.PlacedMixedGraphTaylorCoefficients.effectiveFamily_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.llcomp_apply]

section Canonical

variable [Algebra ℝ k]

/-- The actual geometric quotient-graph weight at its retained distinguished position. -/
def canonicalWeight (i : Fin (n + 1)) (Θ : CurvatureGraph i) : k :=
  algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalEffectiveWeight Θ
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i))

theorem canonicalWeight_factorial (i : Fin (n + 1)) (Θ : CurvatureGraph i) :
    canonicalWeight (k := k) i Θ = ((n + 1).factorial : ℚ)⁻¹ •
      algebraMap ℝ k (Kontsevich.GeometricWeights.canonicalWeight Θ
        (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i)) :=
  Kontsevich.map_effectiveMCWeight (algebraMap ℝ k).toAddMonoidHom (n + 1) _

/-- The literal canonical scalar curvature profile retains both the 1/2
and the quotient internal-vertex factorial; outgoing factors remain in W. -/
theorem canonical_curvatureProfile_apply (H : BinaryGraph (n + 2) 3) :
    curvatureProfile (canonicalWeight (k := k)) H =
      (1/2 : k) * ∑ i : Fin (n + 1), ∑ Θ : CurvatureGraph i,
        (((n + 1).factorial : ℚ)⁻¹ • algebraMap ℝ k
          (Kontsevich.GeometricWeights.canonicalWeight Θ
            (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i))) *
          ∑ c : Fin 3, ∑ χ : SplitChoices i Θ,
            ((if uniformCurvatureForward i Θ c χ = H then 1 else 0) +
              (if uniformCurvatureReverse i Θ c χ = H then 1 else 0)) := by
  rw [curvatureProfile_apply]
  simp only [canonicalWeight_factorial]

end Canonical

end EnvelopingIsomorphism.Deformation.GraphCurvatureProfiles
