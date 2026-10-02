import EnvelopingIsomorphism.Deformation.UniformBinaryContractionAdmissibility

/-! A literal extracted raw quotient coefficient for every graph: admissible
one-arrow pairs give their signed geometric integral, and other pairs give zero.
Its equality to the actual outgoing fibre average is proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCurvatureExtractedCoefficient
open KontsevichGraph.General KontsevichGraph.General.Graph
open UniformBinaryGraphs UniformCurvatureOutgoing UniformBinaryContraction
open GraphCurvatureProfiles GraphCurvatureOutgoingAverage BinaryGraphAveraging
open scoped Classical BigOperators
variable {n : ℕ} (i : Fin (n + 1))

def rawWeight (Γ : CurvatureGraph i) : ℝ :=
  Kontsevich.GeometricWeights.canonicalWeight Γ (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i)

theorem canonicalWeight_eq_factorial (Γ : CurvatureGraph i) :
    canonicalWeight (k := ℝ) i Γ = ((n + 1).factorial : ℝ)⁻¹ * rawWeight i Γ := by
  simp [canonicalWeight, rawWeight, Kontsevich.GeometricWeights.canonicalEffectiveWeight,
    Kontsevich.effectiveMCWeight, Rat.smul_def]

/-- This definition contains the genuine quotient integral and the original
internal-arrow slot sign, and contains no averaged graph profile. -/
def coefficient (H : BinaryGraph (n + 2) 3) : ℝ :=
  if h : AdmissiblePair i H then
    let a := h.choose
    let s := h.choose_spec.choose
    let hs := h.choose_spec.choose_spec
    (-1 : ℝ) ^ s.val * rawWeight i (curvatureGraph i H a s hs.1 hs.2.1 hs.2.2)
  else 0

theorem outgoingAverage_zero_of_not_admissible (H : BinaryGraph (n + 2) 3)
    (hH : ¬ AdmissiblePair i H) : outgoingAverage (pairProfile i) H = 0 := by
  have hp (τ : Fin (n + 2) → Equiv.Perm (Fin 2)) :
      pairProfile i (H.permuteOutgoing (fun v ↦ (τ v).symm)) = 0 := by
    simp only [pairProfile, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    unfold canonicalProfile GraphCoefficientProfiles.pushforward
    apply Finset.sum_eq_zero
    intro D _
    apply if_neg
    intro he
    have h0 : AdmissiblePair i (H.permuteOutgoing (fun v ↦ (τ v).symm)) := by
      rw [← he]
      exact canonicalDataGraph_admissible i a D
    have h1 := admissiblePair_permuteOutgoing i _ h0 τ
    have hcancel := (outgoingGraphEquiv (fun _ : Fin (n + 2) ↦ 2) 3 τ).right_inv H
    exact hH (hcancel ▸ h1)
  simp only [outgoingAverage_apply, hp, mul_zero, Finset.sum_const_zero]

/-- The full outgoing fibre computation removes exactly one half and the
quotient MC factorial, with the remaining scalar the actual raw integral. -/
theorem coefficient_eq_average (H : BinaryGraph (n + 2) 3) :
    coefficient i H = (2 * (n + 1).factorial : ℕ) * outgoingAverage (pairProfile i) H := by
  by_cases h : AdmissiblePair i H
  · let a := h.choose
    let s := h.choose_spec.choose
    have hs := h.choose_spec.choose_spec
    rw [coefficient, dif_pos h,
      outgoingAverage_pairProfile_original i a H s hs.1 hs.2.1 hs.2.2,
      canonicalWeight_eq_factorial]
    have hf : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
    dsimp only
    push_cast
    field_simp
    rfl
  · rw [coefficient, dif_neg h, outgoingAverage_zero_of_not_admissible i H h, mul_zero]

/-- Any actual admissible extraction gives the same literal signed raw weight,
so the choice used by the total coefficient has no mathematical effect. -/
theorem coefficient_eq_extracted (H : BinaryGraph (n + 2) 3) (a s : Fin 2)
    (hi : UniqueInternalAt i H a s) (hd : CoarseDistinct i H) (hx : ExitsDistinctAt i H a s) :
    coefficient i H = (-1 : ℝ) ^ s.val * rawWeight i (curvatureGraph i H a s hi hd hx) := by
  rw [coefficient_eq_average, outgoingAverage_pairProfile_original i a H s hi hd hx,
    canonicalWeight_eq_factorial]
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
  push_cast
  field_simp

@[simp] theorem coefficient_zero_of_not_admissible (H : BinaryGraph (n + 2) 3)
    (hH : ¬ AdmissiblePair i H) : coefficient i H = 0 := by simp [coefficient,hH]

end EnvelopingIsomorphism.Deformation.GraphCurvatureExtractedCoefficient
