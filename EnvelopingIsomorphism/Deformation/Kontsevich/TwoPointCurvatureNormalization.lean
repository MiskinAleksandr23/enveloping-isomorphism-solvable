import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointGraphWeightProduct
import EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedGraphTaylorCoefficients

/-! Actual outgoing factorials for the two-bivector contraction. The factor
3/2 is retained before averaging the six ordered Schouten splits. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCurvatureNormalization

open scoped BigOperators Classical

theorem binary_outgoingFactor (n : ℕ) :
    GeometricWeights.outgoingFactor (fun _ : Fin (n + 1) => 2) =
      ((2 : ℝ)⁻¹) ^ (n + 1) := by
  simp [GeometricWeights.outgoingFactor, inv_pow]

theorem curvature_outgoingFactor {n : ℕ} (i : Fin (n + 1)) :
    GeometricWeights.outgoingFactor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) =
      ((2 : ℝ)⁻¹) ^ (n + 1) * (3 : ℝ)⁻¹ := by
  have h (v : Fin (n + 1)) :
      (((Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i v).factorial : ℝ)⁻¹) =
        (2 : ℝ)⁻¹ * (if v = i then (3 : ℝ)⁻¹ else 1) := by
    by_cases hv : v = i <;>
      norm_num [Gauge.PlacedMixedGraphTaylorCoefficients.arities, hv]
  simp only [GeometricWeights.outgoingFactor, h, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.prod_ite_eq']

theorem binary_curvature_factor {n : ℕ} (i : Fin (n + 1)) :
    GeometricWeights.outgoingFactor (fun _ : Fin (n + 2) => 2) =
      (3 / 2 : ℝ) *
        GeometricWeights.outgoingFactor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 3 i) := by
  rw [binary_outgoingFactor (n + 1), curvature_outgoingFactor i, pow_succ]
  norm_num
  ring

theorem normalized_circle_product {n : ℕ} (i : Fin (n + 1))
    (Γ : Gauge.PlacedMixedGraphTaylorCoefficients.Graph 3 i)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n 3 + 1))) :
    GeometricWeights.outgoingFactor (fun _ : Fin (n + 2) => 2) *
      (((2 * Real.pi) ^ (GraphForms.dimension n 3 + 1))⁻¹ *
        (∫ z in GeometricWeights.realDomain n 3 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
          TwoPointGraphWeightProduct.circleProductDensity
            (GeometricWeights.orderedEdges Γ
              (GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i)))
            σ τ z)) =
      (3 / 2 : ℝ) * (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        GeometricWeights.canonicalWeight Γ (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 3 i) := by
  rw [binary_curvature_factor i, mul_assoc,
    TwoPointGraphWeightProduct.integral_circleProduct_eq_geometricWeight]
  simp only [GeometricWeights.canonicalWeight]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointCurvatureNormalization
