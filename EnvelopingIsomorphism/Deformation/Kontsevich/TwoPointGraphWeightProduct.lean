import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInteriorFace
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability

/-! The true two-point circle factor with genuine coarse graph covectors.
Coarse integrability is proved, and edge and tangent permutation signs are
retained. Identifying a forest face with this product is a separate obligation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointGraphWeightProduct

open MeasureTheory Set
open scoped BigOperators

variable {n m : ℕ}

abbrev RealCoordinates := Fin (GraphForms.dimension n m) → ℝ

def coarseCovectors
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (x : RealCoordinates (n := n) (m := m)) :
    Fin (GraphForms.dimension n m) → RealCoordinates (n := n) (m := m) →L[ℝ] ℝ :=
  fun j => (GraphForms.edgeLinear (edges j)
    ((ForestGraphIntegrability.nativeCoordinates (n := n) (m := m)).symm x)).comp
      (ForestGraphIntegrability.nativeCoordinates (n := n) (m := m)).symm.toContinuousLinearMap

theorem coarseCovectors_density
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (x : RealCoordinates (n := n) (m := m)) :
    GraphFormProduct.ofCovectors (coarseCovectors edges x)
      (BoxStokes.standardBasis (GraphForms.dimension n m)) =
        GeometricWeights.realDensity edges x := by
  unfold coarseCovectors
  rw [← GraphFormProduct.graphTopForm_pullback_eq]
  change GraphForms.topForm edges _
    (fun j => (ForestGraphIntegrability.nativeCoordinates (n := n) (m := m)).symm
      (BoxStokes.standardBasis (GraphForms.dimension n m) j)) = _
  simp only [ForestGraphIntegrability.nativeCoordinates_symm_basis]
  rfl

def circleProductDensity
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n m + 1)))
    (z : RealCoordinates (n := n) (m := m) × ℝ) : ℝ :=
  GraphFormProduct.permutedProductDensity (coarseCovectors edges)
    TwoPointInteriorFace.fiberCovectors (BoxStokes.standardBasis (GraphForms.dimension n m))
    (fun _ : Fin 1 => (1 : ℝ)) σ τ z

theorem integrableOn_circleProductDensity
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n m + 1))) :
    IntegrableOn (circleProductDensity edges σ τ)
      (GeometricWeights.realDomain n m ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
  have hα : IntegrableOn
      (fun x => GraphFormProduct.ofCovectors (coarseCovectors edges x)
        (BoxStokes.standardBasis (GraphForms.dimension n m)))
      (GeometricWeights.realDomain n m) := by
    simpa only [coarseCovectors_density, GeometricWeights.AbsolutelyIntegrable] using
      ForestGraphIntegrability.absolutelyIntegrable edges
  unfold circleProductDensity IntegrableOn
  rw [Measure.volume_eq_prod]
  exact GraphFormProduct.integrableOn_permutedProductDensity (coarseCovectors edges)
      TwoPointInteriorFace.fiberCovectors (BoxStokes.standardBasis (GraphForms.dimension n m))
      (fun _ : Fin 1 => (1 : ℝ)) σ τ hα TwoPointInteriorFace.fiber_integrable

theorem integral_circleProductDensity
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n m + 1))) :
    (∫ z in GeometricWeights.realDomain n m ×ˢ Icc (0 : ℝ) (2 * Real.pi),
      circleProductDensity edges σ τ z) =
        (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
          ((2 * Real.pi) * GeometricWeights.rawIntegral edges) := by
  have hα : IntegrableOn
      (fun x => GraphFormProduct.ofCovectors (coarseCovectors edges x)
        (BoxStokes.standardBasis (GraphForms.dimension n m)))
      (GeometricWeights.realDomain n m) := by
    simpa only [coarseCovectors_density, GeometricWeights.AbsolutelyIntegrable] using
      ForestGraphIntegrability.absolutelyIntegrable edges
  simpa only [circleProductDensity, coarseCovectors_density, GeometricWeights.rawIntegral,
    Measure.volume_eq_prod] using
    TwoPointInteriorFace.integral_product_circle_permuted (coarseCovectors edges)
      (BoxStokes.standardBasis (GraphForms.dimension n m))
      (GeometricWeights.realDomain n m) volume σ τ hα

theorem circle_normalization (d : ℕ) :
    ((2 * Real.pi) ^ (d + 1))⁻¹ * (2 * Real.pi) = ((2 * Real.pi) ^ d)⁻¹ := by
  have h : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [pow_succ, mul_inv_rev]
  field_simp

theorem normalized_integral_circleProductDensity
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n m + 1))) :
    ((2 * Real.pi) ^ (GraphForms.dimension n m + 1))⁻¹ *
      (∫ z in GeometricWeights.realDomain n m ×ˢ Icc (0 : ℝ) (2 * Real.pi),
        circleProductDensity edges σ τ z) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        (((2 * Real.pi) ^ GraphForms.dimension n m)⁻¹ * GeometricWeights.rawIntegral edges) := by
  rw [integral_circleProductDensity]
  calc
    _ = (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ((((2 * Real.pi) ^ (GraphForms.dimension n m + 1))⁻¹ * (2 * Real.pi)) *
          GeometricWeights.rawIntegral edges) := by ring
    _ = _ := by rw [circle_normalization]

/-- The quotient graph's actual labelled weight is recovered from its coarse
form times the true circle form, including both displayed permutation signs. -/
theorem integral_circleProduct_eq_geometricWeight
    {q : Fin (n + 1) → ℕ} (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q)
    (σ τ : Equiv.Perm (Fin (GraphForms.dimension n m + 1))) :
    GeometricWeights.outgoingFactor q *
      (((2 * Real.pi) ^ (GraphForms.dimension n m + 1))⁻¹ *
        (∫ z in GeometricWeights.realDomain n m ×ˢ Icc (0 : ℝ) (2 * Real.pi),
          circleProductDensity (GeometricWeights.orderedEdges Γ order) σ τ z)) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        GeometricWeights.geometricWeight Γ order := by
  rw [normalized_integral_circleProductDensity, GeometricWeights.geometricWeight]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointGraphWeightProduct
