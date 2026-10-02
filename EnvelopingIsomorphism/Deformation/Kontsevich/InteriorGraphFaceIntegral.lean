import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceDimension
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAllAngularVanishing
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability

/-! Genuine product integration of a simple interior graph face. The coarse
factor uses precisely the original real coordinates of GeometricWeights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
open InteriorFiberAngleSplit ContinuousAlternatingMap GraphFormProduct Set MeasureTheory
open scoped Classical
variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev RealProductCoordinates (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  ShapeCoordinates a b S × (Fin (coarseDegree i a S m) → ℝ)

def toProduct : RealProductCoordinates i a b S m ≃L[ℝ] ProductCoordinates i a b S m :=
  (ContinuousLinearEquiv.refl ℝ (ShapeCoordinates a b S)).prodCongr
    (GraphForms.realCoordinates (coarseN i a S) m).symm.toContinuousLinearEquiv

def toAngularReal : RealProductCoordinates i a b S m → ClusterAngularCoordinates i a b S m :=
  toAngular ∘ toProduct

def faceFrame : Fin (shapeDegree a b S + coarseDegree i a S m) → RealProductCoordinates i a b S m :=
  productVectors (fiberFrame (shapeN a b S)) (BoxStokes.standardBasis _)

def realFaceDensity
    (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (x : RealProductCoordinates i a b S m) : ℝ :=
  (graphForm edges (toAngularReal x)).compContinuousLinearMap (fderiv ℝ toAngularReal x) faceFrame

private theorem toProduct_frame (j : Fin (shapeDegree a b S + coarseDegree i a S m)) :
    toProduct (faceFrame (i := i) (a := a) (b := b) (S := S) (m := m) j) =
      productVectors (fiberFrame (shapeN a b S)) (GraphForms.realBasis (coarseN i a S) m) j := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => simp [faceFrame, productVectors, toProduct]
  | inr j =>
    simp only [faceFrame, productVectors, Equiv.symm_apply_apply, Sum.elim_inr]
    apply Prod.ext
    · rfl
    · exact ForestGraphIntegrability.nativeCoordinates_symm_basis j

/-- The literal coefficient of the actual graph pullback is its two graph
factors with the constructed edge sign. The frame is shape first. -/
theorem realFaceDensity_eq_product
    (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
    (ha : a ∈ S) (hba : b ≠ a) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
    (x : RealProductCoordinates i a b S m)
    (hx : x ∈ integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) :
    realFaceDensity edges x =
      (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ) *
        (PlanarOrderedAngularForms.density (planarEdges edges hcount) (Equiv.refl _) x.1 *
          GeometricWeights.realDensity (coarseEdges edges hcount) x.2) := by
  have hadm := openConditions_toAngular ha hba (toProduct x) hx.1.2 hx.2
  have h := graphForm_product edges hcount hba (toProduct x) hadm hne
    (fiberFrame _) (GraphForms.realBasis _ _) (Equiv.refl _)
  unfold realFaceDensity toAngularReal
  rw [fderiv_comp x (contDiff_toAngular.differentiable (by simp)).differentiableAt
    toProduct.differentiableAt, toProduct.fderiv]
  change graphForm edges (toAngular (toProduct x))
    (fun j ↦ fderiv ℝ toAngular (toProduct x) (toProduct (faceFrame j))) = _
  simp_rw [toProduct_frame]
  simp only [Equiv.refl_apply, Equiv.Perm.sign_refl, Int.cast_one, Units.val_one, mul_one] at h
  convert h using 1 <;> try rfl


private theorem planar_integrable_zero {N : ℕ} (hN : 0 < N) (e : PlanarOrderedAngularForms.OrderedEdges N) :
    IntegrableOn (PlanarOrderedAngularForms.density e (Equiv.refl _)) (integrationRegion N) ∧
      (∫ x in integrationRegion N, PlanarOrderedAngularForms.density e (Equiv.refl _) x) = 0 := by
  cases N with
  | zero => omega
  | succ N => exact PlanarAllAngularVanishing.integral_eq_zero e

/-- Actual large interior-face integral in shape/coarse product coordinates.
Both L1 factors are supplied by proved global geometric integrability theorems;
there is no assumed integral, admissibility, or factorization identity. -/
theorem integral_realFaceDensity_eq_zero
    (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge n m)
    (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hlarge : 3 ≤ S.card)
    (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1) :
    IntegrableOn (realFaceDensity edges)
      (integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) ∧
    (∫ x in integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m,
      realFaceDensity edges x) = 0 := by
  have hp : 0 < shapeN a b S := by
    change 0 < Fintype.card (ClusterShapeIndex a b S)
    rw [card_clusterShapeIndex a b S ha hb hba]
    omega
  have hshape := planar_integrable_zero hp (planarEdges edges hcount)
  have hcoarse := ForestGraphIntegrability.absolutelyIntegrable (coarseEdges (i := i) edges hcount)
  let c : ℝ := (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ)
  have hprod : IntegrableOn (fun x : RealProductCoordinates i a b S m ↦
      c * (PlanarOrderedAngularForms.density (planarEdges edges hcount) (Equiv.refl _) x.1 *
        GeometricWeights.realDensity (coarseEdges edges hcount) x.2))
      (integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (hshape.1.mul_prod hcoarse).const_mul c
  have hm := (measurableSet_integrationRegion (shapeN a b S)).prod
    (GeometricWeights.measurableSet_realDomain (coarseN i a S) m)
  have heq := fun x hx ↦ realFaceDensity_eq_product edges hcount ha hba hne x hx
  refine ⟨hprod.congr_fun (fun x hx ↦ (heq x hx).symm) hm, ?_⟩
  rw [setIntegral_congr_fun hm heq, integral_const_mul, Measure.volume_eq_prod,
    setIntegral_prod_mul, hshape.2, zero_mul, mul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
