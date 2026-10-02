import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointGraphWeightProduct

/-! The literal simple two-point face density has the actual circle integral
2π times the genuine coarse graph integral, with its native edge-order sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointActualFaceIntegral
open InteriorFiberAngleSplit InteriorGraphFaceCoordinates GraphFormProduct
open Set MeasureTheory ContinuousAlternatingMap
open scoped Classical

theorem shapeEdgeForm_zero (s t : Point 0) (η : Shape 0) : shapeEdgeForm s t η = 0 := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv]
  simp

theorem rotatedEdgeForm_twoPoint (s t : Point 0) (hst : s ≠ t) (x : Parameters 0) :
    rotatedEdgeForm s t x = dtheta 0 := by
  have hx : x.2 ∈ shapeConfiguration 0 := by simp
  rw [rotatedEdgeForm_split_on_configuration x hx s t hst, shapeEdgeForm_zero]
  have hz : (0 : Shape 0 [⋀^Fin 1]→L[ℝ] ℝ).compContinuousLinearMap
      (ContinuousLinearMap.snd ℝ ℝ (Shape 0)) = 0 := by ext v; rfl
  rw [hz, add_zero]

theorem planar_density_twoPoint (e : PlanarOrderedAngularForms.OrderedEdges 0)
    (he : ∀ j, (e j).1 ≠ (e j).2) (σ : Equiv.Perm (Point 0)) (x : Parameters 0) :
    PlanarOrderedAngularForms.density e σ x = 1 := by
  rw [PlanarOrderedAngularForms.density_eq_det]
  change Matrix.det (fun r c : Fin 1 => _) = 1
  rw [Matrix.det_fin_one, relabeledEdgeForm_eq,
    rotatedEdgeForm_twoPoint _ _ (σ.symm.injective.ne (he 0))]
  rfl

theorem planar_density_of_zero {N : ℕ} (hN : N = 0) (e : PlanarOrderedAngularForms.OrderedEdges N)
    (he : ∀ j, (e j).1 ≠ (e j).2) (x : Parameters N) :
    PlanarOrderedAngularForms.density e (Equiv.refl _) x = 1 := by
  subst N
  exact planar_density_twoPoint e he _ x

theorem integral_one_region_zero : (∫ _ in integrationRegion 0, (1 : ℝ)) = 2 * Real.pi := by
  have h := integral_two_point_fiber (fun j : Fin (Dim 0) => Fin.elim0 j)
  simpa only [fiberDensity_eq_shapeDensity, shapeDensity_zero_dim] using h

theorem integrable_one_region_zero : IntegrableOn (fun _ : Parameters 0 => (1 : ℝ)) (integrationRegion 0) := by
  let e : Edges 0 := fun j => Fin.elim0 j
  have hshape : IntegrableOn (shapeDensity e) (shapeConfiguration 0) := by
    have heq : shapeDensity e = fun _ => (1 : ℝ) := funext (shapeDensity_zero_dim e)
    rw [heq, shapeConfiguration_zero_dim, IntegrableOn, Measure.restrict_univ]
    haveI : IsFiniteMeasure (volume : Measure (Shape 0)) := by
      constructor
      simp [volume_pi]
    exact integrable_const (1 : ℝ)
  have heq : fiberDensity e = fun _ => (1 : ℝ) := by
    funext x
    rw [fiberDensity_eq_shapeDensity, shapeDensity_zero_dim]
  simpa only [heq] using (integrableOn_fiberDensity_iff e).mpr hshape

theorem integral_one_region {N : ℕ} (hN : N = 0) :
    (∫ _ in integrationRegion N, (1 : ℝ)) = 2 * Real.pi := by
  subst N
  exact integral_one_region_zero

theorem integrable_one_region {N : ℕ} (hN : N = 0) :
    IntegrableOn (fun _ : Parameters N => (1 : ℝ)) (integrationRegion N) := by
  subst N
  exact integrable_one_region_zero

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
  (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → InteriorGraphFaceCoordinates.Edge n m)
  (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hS : S.card = 2)
  (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)

include ha hb hba hS

theorem shapeN_eq_zero : shapeN a b S = 0 := by
  change Fintype.card (ClusterShapeIndex a b S) = 0
  rw [card_clusterShapeIndex a b S ha hb hba, hS]

include hne

theorem realFaceDensity_eq_coarse
    (x : RealProductCoordinates i a b S m)
    (hx : x ∈ integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) :
    realFaceDensity edges x =
      (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ) *
        GeometricWeights.realDensity (coarseEdges edges hcount) x.2 := by
  rw [realFaceDensity_eq_product edges hcount ha hba hne x hx]
  rw [planar_density_of_zero (shapeN_eq_zero ha hb hba hS)]
  · simp
  · intro j
    exact planarEdge_nonloop _ ((internalEnum edges hcount).symm j).property (hne _)

/-- No circle-density, integrability, or coefficient identity is assumed. -/
theorem integral_realFaceDensity
    : IntegrableOn (realFaceDensity edges)
        (integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) ∧
      (∫ x in integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m,
        realFaceDensity edges x) =
        (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ) *
          ((2 * Real.pi) * GeometricWeights.rawIntegral (coarseEdges edges hcount)) := by
  let c : ℝ := (Equiv.Perm.sign (edgeBlockPermutation edges hcount).symm : ℝ)
  have hshape := integrable_one_region (shapeN_eq_zero ha hb hba hS)
  have hcoarse := ForestGraphIntegrability.absolutelyIntegrable (coarseEdges (i := i) edges hcount)
  have hprod : IntegrableOn (fun x : RealProductCoordinates i a b S m =>
      c * ((1 : ℝ) * GeometricWeights.realDensity (coarseEdges edges hcount) x.2))
      (integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (hshape.mul_prod hcoarse).const_mul c
  have hm := (measurableSet_integrationRegion (shapeN a b S)).prod
    (GeometricWeights.measurableSet_realDomain (coarseN i a S) m)
  have heq := fun x hx => realFaceDensity_eq_coarse edges hcount ha hb hba hS hne x hx
  refine ⟨hprod.congr_fun (fun x hx => by simpa only [one_mul] using (heq x hx).symm) hm, ?_⟩
  rw [setIntegral_congr_fun hm heq, integral_const_mul, Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure (ShapeCoordinates a b S)))
    (ν := (volume : Measure (Fin (coarseDegree i a S m) → ℝ)))
    (fun _ => (1 : ℝ)) (GeometricWeights.realDensity (coarseEdges (i := i) edges hcount))
    (integrationRegion (shapeN a b S)) (GeometricWeights.realDomain (coarseN i a S) m)
  simp only [one_mul] at h
  rw [h, integral_one_region (shapeN_eq_zero ha hb hba hS)]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointActualFaceIntegral
