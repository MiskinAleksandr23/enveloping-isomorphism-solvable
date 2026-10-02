import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomainEquivalence
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

/-! Actual real-boundary density in ordered product coordinates. The smaller
integrals are over the genuine increasing external chambers. The signs of
both old arbitrary enumerations remain explicit. These anchored charts cover
nonempty proper internal clusters; no completeness claim about nullary
clusters is made here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedIntegrals
open Configuration BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
open MeasureTheory
open scoped BigOperators Classical
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

abbrev RealShape := Fin (GraphForms.dimension (shapeN a S) (shapeM l u)) → ℝ
abbrev RealCoarse := Fin (GraphForms.dimension (coarseN i S) (outsideM l u + 1)) → ℝ

def orderedRealFace (hlu : l ≤ u)
    (z : RealShape (a := a) (S := S) (l := l) (u := u) × RealCoarse (i := i) (S := S) (l := l) (u := u)) :
    FaceCoordinates i a S m :=
  (orderedSplitFace hlu).symm
    ((GraphForms.realCoordinates _ _).symm z.1, (GraphForms.realCoordinates _ _).symm z.2)

theorem orderedRealFace_open_iff (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (z : RealShape (a := a) (S := S) (l := l) (u := u) × RealCoarse (i := i) (S := S) (l := l) (u := u)) :
    (BoundaryClusterFreeCoordinates.faceEmbedding (orderedRealFace hlu z)).OpenConditions l u ↔
      z ∈ GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1) := by
  rw [faceOpenConditions_iff_ordered_admissible ha hi hlu]
  simp only [orderedRealFace, ContinuousLinearEquiv.apply_symm_apply]
  rfl

variable (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → BoundaryGraphFaceFactorization.Edge n m)
    (hcount : Fintype.card {j // (edges j).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ j, (edges j).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges j).2))

def orderedShapeEdges := fun j ↦ boundaryEdge (shapePermutation l u)
  (shapeEdges (a := a) edges S hcount hnout j)

def orderedCoarseEdges (hlu : l ≤ u) := fun j ↦ boundaryEdge (coarsePermutation hlu)
  (coarseEdges (i := i) (l := l) (u := u) edges S hcount j)

def orderedFaceSign (hlu : l ≤ u) : ℝ :=
  (Equiv.Perm.sign (edgeBlockPermutation edges S hcount).symm : ℝ) *
    (tangentBlockPermutation (i := i) (a := a) (S := S) (l := l) (u := u)).sign *
    (shapePermutation l u).sign * (coarsePermutation hlu).sign

def orderedRealDensity (hlu : l ≤ u)
    (z : RealShape (a := a) (S := S) (l := l) (u := u) × RealCoarse (i := i) (S := S) (l := l) (u := u)) : ℝ :=
  nativeFaceDensity (l := l) (u := u) edges (orderedRealFace hlu z)

theorem orderedRealDensity_eq_product (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (hloop : ∀ j, (edges j).2 ≠ Sum.inl (edges j).1)
    (z : RealShape (a := a) (S := S) (l := l) (u := u) × RealCoarse (i := i) (S := S) (l := l) (u := u))
    (hz : z ∈ GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
      GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1)) :
    orderedRealDensity edges hlu z = orderedFaceSign edges hcount hlu *
      (GeometricWeights.realDensity (orderedShapeEdges edges hcount hnout) z.1 *
       GeometricWeights.realDensity (orderedCoarseEdges edges hcount hlu) z.2) := by
  have h := nativeFaceDensity_ordered hlu edges hcount hnout hloop (orderedRealFace hlu z)
    ((orderedRealFace_open_iff ha hi hlu z).mpr hz)
  simp only [orderedRealFace, ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- Fubini over exactly the two physical ordered chambers. Integrability is
required of the actual smaller densities; external relabelling invariance is
neither used nor assumed. -/
theorem integral_orderedRealDensity (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (hloop : ∀ j, (edges j).2 ≠ Sum.inl (edges j).1)
    (hshape : GeometricWeights.AbsolutelyIntegrable (orderedShapeEdges edges hcount hnout))
    (hcoarse : GeometricWeights.AbsolutelyIntegrable (orderedCoarseEdges edges hcount hlu)) :
    (∫ z in GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1),
      orderedRealDensity edges hlu z ∂volume.prod volume) =
      orderedFaceSign edges hcount hlu *
        (GeometricWeights.rawIntegral (orderedShapeEdges edges hcount hnout) *
         GeometricWeights.rawIntegral (orderedCoarseEdges edges hcount hlu)) := by
  have he := setIntegral_congr_fun (μ := volume.prod volume)
    ((GeometricWeights.measurableSet_realDomain _ _).prod (GeometricWeights.measurableSet_realDomain _ _))
    (fun z hz ↦ orderedRealDensity_eq_product edges hcount hnout ha hi hlu hloop z hz)
  rw [he, integral_const_mul]
  congr 1
  have hp : IntegrableOn (fun z ↦
      GeometricWeights.realDensity (orderedShapeEdges edges hcount hnout) z.1 *
      GeometricWeights.realDensity (orderedCoarseEdges edges hcount hlu) z.2)
      (GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
        GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1)) (volume.prod volume) := by
    change Integrable _ ((volume.prod volume).restrict _)
    rw [← Measure.prod_restrict]
    exact hshape.mul_prod hcoarse
  rw [setIntegral_prod _ hp]
  simp only [integral_const_mul, integral_mul_const, GeometricWeights.rawIntegral]

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedIntegrals
