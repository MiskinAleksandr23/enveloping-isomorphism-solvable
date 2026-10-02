import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryFaceEdgeForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestStaticFaceForms

/-! Actual graph-form transport from a strict all-interior infinity forest
face to its established simple infinity chart, including every derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceForms
open Configuration ForestRadialFaceClassification InfinityForestSimpleCoordinates RealForestFaceForms
open InfinityForestSimpleCluster (lower upper)
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity) (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hq hne in
theorem nativePairForm_eq_simple (p : DoubledPair (n+1) m) :
    nativePairForm hdim x o p z.val =
      (InfinityBoundaryFaceEdgeForms.pairForm (lower x o) (upper x o) p
        (coordinates hdim x o q z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o q) z.val) := by
  apply ForestStaticFaceForms.nativePairForm_eq_pullback hdim x o (coordinates hdim x o q)
    (boundaryAnchoredInfinityPairCollapses (lower x o) (upper x o))
    (InfinityBoundaryFaceDR.pairBase (lower x o) (upper x o))
    (InfinityBoundaryFaceDR.pairVelocity (lower x o) (upper x o))
    (fun w ↦ InfinityForestSimpleOverlap.ambient_coordinates hdim x o q ho hq hne w)
    (fun w p ↦ InfinityBoundaryFaceEdgeForms.resolvedPair_ne_zero _ _ p _
      (coordinates_mem_source hdim x o q ho hq hne w)) z
    (contDiffAt_coordinates hdim x o q ho hq hne z) p
  · exact ((InfinityBoundaryFaceDR.contDiff_base _ _ p.val.2).sub
      (InfinityBoundaryFaceDR.contDiff_base _ _ p.val.1)).contDiffAt
  · exact ((InfinityBoundaryFaceDR.contDiff_velocity _ _ p.val.2).sub
      (InfinityBoundaryFaceDR.contDiff_velocity _ _ p.val.1)).contDiffAt

include ho hq hne in
theorem nativeEdgeForm_eq_extended_face (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) : nativeEdgeForm hdim x o j v hv z.val =
      ((BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm (lower x o) (upper x o) j v
        (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))).compContinuousLinearMap
          BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding).compContinuousLinearMap
            (fderiv ℝ (coordinates hdim x o q) z.val) := by
  rw [← InfinityBoundaryFaceEdgeForms.edgeForm_eq_extended_face (lower x o) (upper x o) j v hv _
    (coordinates_mem_source hdim x o q ho hq hne z)]
  unfold nativeEdgeForm InfinityBoundaryFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_simple hdim x o q ho hq hne z, nativePairForm_eq_simple hdim x o q ho hq hne z]
  ext w
  rfl

include ho hq hne in
theorem graphForm_eq_simple {k : ℕ} (edges : Fin k → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z.val)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) z.val) =
    (InfinityBoundaryGraphFactorization.graphForm (l := lower x o) (u := upper x o)
      (fun j ↦ ((edges j).source,(edges j).target))
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))).compContinuousLinearMap
        (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding.comp (fderiv ℝ (coordinates hdim x o q) z.val)) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (ExtractedForestChildShapes.shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o z.val))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o z.val))
        ((fderiv ℝ (faceAmbient hdim x o) z.val) (V i)))) =
    Matrix.det (fun i j ↦ InfinityBoundaryGraphFactorization.edgeLinear (l := lower x o) (u := upper x o)
      ((edges j).source,(edges j).target)
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding ((fderiv ℝ (coordinates hdim x o q) z.val) (V i))))
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply, InfinityBoundaryGraphFactorization.edgeLinear_apply]
  have hn := nativeEdgeForm_eq_orthant_edge hdim x o (edges j).source (edges j).target (edges j).nonloop z.val
  have hs := nativeEdgeForm_eq_extended_face hdim x o q ho hq hne z (edges j).source (edges j).target (edges j).nonloop
  exact congrArg (fun ω : Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceForms
