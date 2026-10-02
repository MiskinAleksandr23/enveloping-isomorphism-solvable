import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryFaceEdgeForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestStaticFaceForms

/-! Actual complete graph-form pullback on a strict pure-boundary forest
face, retaining every derivative of the primitive normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceForms
open Configuration ForestRadialFaceClassification PureForestSimpleCoordinates RealForestFaceForms
open PureForestSimpleCluster (lower upper)
open BoxStokes
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (a b : Fin m)
  (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hl hu hab in
theorem nativePairForm_eq_simple (p : DoubledPair (n+1) m) :
    nativePairForm hdim x o p z.val =
      (PureBoundaryFaceEdgeForms.pairForm (lower x o) (upper x o) a b p
        (coordinates hdim x o a b z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  have hn (w : ForestRadialFaceLocalization.source hdim x o) (p : DoubledPair (n+1) m) :
      PureBoundaryFaceEdgeForms.resolvedPair (lower x o) (upper x o) a b p
        (coordinates hdim x o a b w.val) ≠ 0 := by
    rw [coordinates_eq_datum hdim x o a b ho hl hu hab w]
    exact PureBoundaryFaceEdgeForms.resolvedPair_ne_zero_data _ _ _ _ _ p
  apply ForestStaticFaceForms.nativePairForm_eq_pullback hdim x o (coordinates hdim x o a b)
    (pureBoundaryClusterPairCollapses (lower x o) (upper x o))
    (PureBoundaryFaceDR.pairBase (lower x o) (upper x o) a b)
    (PureBoundaryFaceDR.pairVelocity (lower x o) (upper x o) a b)
    (fun w ↦ PureForestSimpleOverlap.ambient_coordinates hdim x o a b ho hl hu hab w)
    hn z (contDiffAt_coordinates hdim x o a b ho hl hu hab z) p
  · exact ((PureBoundaryFaceDR.contDiff_base _ _ _ _ p.val.2).sub
      (PureBoundaryFaceDR.contDiff_base _ _ _ _ p.val.1)).contDiffAt
  · exact ((PureBoundaryFaceDR.contDiff_velocity _ _ _ _ p.val.2).sub
      (PureBoundaryFaceDR.contDiff_velocity _ _ _ _ p.val.1)).contDiffAt

include ho hl hu hab in
theorem nativeEdgeForm_eq_face (e : GraphForms.Edge n m) (he : e.target ≠ Sum.inl e.source) :
    nativeEdgeForm hdim x o e.source e.target he z.val =
      (PureBoundaryClusterForms.faceEdgeForm (boundaryClusterBlock (lower x o) (upper x o)) a b e
        (coordinates hdim x o a b z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  have hs : PureBoundaryFaceEdgeForms.edgeForm (lower x o) (upper x o) a b e he
      (coordinates hdim x o a b z.val) =
      PureBoundaryClusterForms.faceEdgeForm (boundaryClusterBlock (lower x o) (upper x o)) a b e
        (coordinates hdim x o a b z.val) := by
    rw [coordinates_eq_datum hdim x o a b ho hl hu hab z]
    exact PureBoundaryFaceEdgeForms.edgeForm_eq_face_data _ _ _ _ _ e he
  rw [← hs]
  unfold nativeEdgeForm PureBoundaryFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_simple hdim x o a b ho hl hu hab z,
    nativePairForm_eq_simple hdim x o a b ho hl hu hab z]
  ext w
  rfl

include ho hl hu hab in
theorem graphForm_eq_simple {k : ℕ} (edges : Fin k → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z.val)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) z.val) =
    (PureBoundaryClusterForms.faceGraphForm (boundaryClusterBlock (lower x o) (upper x o)) a b
      (fun j ↦ ⟨(edges j).source,(edges j).target⟩) (coordinates hdim x o a b z.val)).compContinuousLinearMap
        (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (ExtractedForestChildShapes.shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o z.val))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o z.val))
        ((fderiv ℝ (faceAmbient hdim x o) z.val) (V i)))) = _
  change _ = GraphForms.topForm _ _ (fun i ↦
    (fderiv ℝ (PureBoundaryClusterForms.faceMap (boundaryClusterBlock (lower x o) (upper x o)) a b)
      (coordinates hdim x o a b z.val)) ((fderiv ℝ (coordinates hdim x o a b) z.val) (V i)))
  rw [GraphForms.topForm_apply]
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply]
  have hn := nativeEdgeForm_eq_orthant_edge hdim x o (edges j).source (edges j).target (edges j).nonloop z.val
  have hs := nativeEdgeForm_eq_face hdim x o a b ho hl hu hab z
    ⟨(edges j).source,(edges j).target⟩ (edges j).nonloop
  exact congrArg (fun ω : Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceForms
