import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterFaceEdgeForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphFaceFactorization

/-! Actual angular edge pullback on a strict proper-real native forest face.
Equality follows from the full-DR identity, with all normalization derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceForms
open Configuration ExtractedForestParameters ExtractedForestChildShapes ForestOrthantRealization
open ForestRadialFaceClassification ForestDirectionRatioCoordinates RealForestSimpleCoordinates
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open BoxStokes Filter
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1))

def nativeUnit (p : DoubledPair (n+1) m) (w : Coord r) : ℂ :=
  pairUnit (tree 0 x) (canonicalLeaf 0 x) (ambientParameters hdim x o w) p

theorem contDiff_nativeUnit (p : DoubledPair (n+1) m) : ContDiff ℝ ⊤ (nativeUnit hdim x o p) :=
  (contDiff_pairUnit _ _ p).comp (contDiff_ambientParameters hdim x o)

def nativePairForm (p : DoubledPair (n+1) m) (w : Coord r) : Coord r [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (nativeUnit hdim x o p) w

def nativeEdgeForm (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (w : Coord r) : Coord r [⋀^Fin 1]→L[ℝ] ℝ :=
  nativePairForm hdim x o (harmonicNumeratorPair j v hv) w -
    nativePairForm hdim x o (harmonicDenominatorPair j v) w

def parameterRealization (w : Coord r) : ForestGraphForms.ParameterSpace (shapeData 0 x) :=
  ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o w)

theorem contDiff_parameterRealization : ContDiff ℝ ⊤ (parameterRealization hdim x o) :=
  (ForestOrthantGraphForms.contDiff_reflectedRealization 0 x).comp
    (ForestRadialFaceImmersion.contDiff_faceAmbient hdim x o)

theorem nativeUnit_eq_parameter (p : DoubledPair (n+1) m) :
    nativeUnit hdim x o p = ForestGraphForms.unit (shapeData 0 x) p ∘ parameterRealization hdim x o := by
  funext w
  change _ = pairUnit (tree 0 x) (canonicalLeaf 0 x)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o w)).val p
  rw [ForestOrthantGraphForms.reflectedRealization_val]
  rfl

theorem nativePairForm_eq_parameter (p : DoubledPair (n+1) m) (w : Coord r) :
    nativePairForm hdim x o p w =
      (angularPullback (ForestGraphForms.unit (shapeData 0 x) p) (parameterRealization hdim x o w)).compContinuousLinearMap
        (fderiv ℝ (parameterRealization hdim x o) w) := by
  rw [nativePairForm, nativeUnit_eq_parameter]
  exact angularPullback_comp_differentiable _ _ w
    ((ForestGraphForms.contDiff_unit _ _).contDiffAt.differentiableAt (by simp))
    ((contDiff_parameterRealization hdim x o).contDiffAt.differentiableAt (by simp))

/-- This is the restriction of the original forest unit edge form to the
actual native face; the intermediate pair notation changes no form. -/
theorem nativeEdgeForm_eq_orthant_edge (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) (w : Coord r) :
    nativeEdgeForm hdim x o j v hv w =
      ((ForestGraphForms.edgeForm (shapeData 0 x) j v hv
        (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o w))).compContinuousLinearMap
          (fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o w))).compContinuousLinearMap
            (fderiv ℝ (faceAmbient hdim x o) w) := by
  unfold nativeEdgeForm
  rw [nativePairForm_eq_parameter, nativePairForm_eq_parameter]
  have hd : fderiv ℝ (parameterRealization hdim x o) w =
      (fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o w)).comp
        (fderiv ℝ (faceAmbient hdim x o) w) :=
    fderiv_comp w
      ((ForestOrthantGraphForms.contDiff_reflectedRealization 0 x).contDiffAt.differentiableAt (by simp))
      ((ForestRadialFaceImmersion.contDiff_faceAmbient hdim x o).contDiffAt.differentiableAt (by simp))
  rw [hd]
  ext V
  rfl

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem nativeUnit_ne_zero (p : DoubledPair (n+1) m) : nativeUnit hdim x o p z.val ≠ 0 :=
  (RealForestResolvedCoordinates.nativeDomain hdim x o z).property.2 p

include ho ha hb hne in
theorem nativePhase_eq_simple (p : DoubledPair (n+1) m) :
    (complexPhase (nativeUnit hdim x o p z.val) : ℂ) =
      (complexPhase (BoundaryClusterFaceEdgeForms.resolvedPair (lower x o) (upper x o) p
        (coordinates hdim x o a b z.val)) : ℂ) := by
  have h := congrArg (fun d : CompactDRCoordinates.Ambient (n+1) m ↦ d.1 p)
    (RealForestSimpleOverlap.ambient_coordinates hdim x o a b ho ha hb hne z)
  change BoundaryClusterFaceDR.direction (lower x o) (upper x o) p (coordinates hdim x o a b z.val) =
    (complexPhase (nativeUnit hdim x o p z.val) : ℂ) at h
  rw [BoundaryClusterFaceEdgeForms.direction_eq_phase] at h
  exact h.symm

include ho ha hb hne in
theorem nativePairForm_eq_simple (p : DoubledPair (n+1) m) :
    nativePairForm hdim x o p z.val =
      (BoundaryClusterFaceEdgeForms.pairForm (lower x o) (upper x o) p
        (coordinates hdim x o a b z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  have hf := (contDiff_nativeUnit hdim x o p).contDiffAt (x := z.val)
  have hc := contDiffAt_coordinates hdim x o a b ho ha hb z
  have hs := (BoundaryClusterFaceEdgeForms.contDiff_resolvedPair (i := b) (a := a)
    (S := labelsSet x o) (lower x o) (upper x o) p).contDiffAt (x := coordinates hdim x o a b z.val)
  have hsn := BoundaryClusterFaceEdgeForms.resolvedPair_ne_zero (lower x o) (upper x o) p _
    (coordinates_mem_source hdim x o a b ho ha hb hne z)
  have he : (fun w ↦ (complexPhase (nativeUnit hdim x o p w) : ℂ)) =ᶠ[𝓝 z.val]
      (fun w ↦ (complexPhase (BoundaryClusterFaceEdgeForms.resolvedPair (lower x o) (upper x o) p
        (coordinates hdim x o a b w)) : ℂ)) :=
    eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ nativePhase_eq_simple hdim x o a b ho ha hb hne ⟨w,hw⟩ p)
  unfold nativePairForm BoundaryClusterFaceEdgeForms.pairForm
  rw [angularPullback_eq_of_complexPhase_eventually hf (hs.comp z.val hc)
    (nativeUnit_ne_zero hdim x o z p) hsn he]
  exact angularPullback_comp_differentiable _ _ z.val
    (hs.differentiableAt (by simp)) (hc.differentiableAt (by simp))

include ho ha hb hne in
/-- The genuine native edge one-form is the pullback of the already defined
simple face restriction, not a new replacement graph form. -/
theorem nativeEdgeForm_eq_extended_face (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) :
    nativeEdgeForm hdim x o j v hv z.val =
      ((BoundaryClusterFreeCoordinates.extendedEdgeForm (lower x o) (upper x o) j v
        (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))).compContinuousLinearMap
          BoundaryClusterFreeCoordinates.faceEmbedding).compContinuousLinearMap
            (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  rw [← BoundaryClusterFaceEdgeForms.edgeForm_eq_extended_face (lower x o) (upper x o) j v hv _
    (coordinates_mem_source hdim x o a b ho ha hb hne z)]
  unfold nativeEdgeForm BoundaryClusterFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_simple hdim x o a b ho ha hb hne z,
    nativePairForm_eq_simple hdim x o a b ho ha hb hne z]
  ext w
  rfl

include ho ha hb hne in
/-- The determinant graph form in native forest coordinates is the pullback
of the literal simple-cluster graph form used by boundary integral matching. -/
theorem graphForm_eq_simple {q : ℕ} (edges : Fin q → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z.val)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) z.val) =
    (BoundaryGraphFaceFactorization.graphForm (l := lower x o) (u := upper x o)
      (fun j ↦ ((edges j).source, (edges j).target))
      (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))).compContinuousLinearMap
        (BoundaryClusterFreeCoordinates.faceEmbedding.comp (fderiv ℝ (coordinates hdim x o a b) z.val)) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o z.val))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o z.val))
        ((fderiv ℝ (faceAmbient hdim x o) z.val) (V i)))) =
    Matrix.det (fun i j ↦ BoundaryGraphFaceFactorization.edgeLinear (l := lower x o) (u := upper x o)
      ((edges j).source, (edges j).target)
      (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))
      (BoundaryClusterFreeCoordinates.faceEmbedding ((fderiv ℝ (coordinates hdim x o a b) z.val) (V i))))
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply]
  change _ = BoundaryGraphFaceFactorization.formLinear _ _
  rw [BoundaryGraphFaceFactorization.formLinear_apply]
  have hn := nativeEdgeForm_eq_orthant_edge hdim x o (edges j).source (edges j).target (edges j).nonloop z.val
  have hs := nativeEdgeForm_eq_extended_face hdim x o a b ho ha hb hne z
    (edges j).source (edges j).target (edges j).nonloop
  exact congrArg (fun ω : Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceForms
