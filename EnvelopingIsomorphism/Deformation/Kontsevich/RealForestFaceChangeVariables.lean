import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeTransport
import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables

/-! The genuine determinant and Lebesgue change of variables for the proper
real forest face, in the inherited simple-face basis used by native matching. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceChangeVariables
open Configuration RealForestSimpleCoordinates RealForestSimpleOverlap
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestFaceForms BoundaryGraphFaceFactorization
open ForestRadialFaceClassification BoxStokes MeasureTheory Set
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (a b : Fin (n+1)) (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

include hdim ha hb in
theorem dimension_eq : shapeDegree a (labelsSet x o) (lower x o) (upper x o) +
    coarseDegree b (labelsSet x o) (lower x o) (upper x o) = r := by
  rw [face_degree_eq ha hb]
  dsimp [GraphForms.dimension] at hdim
  omega

/-- Exactly the inherited native face basis, reindexed only by the proved
vertex-count equality. -/
def simpleCoordinates : BoundaryClusterFreeCoordinates.FaceCoordinates b a (labelsSet x o) m ≃L[ℝ] Coord r :=
  (BoundaryGraphNativeTransport.nativeCoordinates (l := lower x o) (u := upper x o)).trans
    (ForestGlobalGraphStokes.coordinateCast (dimension_eq hdim x o a b ha hb))

def map (w : Coord r) : Coord r := simpleCoordinates hdim x o a b ha hb (coordinates hdim x o a b w)

def jacobian (w : Coord r) : ℝ := (fderiv ℝ (map hdim x o a b ha hb) w).det

variable (ho : RealForestCoarsePositions.IsFixed x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho in
theorem contDiffAt_map : ContDiffAt ℝ ⊤ (map hdim x o a b ha hb) z.val :=
  (simpleCoordinates hdim x o a b ha hb).contDiff.contDiffAt.comp z.val
    (contDiffAt_coordinates hdim x o a b ho ha hb z)

include ho hne in
theorem jacobian_ne_zero : jacobian hdim x o a b ha hb z.val ≠ 0 := by
  have hd := ((simpleCoordinates hdim x o a b ha hb).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho ha hb z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (map hdim x o a b ha hb) z.val = _ at hd
  unfold jacobian
  rw [hd]
  let e := LinearEquiv.ofBijective
    (((simpleCoordinates hdim x o a b ha hb).toContinuousLinearMap.comp
      (fderiv ℝ (coordinates hdim x o a b) z.val)).toLinearMap)
    ((simpleCoordinates hdim x o a b ha hb).bijective.comp
      (differential_bijective hdim x o a b ho ha hb hne z))
  exact e.isUnit_det'.ne_zero

def chart : OpenPartialHomeomorph (Coord r) (Coord r) :=
  (localChart hdim x o a b ho ha hb hne z).trans
    (simpleCoordinates hdim x o a b ha hb).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem chart_source : (chart hdim x o a b ha hb ho hne z).source =
    (localChart hdim x o a b ho ha hb hne z).source := by
  simp only [chart, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

@[simp] theorem chart_apply (w : Coord r) : chart hdim x o a b ha hb ho hne z w = map hdim x o a b ha hb w := rfl

theorem chart_contDiffAt {w : Coord r} (hw : w ∈ (chart hdim x o a b ha hb ho hne z).source) :
    ContDiffAt ℝ ⊤ (chart hdim x o a b ha hb ho hne z) w := by
  have hs := localChart_source_subset hdim x o a b ho ha hb hne z ((chart_source ..) ▸ hw)
  exact contDiffAt_map hdim x o a b ha hb ho ⟨w,hs⟩

/-- Native Lebesgue measure transforms by the absolute determinant of the
actual face map on every measurable subset of the constructed chart. -/
theorem integral_image (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (chart hdim x o a b ha hb ho hne z).source) (g : Coord r → ℝ) :
    (∫ y in chart hdim x o a b ha hb ho hne z '' s, g y) =
      ∫ w in s, |jacobian hdim x o a b ha hb w| * g (map hdim x o a b ha hb w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f' := fun w ↦ fderiv ℝ (chart hdim x o a b ha hb ho hne z) w)]
  · rfl
  · intro w hw
    exact ((chart_contDiffAt hdim x o a b ha hb ho hne z (hsub hw)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (chart hdim x o a b ha hb ho hne z).injOn.mono hsub

theorem integrableOn_image_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ (chart hdim x o a b ha hb ho hne z).source) (g : Coord r → ℝ) :
    IntegrableOn g (chart hdim x o a b ha hb ho hne z '' s) ↔
      IntegrableOn (fun w ↦ |jacobian hdim x o a b ha hb w| * g (map hdim x o a b ha hb w)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f' := fun w ↦ fderiv ℝ (chart hdim x o a b ha hb ho hne z) w)]
  · rfl
  · intro w hw
    exact ((chart_contDiffAt hdim x o a b ha hb ho hne z (hsub hw)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (chart hdim x o a b ha hb ho hne z).injOn.mono hsub

def simpleForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun y ↦ (BoundaryGraphFaceFactorization.graphForm (l := lower x o) (u := upper x o)
    (fun j ↦ ((edges j).source, (edges j).target))
    (BoundaryClusterFreeCoordinates.faceEmbedding ((simpleCoordinates hdim x o a b ha hb).symm y))).compContinuousLinearMap
      (BoundaryClusterFreeCoordinates.faceEmbedding.comp (simpleCoordinates hdim x o a b ha hb).symm.toContinuousLinearMap)

def nativeForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun w ↦ (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o w)).compContinuousLinearMap
    (fderiv ℝ (faceAmbient hdim x o) w)

include ho hne in
theorem nativeForm_eq_pullback (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    nativeForm hdim x o edges z.val =
      OrientedFormChangeVariables.pullback (map hdim x o a b ha hb)
        (simpleForm hdim x o a b ha hb edges) z.val := by
  rw [nativeForm, graphForm_eq_simple hdim x o a b ho ha hb hne z]
  unfold OrientedFormChangeVariables.pullback simpleForm map
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have hd := ((simpleCoordinates hdim x o a b ha hb).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho ha hb z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun w ↦ simpleCoordinates hdim x o a b ha hb (coordinates hdim x o a b w)) z.val = _ at hd
  rw [hd]
  ext V
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  simp

include ho hne in
/-- The actual signed native coefficient has the actual derivative determinant,
not its absolute value. This is the pointwise input to outward-sign assembly. -/
theorem native_density_eq_jacobian (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    OrientedFormChangeVariables.density (nativeForm hdim x o edges) z.val =
      jacobian hdim x o a b ha hb z.val *
        OrientedFormChangeVariables.density (simpleForm hdim x o a b ha hb edges)
          (map hdim x o a b ha hb z.val) := by
  unfold OrientedFormChangeVariables.density
  rw [nativeForm_eq_pullback hdim x o a b ha hb ho hne z]
  exact OrientedFormChangeVariables.density_pullback _ _ _

include ho hne in
theorem map_injective_on : Set.InjOn (map hdim x o a b ha hb)
    (ForestRadialFaceLocalization.source hdim x o) := by
  intro w hw v hv he
  exact RealForestSimpleEmbedding.coordinates_injective_on hdim x o a b ho ha hb hne hw hv
    ((simpleCoordinates hdim x o a b ha hb).injective he)

include ho hne in
/-- The actual face map is globally injective on the localized source, so its
Lebesgue change of variables needs no auxiliary cover of IFT neighborhoods. -/
theorem integral_image_source (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    (∫ y in map hdim x o a b ha hb '' s, g y) =
      ∫ w in s, |jacobian hdim x o a b ha hb w| * g (map hdim x o a b ha hb w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f' := fun w ↦ fderiv ℝ (map hdim x o a b ha hb) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o a b ha hb ho ⟨w,hsub hw⟩).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o a b ha hb ho hne).mono hsub

include ho hne in
theorem integrableOn_image_source_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    IntegrableOn g (map hdim x o a b ha hb '' s) ↔
      IntegrableOn (fun w ↦ |jacobian hdim x o a b ha hb w| * g (map hdim x o a b ha hb w)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f' := fun w ↦ fderiv ℝ (map hdim x o a b ha hb) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o a b ha hb ho ⟨w,hsub hw⟩).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o a b ha hb ho hne).mono hsub

def inverseReal (y : Coord r) : Coord r :=
  RealForestSimpleOverlap.inverse hdim x o a b ((simpleCoordinates hdim x o a b ha hb).symm y)

include ho hne in
theorem inverseReal_map : inverseReal hdim x o a b ha hb (map hdim x o a b ha hb z.val) = z.val := by
  rw [inverseReal, map, ContinuousLinearEquiv.symm_apply_apply]
  exact inverse_coordinates hdim x o a b ho ha hb hne z

include ho hne in
/-- Weighted actual graph-form transport on any measurable native source
subset with its true determinant sign. No scalar boundary relation is used. -/
theorem signed_weighted_graph_integral (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (ε : ℝ) (hε : ∀ w ∈ s, ε * jacobian hdim x o a b ha hb w = |jacobian hdim x o a b ha hb w|)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    ε * (∫ w in s, κ w * OrientedFormChangeVariables.density (nativeForm hdim x o edges) w) =
      ∫ y in map hdim x o a b ha hb '' s,
        κ (inverseReal hdim x o a b ha hb y) *
          OrientedFormChangeVariables.density (simpleForm hdim x o a b ha hb edges) y := by
  rw [← integral_const_mul, integral_image_source hdim x o a b ha hb ho hne s hs hsub]
  apply setIntegral_congr_fun hs
  intro w hw
  dsimp only
  rw [inverseReal_map hdim x o a b ha hb ho hne ⟨w,hsub hw⟩,
    native_density_eq_jacobian hdim x o a b ha hb ho hne ⟨w,hsub hw⟩, ← hε w hw]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceChangeVariables
