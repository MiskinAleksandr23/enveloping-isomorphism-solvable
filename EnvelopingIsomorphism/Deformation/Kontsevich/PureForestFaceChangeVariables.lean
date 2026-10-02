import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestFaceCutoffIntegrability

/-! Actual Lebesgue and cutoff transport for the surviving two-point pure
boundary face, in the exact frame used by its geometric-weight endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceChangeVariables
open Configuration PureForestSimpleCoordinates ForestRadialFaceClassification BoxStokes MeasureTheory Set
open PureForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (a b : Fin m)
  (ho : kind 0 x o = .pureBoundary)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)

include hdim ho hl hu hab hcard in
theorem dimension_eq : PureBoundaryGraphIntegral.Degree (n := n) (l := lower x o) (u := upper x o) = r := by
  have h := (PureBoundaryGraphIntegral.faceCoordinates (n := n) (ForestRadialClusterLabels.block_order 0 x _)
    a b (PureForestSimpleCluster.left_mem x o a b hl hu hab)
    (PureForestSimpleCluster.right_mem x o a b hl hu hab) hab.ne hcard).toLinearEquiv.finrank_eq
  have hf := PureForestSimpleOverlap.finrank_face hdim x o a b ho hl hu hab
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at h
  exact h.symm.trans hf

def simpleCoordinates : PureForestSimpleOverlap.Face x o a b ≃L[ℝ] Coord r :=
  (PureBoundaryGraphIntegral.faceCoordinates (ForestRadialClusterLabels.block_order 0 x _)
    a b (PureForestSimpleCluster.left_mem x o a b hl hu hab)
    (PureForestSimpleCluster.right_mem x o a b hl hu hab) hab.ne hcard).trans
    (ForestGlobalGraphStokes.coordinateCast (dimension_eq hdim x o a b ho hl hu hab hcard))

def simpleFaceForm {k : ℕ} (edges : Fin k → ForestGraphTopForms.Edge (n+1) m)
    (y : PureForestSimpleOverlap.Face x o a b) :=
  PureBoundaryClusterForms.faceGraphForm (boundaryClusterBlock (lower x o) (upper x o)) a b
    (fun j ↦ ⟨(edges j).source,(edges j).target⟩) y


def map (w : Coord r) : Coord r := simpleCoordinates hdim x o a b ho hl hu hab hcard (coordinates hdim x o a b w)
def jacobian (w : Coord r) : ℝ := (fderiv ℝ (map hdim x o a b ho hl hu hab hcard) w).det

def inverseReal (y : Coord r) : Coord r := PureForestSimpleOverlap.inverse hdim x o a b ((simpleCoordinates hdim x o a b ho hl hu hab hcard).symm y)

variable (z : ForestRadialFaceLocalization.source hdim x o)

include ho hl hu hab hcard in
theorem contDiffAt_map : ContDiffAt ℝ ⊤ (map hdim x o a b ho hl hu hab hcard) z.val :=
  (simpleCoordinates hdim x o a b ho hl hu hab hcard).contDiff.contDiffAt.comp z.val
    (contDiffAt_coordinates hdim x o a b ho hl hu hab z)

include ho hl hu hab hcard in
theorem inverseReal_map : inverseReal hdim x o a b ho hl hu hab hcard (map hdim x o a b ho hl hu hab hcard z.val) = z.val := by
  rw [inverseReal, map, ContinuousLinearEquiv.symm_apply_apply]
  exact PureForestSimpleOverlap.inverse_coordinates hdim x o a b ho hl hu hab z

include ho hl hu hab hcard in
theorem map_injective_on : Set.InjOn (map hdim x o a b ho hl hu hab hcard) (ForestRadialFaceLocalization.source hdim x o) := by
  intro w hw v hv he
  have h := congrArg (inverseReal hdim x o a b ho hl hu hab hcard) he
  rw [inverseReal_map hdim x o a b ho hl hu hab hcard ⟨w,hw⟩, inverseReal_map hdim x o a b ho hl hu hab hcard ⟨v,hv⟩] at h
  exact h

include ho hl hu hab hcard in
theorem jacobian_ne_zero : jacobian hdim x o a b ho hl hu hab hcard z.val ≠ 0 := by
  have hd := ((simpleCoordinates hdim x o a b ho hl hu hab hcard).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho hl hu hab z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (map hdim x o a b ho hl hu hab hcard) z.val = _ at hd
  unfold jacobian
  rw [hd]
  let e := LinearEquiv.ofBijective
    (((simpleCoordinates hdim x o a b ho hl hu hab hcard).toContinuousLinearMap.comp
      (fderiv ℝ (coordinates hdim x o a b) z.val)).toLinearMap)
    ((simpleCoordinates hdim x o a b ho hl hu hab hcard).bijective.comp (PureForestSimpleOverlap.differential_bijective hdim x o a b ho hl hu hab z))
  exact e.isUnit_det'.ne_zero

include ho hl hu hab hcard in
theorem integral_image_source (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    (∫ y in map hdim x o a b ho hl hu hab hcard '' s, g y) = ∫ w in s, |jacobian hdim x o a b ho hl hu hab hcard w| * g (map hdim x o a b ho hl hu hab hcard w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (map hdim x o a b ho hl hu hab hcard) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o a b ho hl hu hab hcard).mono hsub

include ho hl hu hab hcard in
theorem integrableOn_image_source_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    IntegrableOn g (map hdim x o a b ho hl hu hab hcard '' s) ↔
      IntegrableOn (fun w ↦ |jacobian hdim x o a b ho hl hu hab hcard w| * g (map hdim x o a b ho hl hu hab hcard w)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (map hdim x o a b ho hl hu hab hcard) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o a b ho hl hu hab hcard).mono hsub

def nativeForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun w ↦ (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o w)).compContinuousLinearMap
    (fderiv ℝ (faceAmbient hdim x o) w)

def simpleForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun y ↦ (simpleFaceForm x o a b edges ((simpleCoordinates hdim x o a b ho hl hu hab hcard).symm y)).compContinuousLinearMap
    (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm.toContinuousLinearMap

include ho hl hu hab hcard in
theorem nativeForm_eq_pullback (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    nativeForm hdim x o edges z.val =
      OrientedFormChangeVariables.pullback (map hdim x o a b ho hl hu hab hcard) (simpleForm hdim x o a b ho hl hu hab hcard edges) z.val := by
  rw [nativeForm, PureForestFaceForms.graphForm_eq_simple hdim x o a b ho hl hu hab z]
  change (simpleFaceForm x o a b edges (coordinates hdim x o a b z.val)).compContinuousLinearMap
    (fderiv ℝ (coordinates hdim x o a b) z.val) = _
  unfold OrientedFormChangeVariables.pullback simpleForm map
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have hd := ((simpleCoordinates hdim x o a b ho hl hu hab hcard).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o a b ho hl hu hab z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun w ↦ simpleCoordinates hdim x o a b ho hl hu hab hcard (coordinates hdim x o a b w)) z.val = _ at hd
  rw [hd]
  ext V
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  simp

include ho hl hu hab hcard in
theorem native_density_eq_jacobian (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    OrientedFormChangeVariables.density (nativeForm hdim x o edges) z.val =
      jacobian hdim x o a b ho hl hu hab hcard z.val * OrientedFormChangeVariables.density (simpleForm hdim x o a b ho hl hu hab hcard edges) (map hdim x o a b ho hl hu hab hcard z.val) := by
  unfold OrientedFormChangeVariables.density
  rw [nativeForm_eq_pullback hdim x o a b ho hl hu hab hcard z]
  exact OrientedFormChangeVariables.density_pullback _ _ _

include ho hl hu hab hcard in
/-- Exact cutoff transport with the actual derivative sign. There is no
assumed orientation multiplier; the remaining collar comparison must evaluate
this explicit ratio relative to the global configuration orientation. -/
theorem weighted_graph_integral (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (∫ w in s, κ w * OrientedFormChangeVariables.density (nativeForm hdim x o edges) w) =
      ∫ y in map hdim x o a b ho hl hu hab hcard '' s, κ (inverseReal hdim x o a b ho hl hu hab hcard y) *
        (jacobian hdim x o a b ho hl hu hab hcard (inverseReal hdim x o a b ho hl hu hab hcard y) / |jacobian hdim x o a b ho hl hu hab hcard (inverseReal hdim x o a b ho hl hu hab hcard y)|) *
        OrientedFormChangeVariables.density (simpleForm hdim x o a b ho hl hu hab hcard edges) y := by
  rw [integral_image_source hdim x o a b ho hl hu hab hcard s hs hsub]
  apply setIntegral_congr_fun hs
  intro w hw
  dsimp only
  rw [inverseReal_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩, native_density_eq_jacobian hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩]
  have hj := abs_ne_zero.mpr (jacobian_ne_zero hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩)
  field_simp
  <;> ring

/-- The transported signed density includes the actual derivative orientation. -/
def transportedDensity (κ : Coord r → ℝ)
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) (y : Coord r) : ℝ :=
  κ (inverseReal hdim x o a b ho hl hu hab hcard y) *
    (jacobian hdim x o a b ho hl hu hab hcard (inverseReal hdim x o a b ho hl hu hab hcard y) /
      |jacobian hdim x o a b ho hl hu hab hcard (inverseReal hdim x o a b ho hl hu hab hcard y)|) *
    OrientedFormChangeVariables.density (simpleForm hdim x o a b ho hl hu hab hcard edges) y

include ho hl hu hab hcard in
/-- Actual weighted L1 transport, not merely equality of totalized integrals. -/
theorem integrableOn_transportedDensity_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    IntegrableOn (transportedDensity hdim x o a b ho hl hu hab hcard κ edges) (map hdim x o a b ho hl hu hab hcard '' s) ↔
      IntegrableOn (fun w ↦ κ w * OrientedFormChangeVariables.density
        (nativeForm hdim x o edges) w) s := by
  rw [integrableOn_image_source_iff hdim x o a b ho hl hu hab hcard s hs hsub]
  apply integrableOn_congr_fun _ hs
  intro w hw
  dsimp only [transportedDensity]
  rw [inverseReal_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩,
    native_density_eq_jacobian hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩]
  have hj := abs_ne_zero.mpr (jacobian_ne_zero hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩)
  field_simp

include ho hl hu hab hcard in
/-- Exact support of the pulled cutoff on the actual image, including cutoffs
that vanish at interior points. -/
theorem cutoff_support_image (s : Set (Coord r))
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (κ : Coord r → ℝ) :
    Function.support (fun y ↦ κ (inverseReal hdim x o a b ho hl hu hab hcard y)) ∩ (map hdim x o a b ho hl hu hab hcard '' s) =
      map hdim x o a b ho hl hu hab hcard '' (Function.support κ ∩ s) := by
  ext y
  constructor
  · rintro ⟨hκ,w,hw,rfl⟩
    refine ⟨w,⟨?_,hw⟩,rfl⟩
    simpa only [Function.mem_support, inverseReal_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩] using hκ
  · rintro ⟨w,⟨hκ,hw⟩,rfl⟩
    refine ⟨?_,⟨w,hw,rfl⟩⟩
    simpa only [Function.mem_support, inverseReal_map hdim x o a b ho hl hu hab hcard ⟨w,hsub hw⟩] using hκ

include ho hl hu hab hcard in
/-- The finite partition's actual cutoff gives a Lebesgue integrable simple
face density, by compact orthant Stokes and the proved change of variables. -/
theorem integrableOn_transported_partition
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ)
    (hcont : Continuous (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ))
    (hcompact : HasCompactSupport (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ)) :
    IntegrableOn (transportedDensity hdim x o a b ho hl hu hab hcard (ForestFaceCutoffIntegrability.cutoff hdim x o ρ)
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)))
      (map hdim x o a b ho hl hu hab hcard '' ForestRadialFaceLocalization.source hdim x o) := by
  apply (integrableOn_transportedDensity_iff hdim x o a b ho hl hu hab hcard _
    (ForestRadialFaceLocalization.measurableSet_source hdim x o) (Subset.refl _) _ _).mpr
  exact ForestFaceCutoffIntegrability.integrableOn_cutoff_graphDensity
    hdim x o ρ edges hloop κ hmatch hcont hcompact

include ho hl hu hab hcard in
/-- Exact transport of the actual localized outward contribution, retaining
its native lower-face sign and the actual change-of-variables determinant. -/
theorem contribution_eq_transported_partition
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x ρ edges hloop κ) :
    ForestRadialFaceClassification.contribution hdim x
      (ForestGlobalGraphStokes.localForm hdim x ρ edges hloop κ) o =
      -((-1 : ℝ) ^ (axis hdim x o).val) •
        ∫ y in map hdim x o a b ho hl hu hab hcard '' ForestRadialFaceLocalization.source hdim x o,
          transportedDensity hdim x o a b ho hl hu hab hcard (ForestFaceCutoffIntegrability.cutoff hdim x o ρ)
            (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) y := by
  rw [ForestRadialFaceLocalization.contribution_eq_integral_source
    hdim x o ρ edges hloop κ hmatch]
  congr 1
  calc
    _ = ∫ w in ForestRadialFaceLocalization.source hdim x o,
        ForestFaceCutoffIntegrability.cutoff hdim x o ρ w *
          OrientedFormChangeVariables.density (nativeForm hdim x o
            (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))) w := by
      apply setIntegral_congr_fun (ForestRadialFaceLocalization.measurableSet_source hdim x o)
      intro w hw
      exact ForestFaceCutoffIntegrability.local_density_eq hdim x o ρ edges hloop κ hmatch w hw
    _ = _ := weighted_graph_integral hdim x o a b ho hl hu hab hcard _
      (ForestRadialFaceLocalization.measurableSet_source hdim x o) (Subset.refl _) _ _

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestFaceChangeVariables
