import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestFaceCutoffIntegrability

/-! Actual Lebesgue and cutoff transport for the surviving all-interior
infinity face, in the exact real shape frame used by its weight endpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceChangeVariables
open Configuration InfinityForestSimpleCoordinates ForestRadialFaceClassification BoxStokes MeasureTheory Set
open InfinityForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (q : Fin m)
  (ho : kind 0 x o = .infinity) (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (hall : ∀ j : Fin m, j ≠ q → j ∈ boundaryClusterBlock (lower x o) (upper x o))

include hdim ho hq hne hall in
theorem dimension_eq : InfinityBoundaryGraphIntegral.Degree (0 : Fin (n+1)) (lower x o) (upper x o) = r := by
  have h := (InfinityBoundaryGraphIntegral.faceCoordinates (a := (0 : Fin (n+1))) hq hall).toLinearEquiv.finrank_eq
  have hf := InfinityForestSimpleOverlap.finrank_face hdim x o q ho hq hne
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at h
  exact h.symm.trans hf

def simpleCoordinates : InfinityForestSimpleOverlap.Face x o q ≃L[ℝ] Coord r :=
  (InfinityBoundaryGraphIntegral.faceCoordinates hq hall).trans
    (ForestGlobalGraphStokes.coordinateCast (dimension_eq hdim x o q ho hq hne hall))

def simpleFaceForm {k : ℕ} (edges : Fin k → ForestGraphTopForms.Edge (n+1) m)
    (y : InfinityForestSimpleOverlap.Face x o q) :=
  (InfinityBoundaryGraphFactorization.graphForm (l := lower x o) (u := upper x o)
    (fun j ↦ ((edges j).source,(edges j).target)) (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding y)).compContinuousLinearMap
      BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding


def map (w : Coord r) : Coord r := simpleCoordinates hdim x o q ho hq hne hall (coordinates hdim x o q w)
def jacobian (w : Coord r) : ℝ := (fderiv ℝ (map hdim x o q ho hq hne hall) w).det

def inverseReal (y : Coord r) : Coord r := InfinityForestSimpleOverlap.inverse hdim x o q ((simpleCoordinates hdim x o q ho hq hne hall).symm y)

variable (z : ForestRadialFaceLocalization.source hdim x o)

include ho hq hne hall in
theorem contDiffAt_map : ContDiffAt ℝ ⊤ (map hdim x o q ho hq hne hall) z.val :=
  (simpleCoordinates hdim x o q ho hq hne hall).contDiff.contDiffAt.comp z.val
    (contDiffAt_coordinates hdim x o q ho hq hne z)

include ho hq hne hall in
theorem inverseReal_map : inverseReal hdim x o q ho hq hne hall (map hdim x o q ho hq hne hall z.val) = z.val := by
  rw [inverseReal, map, ContinuousLinearEquiv.symm_apply_apply]
  exact InfinityForestSimpleOverlap.inverse_coordinates hdim x o q ho hq hne z

include ho hq hne hall in
theorem map_injective_on : Set.InjOn (map hdim x o q ho hq hne hall) (ForestRadialFaceLocalization.source hdim x o) := by
  intro w hw v hv he
  have h := congrArg (inverseReal hdim x o q ho hq hne hall) he
  rw [inverseReal_map hdim x o q ho hq hne hall ⟨w,hw⟩, inverseReal_map hdim x o q ho hq hne hall ⟨v,hv⟩] at h
  exact h

include ho hq hne hall in
theorem jacobian_ne_zero : jacobian hdim x o q ho hq hne hall z.val ≠ 0 := by
  have hd := ((simpleCoordinates hdim x o q ho hq hne hall).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o q ho hq hne z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (map hdim x o q ho hq hne hall) z.val = _ at hd
  unfold jacobian
  rw [hd]
  let e := LinearEquiv.ofBijective
    (((simpleCoordinates hdim x o q ho hq hne hall).toContinuousLinearMap.comp
      (fderiv ℝ (coordinates hdim x o q) z.val)).toLinearMap)
    ((simpleCoordinates hdim x o q ho hq hne hall).bijective.comp (InfinityForestSimpleOverlap.differential_bijective hdim x o q ho hq hne z))
  exact e.isUnit_det'.ne_zero

include ho hq hne hall in
theorem integral_image_source (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    (∫ y in map hdim x o q ho hq hne hall '' s, g y) = ∫ w in s, |jacobian hdim x o q ho hq hne hall w| * g (map hdim x o q ho hq hne hall w) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (map hdim x o q ho hq hne hall) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o q ho hq hne hall).mono hsub

include ho hq hne hall in
theorem integrableOn_image_source_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (g : Coord r → ℝ) :
    IntegrableOn g (map hdim x o q ho hq hne hall '' s) ↔
      IntegrableOn (fun w ↦ |jacobian hdim x o q ho hq hne hall w| * g (map hdim x o q ho hq hne hall w)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs (f' := fun w ↦ fderiv ℝ (map hdim x o q ho hq hne hall) w)]
  · rfl
  · intro w hw
    exact ((contDiffAt_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact (map_injective_on hdim x o q ho hq hne hall).mono hsub

def nativeForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun w ↦ (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o w)).compContinuousLinearMap
    (fderiv ℝ (faceAmbient hdim x o) w)

def simpleForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) : OrientedFormChangeVariables.TopForm r :=
  fun y ↦ (simpleFaceForm x o q edges ((simpleCoordinates hdim x o q ho hq hne hall).symm y)).compContinuousLinearMap
    (simpleCoordinates hdim x o q ho hq hne hall).symm.toContinuousLinearMap

include ho hq hne hall in
theorem nativeForm_eq_pullback (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    nativeForm hdim x o edges z.val =
      OrientedFormChangeVariables.pullback (map hdim x o q ho hq hne hall) (simpleForm hdim x o q ho hq hne hall edges) z.val := by
  rw [nativeForm, InfinityForestFaceForms.graphForm_eq_simple hdim x o q ho hq hne z]
  change (simpleFaceForm x o q edges (coordinates hdim x o q z.val)).compContinuousLinearMap
    (fderiv ℝ (coordinates hdim x o q) z.val) = _
  unfold OrientedFormChangeVariables.pullback simpleForm map
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have hd := ((simpleCoordinates hdim x o q ho hq hne hall).hasFDerivAt.comp z.val
    ((contDiffAt_coordinates hdim x o q ho hq hne z).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun w ↦ simpleCoordinates hdim x o q ho hq hne hall (coordinates hdim x o q w)) z.val = _ at hd
  rw [hd]
  ext V
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  simp

include ho hq hne hall in
theorem native_density_eq_jacobian (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    OrientedFormChangeVariables.density (nativeForm hdim x o edges) z.val =
      jacobian hdim x o q ho hq hne hall z.val * OrientedFormChangeVariables.density (simpleForm hdim x o q ho hq hne hall edges) (map hdim x o q ho hq hne hall z.val) := by
  unfold OrientedFormChangeVariables.density
  rw [nativeForm_eq_pullback hdim x o q ho hq hne hall z]
  exact OrientedFormChangeVariables.density_pullback _ _ _

include ho hq hne hall in
/-- Exact cutoff transport with the actual derivative sign. There is no
assumed orientation multiplier; the remaining collar comparison must evaluate
this explicit ratio relative to the global configuration orientation. -/
theorem weighted_graph_integral (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (∫ w in s, κ w * OrientedFormChangeVariables.density (nativeForm hdim x o edges) w) =
      ∫ y in map hdim x o q ho hq hne hall '' s, κ (inverseReal hdim x o q ho hq hne hall y) *
        (jacobian hdim x o q ho hq hne hall (inverseReal hdim x o q ho hq hne hall y) / |jacobian hdim x o q ho hq hne hall (inverseReal hdim x o q ho hq hne hall y)|) *
        OrientedFormChangeVariables.density (simpleForm hdim x o q ho hq hne hall edges) y := by
  rw [integral_image_source hdim x o q ho hq hne hall s hs hsub]
  apply setIntegral_congr_fun hs
  intro w hw
  dsimp only
  rw [inverseReal_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩, native_density_eq_jacobian hdim x o q ho hq hne hall ⟨w,hsub hw⟩]
  have hj := abs_ne_zero.mpr (jacobian_ne_zero hdim x o q ho hq hne hall ⟨w,hsub hw⟩)
  field_simp
  <;> ring

/-- The transported signed density includes the actual derivative orientation. -/
def transportedDensity (κ : Coord r → ℝ)
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) (y : Coord r) : ℝ :=
  κ (inverseReal hdim x o q ho hq hne hall y) *
    (jacobian hdim x o q ho hq hne hall (inverseReal hdim x o q ho hq hne hall y) /
      |jacobian hdim x o q ho hq hne hall (inverseReal hdim x o q ho hq hne hall y)|) *
    OrientedFormChangeVariables.density (simpleForm hdim x o q ho hq hne hall edges) y

include ho hq hne hall in
/-- Actual weighted L1 transport, not merely equality of totalized integrals. -/
theorem integrableOn_transportedDensity_iff (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    IntegrableOn (transportedDensity hdim x o q ho hq hne hall κ edges) (map hdim x o q ho hq hne hall '' s) ↔
      IntegrableOn (fun w ↦ κ w * OrientedFormChangeVariables.density
        (nativeForm hdim x o edges) w) s := by
  rw [integrableOn_image_source_iff hdim x o q ho hq hne hall s hs hsub]
  apply integrableOn_congr_fun _ hs
  intro w hw
  dsimp only [transportedDensity]
  rw [inverseReal_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩,
    native_density_eq_jacobian hdim x o q ho hq hne hall ⟨w,hsub hw⟩]
  have hj := abs_ne_zero.mpr (jacobian_ne_zero hdim x o q ho hq hne hall ⟨w,hsub hw⟩)
  field_simp

include ho hq hne hall in
/-- Exact support of the pulled cutoff on the actual image, including cutoffs
that vanish at interior points. -/
theorem cutoff_support_image (s : Set (Coord r))
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o) (κ : Coord r → ℝ) :
    Function.support (fun y ↦ κ (inverseReal hdim x o q ho hq hne hall y)) ∩ (map hdim x o q ho hq hne hall '' s) =
      map hdim x o q ho hq hne hall '' (Function.support κ ∩ s) := by
  ext y
  constructor
  · rintro ⟨hκ,w,hw,rfl⟩
    refine ⟨w,⟨?_,hw⟩,rfl⟩
    simpa only [Function.mem_support, inverseReal_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩] using hκ
  · rintro ⟨w,⟨hκ,hw⟩,rfl⟩
    refine ⟨?_,⟨w,hw,rfl⟩⟩
    simpa only [Function.mem_support, inverseReal_map hdim x o q ho hq hne hall ⟨w,hsub hw⟩] using hκ

include ho hq hne hall in
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
    IntegrableOn (transportedDensity hdim x o q ho hq hne hall (ForestFaceCutoffIntegrability.cutoff hdim x o ρ)
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)))
      (map hdim x o q ho hq hne hall '' ForestRadialFaceLocalization.source hdim x o) := by
  apply (integrableOn_transportedDensity_iff hdim x o q ho hq hne hall _
    (ForestRadialFaceLocalization.measurableSet_source hdim x o) (Subset.refl _) _ _).mpr
  exact ForestFaceCutoffIntegrability.integrableOn_cutoff_graphDensity
    hdim x o ρ edges hloop κ hmatch hcont hcompact

include ho hq hne hall in
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
        ∫ y in map hdim x o q ho hq hne hall '' ForestRadialFaceLocalization.source hdim x o,
          transportedDensity hdim x o q ho hq hne hall (ForestFaceCutoffIntegrability.cutoff hdim x o ρ)
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
    _ = _ := weighted_graph_integral hdim x o q ho hq hne hall _
      (ForestRadialFaceLocalization.measurableSet_source hdim x o) (Subset.refl _) _ _

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceChangeVariables
