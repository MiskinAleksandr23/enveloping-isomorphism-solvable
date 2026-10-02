import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactOrthantStokes
import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingStokes

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffStokes
open InteriorFiberAngleSplit NormalCrossingStokes Set MeasureTheory ContinuousAlternatingMap Filter
open scoped Topology ContDiff

theorem alternatizeUncurryFinCLM_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} : alternatizeUncurryFin (0 : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℝ) = 0 :=
  (alternatizeUncurryFinCLM ℝ E ℝ).map_zero

abbrev Edges (N : ℕ) := Fin (NormalCrossingStokes.Dim N) → Point (N + 1) × Point (N + 1)
def edgeFunctions {N : ℕ} (e : Edges N) (j : Fin (NormalCrossingStokes.Dim N)) : Space N → ℂ :=
  shapeDifference (e j).1 (e j).2

def beta {N : ℕ} (e : Edges N) : CrossingForm N := LogRadialPrimitive.primitive (edgeFunctions e)
def current {N : ℕ} (e : Edges N) (ε : ℝ) : CrossingForm N := fun η ↦ RatioCutoff.chi ε η • beta e η

def bulkTerm {N : ℕ} (e : Edges N) (ε : ℝ) (η : Space N) : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→L[ℝ] ℝ :=
  RatioCutoff.chi ε η • extDeriv (beta e) η

def cutoffTerm {N : ℕ} (e : Edges N) (ε : ℝ) (η : Space N) : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→L[ℝ] ℝ :=
  alternatizeUncurryFin ((fderiv ℝ (RatioCutoff.chi ε) η).smulRight (beta e η))

theorem contDiffAt_beta {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {η : Space N} (hη : η ∈ shapeConfiguration (N + 1)) : ContDiffAt ℝ ⊤ (beta e) η := by
  apply LogRadialPrimitive.contDiffAt_primitive
  · intro j
    exact ((contDiff_normalizedPoint (e j).2).sub (contDiff_normalizedPoint (e j).1)).contDiffAt
  · intro j
    exact shapeDifference_ne_zero hη (he j)

theorem contDiff_current {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (current e ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η ∈ tsupport (RatioCutoff.chi ε)
  · exact (RatioCutoff.contDiff_chi hε).contDiffAt.smul
      ((contDiffAt_beta e he (RatioCutoff.tsupport_chi_subset hε hη)).of_le (by simp))
  · apply (contDiffAt_const (c := (0 : Space N [⋀^Fin (Degree N)]→L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hη] with ζ hζ
    simp only [current, hζ, Pi.zero_apply, zero_smul]

theorem hasCompactSupport_current {N : ℕ} (e : Edges N) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (current e ε) := (RatioCutoff.hasCompactSupport_chi hε).smul_right

theorem extDeriv_current {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) (η : Space N) :
    extDeriv (current e ε) η = bulkTerm e ε η + cutoffTerm e ε η := by
  by_cases hη : η ∈ tsupport (RatioCutoff.chi ε)
  · change extDeriv (fun ζ ↦ RatioCutoff.chi ε ζ • beta e ζ) η = _
    rw [extDeriv, fderiv_fun_smul ((RatioCutoff.contDiff_chi hε).differentiable (by simp) η)
      ((contDiffAt_beta e he (RatioCutoff.tsupport_chi_subset hε hη)).differentiableAt (by simp)),
      alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
    rfl
  · have hχ : RatioCutoff.chi ε η = 0 := image_eq_zero_of_notMem_tsupport hη
    have hDχ : fderiv ℝ (RatioCutoff.chi ε) η = 0 := fderiv_of_notMem_tsupport ℝ hη
    have hcur : η ∉ tsupport (current e ε) := fun h ↦
      hη (tsupport_smul_subset_left (RatioCutoff.chi ε) (beta e) h)
    simp only [extDeriv, fderiv_of_notMem_tsupport ℝ hcur, alternatizeUncurryFinCLM_zero, bulkTerm, hχ,
      zero_smul, cutoffTerm, hDχ, ContinuousLinearMap.zero_smulRight, zero_add]

theorem continuous_bulkTerm {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) : Continuous (bulkTerm e ε) := by
  apply continuous_iff_continuousAt.mpr
  intro η
  by_cases hη : η ∈ tsupport (RatioCutoff.chi ε)
  · exact (RatioCutoff.contDiff_chi hε).continuous.continuousAt.smul
      ((alternatizeUncurryFinCLM ℝ _ ℝ).continuous.continuousAt.comp
        ((contDiffAt_beta e he (RatioCutoff.tsupport_chi_subset hε hη)).continuousAt_fderiv (by simp)))
  · apply (continuousAt_const (y := (0 : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hη] with ζ hζ
    simp only [bulkTerm, hζ, Pi.zero_apply, zero_smul]

theorem hasCompactSupport_bulkTerm {N : ℕ} (e : Edges N) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (bulkTerm e ε) := (RatioCutoff.hasCompactSupport_chi hε).smul_right

theorem continuous_cutoffTerm {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cutoffTerm e ε) := by
  have h : cutoffTerm e ε = fun η ↦ extDeriv (current e ε) η - bulkTerm e ε η := by
    funext η
    rw [extDeriv_current e he hε]
    abel
  rw [h]
  exact ((alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp
    ((contDiff_current e he hε).continuous_fderiv (by simp))).sub (continuous_bulkTerm e he hε)

theorem hasCompactSupport_cutoffTerm {N : ℕ} (e : Edges N) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (cutoffTerm e ε) := by
  apply (RatioCutoff.hasCompactSupport_chi hε).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro η hη
  by_contra h
  apply hη
  simp [cutoffTerm, fderiv_of_notMem_tsupport ℝ h, alternatizeUncurryFinCLM_zero]

theorem integrable_bulkTerm {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Integrable (fun η ↦ bulkTerm e ε η v) := by
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ v).continuous.comp (continuous_bulkTerm e he hε)).integrable_of_hasCompactSupport
    ((hasCompactSupport_bulkTerm e hε).comp_left rfl)

theorem integrable_cutoffTerm {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    Integrable (fun η ↦ cutoffTerm e ε η v) := by
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ v).continuous.comp (continuous_cutoffTerm e he hε)).integrable_of_hasCompactSupport
    ((hasCompactSupport_cutoffTerm e hε).comp_left rfl)

/-- Actual Cartesian real/imaginary coordinates; the coordinate change preserves volume. -/
def cartesian (N : ℕ) : BoxStokes.Coord (NormalCrossingStokes.Dim N) ≃L[ℝ] Space N :=
  (split N).trans (ContinuousLinearEquiv.piCongrRight (fun _ ↦ Complex.equivRealProdCLM.symm))

def cartesianMeas (N : ℕ) : BoxStokes.Coord (NormalCrossingStokes.Dim N) ≃ᵐ Space N :=
  (splitMeas N).trans (MeasurableEquiv.piCongrRight (fun _ ↦ Complex.measurableEquivRealProd.symm))

theorem cartesianMeas_eq (N : ℕ) : (cartesianMeas N : _ → _) = cartesian N := rfl

theorem volume_preserving_cartesian (N : ℕ) : MeasurePreserving (cartesianMeas N) :=
  (volume_preserving_pi (fun _ ↦ Complex.volume_preserving_equiv_real_prod.symm)).comp
    (volume_preserving_split N)

def cartesianPullback {N : ℕ} (w : CrossingForm N) : BoxStokes.Form (Degree N) := fun x ↦
  (w (cartesian N x)).compContinuousLinearMap (cartesian N).toContinuousLinearMap

theorem extDeriv_cartesianPullback {N : ℕ} (w : CrossingForm N) (hw : ContDiff ℝ 1 w)
    (x : BoxStokes.Coord (NormalCrossingStokes.Dim N)) :
    extDeriv (cartesianPullback w) x = (extDeriv w (cartesian N x)).compContinuousLinearMap
      (cartesian N).toContinuousLinearMap := by
  have h := extDeriv_pullback ((hw.differentiable (by norm_num)) (cartesian N x))
    (cartesian N).contDiff.contDiffAt (show minSmoothness ℝ 2 ≤ ⊤ by simp)
  simp only [ContinuousLinearEquiv.fderiv] at h
  convert h using 1
  rfl

theorem integral_extDeriv_frame_zero {N : ℕ} (w : CrossingForm N) (hw : ContDiff ℝ 1 w)
    (hc : HasCompactSupport w) : (∫ η, extDeriv w η (frame N)) = 0 := by
  have hp : ContDiff ℝ 1 (cartesianPullback w) := by
    change ContDiff ℝ 1 (fun x ↦ (compContinuousLinearMapCLM (cartesian N).toContinuousLinearMap) (w (cartesian N x)))
    exact (compContinuousLinearMapCLM (cartesian N).toContinuousLinearMap).contDiff.comp
      (hw.comp (cartesian N).contDiff)
  have hc' : HasCompactSupport (cartesianPullback w) :=
    (hc.comp_homeomorph (cartesian N).toHomeomorph).comp_left
      ((compContinuousLinearMapCLM (cartesian N).toContinuousLinearMap).map_zero)
  have h := CompactOrthantStokes.integral_whole_extDeriv_eq_zero (cartesianPullback w) hp hc'
  have heq : (fun x ↦ extDeriv (cartesianPullback w) x (BoxStokes.standardBasis (NormalCrossingStokes.Dim N))) =
      (fun x ↦ extDeriv w (cartesianMeas N x) (frame N)) := by
    funext x
    rw [extDeriv_cartesianPullback w hw]
    rfl
  rw [heq] at h
  exact ((volume_preserving_cartesian N).integral_comp (cartesianMeas N).measurableEmbedding
    (fun η ↦ extDeriv w η (frame N))).symm.trans h

def cartesianBasis (N : ℕ) : Module.Basis (Fin (NormalCrossingStokes.Dim N)) ℝ (Space N) :=
  (Pi.basisFun ℝ (Fin (NormalCrossingStokes.Dim N))).map (cartesian N).toLinearEquiv

theorem cartesianBasis_eq_frame (N : ℕ) : (cartesianBasis N : _ → _) = frame N := by
  funext j
  simp only [cartesianBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem integral_extDeriv_zero {N : ℕ} (w : CrossingForm N) (hw : ContDiff ℝ 1 w)
    (hc : HasCompactSupport w) (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    (∫ η, extDeriv w η v) = 0 := by
  have heq : (fun η ↦ extDeriv w η v) = fun η ↦
      (cartesianBasis N).det v * extDeriv w η (frame N) := by
    funext η
    have h := congrArg (fun A : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→ₗ[ℝ] ℝ ↦ A v)
      ((extDeriv w η).toAlternatingMap.eq_smul_basis_det (cartesianBasis N))
    simp only [AlternatingMap.smul_apply, smul_eq_mul, cartesianBasis_eq_frame] at h
    change extDeriv w η v = extDeriv w η (frame N) * (cartesianBasis N).det v at h
    rw [h, mul_comm]
  rw [heq, integral_const_mul, integral_extDeriv_frame_zero w hw hc, mul_zero]

def actualFrame (N : ℕ) : Fin (NormalCrossingStokes.Dim N) → Space N := fun j ↦
  AngularRadial.realBasis (N + 1) (Fin.cast (by dsimp [NormalCrossingStokes.Dim, Degree, AngularRadial.realDimension]; omega) j)

/-- Finite-cutoff Stokes on the original planar configuration coordinates. -/
theorem finite_cutoff_stokes {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) (v : Fin (NormalCrossingStokes.Dim N) → Space N) :
    (∫ η, bulkTerm e ε η v) = -(∫ η, cutoffTerm e ε η v) := by
  have hz := integral_extDeriv_zero (current e ε) ((contDiff_current e he hε).of_le (by simp))
    (hasCompactSupport_current e hε) v
  simp_rw [extDeriv_current e he hε, ContinuousAlternatingMap.add_apply] at hz
  rw [integral_add (integrable_bulkTerm e he hε v) (integrable_cutoffTerm e he hε v)] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem extDeriv_beta {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {η : Space N} (hη : η ∈ shapeConfiguration (N + 1)) :
    extDeriv (beta e) η = LogRadialPrimitive.radialForm (edgeFunctions e) η := by
  apply LogRadialPrimitive.extDeriv_primitive
  · intro j
    exact ((contDiff_normalizedPoint (e j).2).sub (contDiff_normalizedPoint (e j).1)).contDiffAt
  · intro j
    exact shapeDifference_ne_zero hη (he j)

theorem bulkTerm_eq_radialForm {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) (η : Space N) :
    bulkTerm e ε η = RatioCutoff.chi ε η • LogRadialPrimitive.radialForm (edgeFunctions e) η := by
  by_cases hη : η ∈ tsupport (RatioCutoff.chi ε)
  · rw [bulkTerm, extDeriv_beta e he (RatioCutoff.tsupport_chi_subset hε hη)]
  · simp only [bulkTerm, image_eq_zero_of_notMem_tsupport hη, zero_smul]

/-- Both actual terms are Lebesgue integrable, and Stokes holds in the interleaved 1,I frame.
All smoothness, support and integrability facts are produced from the nonloop edges and ε > 0. -/
theorem actual_finite_cutoff_stokes {N : ℕ} (e : Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun η ↦ RatioCutoff.chi ε η * extDeriv (beta e) η (actualFrame N)) ∧
    Integrable (fun η ↦ cutoffTerm e ε η (actualFrame N)) ∧
    (∫ η, extDeriv (current e ε) η (actualFrame N)) = 0 ∧
    (∫ η, RatioCutoff.chi ε η * extDeriv (beta e) η (actualFrame N)) =
      -(∫ η, cutoffTerm e ε η (actualFrame N)) := by
  exact ⟨integrable_bulkTerm e he hε (actualFrame N), integrable_cutoffTerm e he hε (actualFrame N),
    integral_extDeriv_zero (current e ε) ((contDiff_current e he hε).of_le (by simp))
      (hasCompactSupport_current e hε) (actualFrame N), finite_cutoff_stokes e he hε (actualFrame N)⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffStokes
