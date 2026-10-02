import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffGlobalDomination

/-! Global body L1 from the same finite actual monomial charts used for the
cutoff error. Native change of variables derives every chart-image L1 statement.
Finite-cover assembly requires neither primitive L1 nor coefficient derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyGlobalIntegrability
open Set MeasureTheory Filter ContinuousAlternatingMap
open InteriorFiberAngleSplit NormalCrossingStokes RatioCutoffStokes
open RatioCutoffGlobalDomination
open scoped Topology BigOperators

variable {N : ℕ} (e : RatioCutoffStokes.Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)

def body (η : Space N) : ℝ := extDeriv (beta e) η (frame N)

def bodyData (a : ErrorChart e) : PlanarBodyIntegrability.LocalData (Fin (N + 1)) (Degree N) :=
  PlanarBodyIntegrability.LocalData.ofCombinationData a.monomial

theorem topForm_linear_change (α : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→L[ℝ] ℝ)
    (D : Space N →L[ℝ] Space N) :
    α (fun j ↦ D (frame N j)) = D.det * α (frame N) := by
  have h := congrArg (fun A : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→ₗ[ℝ] ℝ ↦
      A (D.toLinearMap ∘ cartesianBasis N))
    (α.toAlternatingMap.eq_smul_basis_det (cartesianBasis N))
  simp only [AlternatingMap.smul_apply, Module.Basis.det_comp, Module.Basis.det_self,
    mul_one, smul_eq_mul, cartesianBasis_eq_frame] at h
  have hb : (cartesianBasis N).det (frame N) = 1 := by
    rw [← cartesianBasis_eq_frame]
    exact Module.Basis.det_self _
  rw [hb, mul_one] at h
  exact h.trans (mul_comm _ _)

include he in
theorem jacobian_mul_body_eq_density (a : ErrorChart e) {x : Space N}
    (hx : x ∈ a.monomial.region) :
    (fderiv ℝ a.map x).det * body e (a.map x) =
      PlanarBodyIntegrability.density (bodyData e a) (frame N) x := by
  have h := topForm_linear_change (extDeriv (beta e) (a.map x)) (fderiv ℝ a.map x)
  apply h.symm.trans
  exact PlanarBodyIntegrability.body_pullback_eq_density e he (bodyData e a)
    ((a.map_C1 x hx).differentiableAt (by norm_num)) (map_configuration e a hx)
    a.identity_open (a.region_identity hx) a.base_identity (frame N)

include he in
/-- The entire chart image has actual body L1, derived with absolute Jacobian. -/
theorem integrableOn_body_image (a : ErrorChart e) :
    IntegrableOn (body e) (a.map '' a.monomial.region) := by
  have hd : ∀ x ∈ a.monomial.region,
      HasFDerivWithinAt a.map (fderiv ℝ a.map x) a.monomial.region x :=
    fun x hx ↦ ((a.map_C1 x hx).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    a.monomial.measurable_region hd a.map_injective (body e)).mpr
  have hJ : AEStronglyMeasurable (fun x ↦ (fderiv ℝ a.map x).det)
      (volume.restrict a.monomial.region) := by
    apply ContinuousOn.aestronglyMeasurable _ a.monomial.measurable_region
    intro x hx
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((a.map_C1 x hx).continuousAt_fderiv (by norm_num))).continuousWithinAt
  change IntegrableOn (fun x ↦ |(fderiv ℝ a.map x).det| * body e (a.map x)) a.monomial.region
  apply (UnorientedFormIntegrability.integrable_abs_mul_iff
    (fun x ↦ (fderiv ℝ a.map x).det) (fun x ↦ body e (a.map x)) hJ).mpr
  apply (PlanarBodyIntegrability.integrableOn_density (bodyData e a) (frame N)
    (CompactMonomialStokes.norm_frame_le_one N)).congr_fun _ a.monomial.measurable_region
  intro x hx
  exact (jacobian_mul_body_eq_density e he a hx).symm

include he in
/-- The same finite geometric chart cover proves global original-domain body L1. -/
theorem integrableOn_body {K : Type*} [Fintype K] (a : K → ErrorChart e)
    (hcover : shapeConfiguration (N + 1) ⊆ ⋃ k, (a k).map '' (a k).monomial.region) :
    IntegrableOn (body e) (shapeConfiguration (N + 1)) :=
  ((integrableOn_finite_iUnion.mpr (fun k ↦ integrableOn_body_image e he (a k)))).mono_set hcover

/-- Frame change is a fixed scalar and does not change the L1 question. -/
theorem body_actualFrame_eq (η : Space N) :
    extDeriv (beta e) η (actualFrame N) =
      (cartesianBasis N).det (actualFrame N) * body e η := by
  have h := congrArg (fun A : Space N [⋀^Fin (NormalCrossingStokes.Dim N)]→ₗ[ℝ] ℝ ↦ A (actualFrame N))
    ((extDeriv (beta e) η).toAlternatingMap.eq_smul_basis_det (cartesianBasis N))
  simp only [AlternatingMap.smul_apply, smul_eq_mul, cartesianBasis_eq_frame] at h
  exact h.trans (mul_comm _ _)

include he in
theorem integrableOn_body_actualFrame {K : Type*} [Fintype K] (a : K → ErrorChart e)
    (hcover : shapeConfiguration (N + 1) ⊆ ⋃ k, (a k).map '' (a k).monomial.region) :
    IntegrableOn (fun η ↦ extDeriv (beta e) η (actualFrame N)) (shapeConfiguration (N + 1)) := by
  have h := (integrableOn_body e he a hcover).const_mul ((cartesianBasis N).det (actualFrame N))
  simp only [body_actualFrame_eq]
  unfold IntegrableOn
  exact h

include he in
/-- Global L1 of the actual planar angular shape density. -/
theorem integrableOn_shapeDensity {K : Type*} [Fintype K] (a : K → ErrorChart e)
    (hcover : shapeConfiguration (N + 1) ⊆ ⋃ k, (a k).map '' (a k).monomial.region) :
    IntegrableOn (shapeDensity (angularEdges e)) (shapeConfiguration (N + 1)) := by
  apply (integrableOn_body_actualFrame e he a hcover).congr_fun _
    (isOpen_shapeConfiguration (N + 1)).measurableSet
  intro η hη
  exact extDeriv_beta_actualFrame_eq_shapeDensity e he hη

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarBodyGlobalIntegrability
