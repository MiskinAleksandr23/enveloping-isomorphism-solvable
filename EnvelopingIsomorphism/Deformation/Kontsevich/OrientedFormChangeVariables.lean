import EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.StdBasis

/-! Change of coordinates for actual top-degree differential forms. Pullback uses
the actual Fréchet derivative, and integration uses Mathlib's Jacobian theorem
on measurable subsets of the source of a native OpenPartialHomeomorph. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables

open Set MeasureTheory ContinuousAlternatingMap
open BoxStokes
open scoped Topology

/-- A top-degree differential form in real coordinate space. -/
abbrev TopForm (d : ℕ) := Coord d → Coord d [⋀^Fin d]→L[ℝ] ℝ

/-- Signed coefficient relative to the actual standard coordinate basis. -/
def density {d : ℕ} (ω : TopForm d) (x : Coord d) : ℝ := ω x (standardBasis d)

/-- Actual pullback of a top form by its Fréchet derivative. -/
def pullback {d : ℕ} (f : Coord d → Coord d) (ω : TopForm d) : TopForm d :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

/-- The genuine Jacobian determinant, without replacing it by an absolute value. -/
def jacobian {d : ℕ} (f : Coord d → Coord d) (x : Coord d) : ℝ := (fderiv ℝ f x).det

theorem topForm_linear_change {d : ℕ} (α : Coord d [⋀^Fin d]→L[ℝ] ℝ)
    (L : Coord d →L[ℝ] Coord d) :
    α (fun i ↦ L (standardBasis d i)) = L.det * α (standardBasis d) := by
  let b := Pi.basisFun ℝ (Fin d)
  have hb : (b : Fin d → Coord d) = standardBasis d := by
    funext i
    exact Pi.basisFun_apply ℝ (Fin d) i
  have h := α.toAlternatingMap.eq_smul_basis_det b
  have hv := congrArg (fun a : Coord d [⋀^Fin d]→ₗ[ℝ] ℝ ↦ a (L.toLinearMap ∘ b)) h
  simp only [AlternatingMap.smul_apply, Module.Basis.det_comp, Module.Basis.det_self, mul_one,
    smul_eq_mul] at hv
  change α (fun i ↦ L (b i)) = α b * L.det at hv
  rw [hb] at hv
  exact hv.trans (mul_comm _ _)

/-- The signed pullback density is determinant times the original density at the image. -/
theorem density_pullback {d : ℕ} (f : Coord d → Coord d) (ω : TopForm d) (x : Coord d) :
    density (pullback f ω) x = jacobian f x * density ω (f x) :=
  topForm_linear_change (ω (f x)) (fderiv ℝ f x)

variable {d : ℕ} (e : OpenPartialHomeomorph (Coord d) (Coord d))

/-- C1 on the native open source supplies an actual derivative on every measurable subregion. -/
theorem hasFDerivWithinAt_on_subset (he : ContDiffOn ℝ 1 e e.source)
    {s : Set (Coord d)} (hs : s ⊆ e.source) (x : Coord d) (hx : x ∈ s) :
    HasFDerivWithinAt e (fderiv ℝ e x) s x :=
  ((he.contDiffAt (e.open_source.mem_nhds (hs hx))).differentiableAt (by decide)).hasFDerivAt.hasFDerivWithinAt

/-- Integrability is transported for signed form densities under a positive coordinate change. -/
theorem integrableOn_image_iff_pullback (he : ContDiffOn ℝ 1 e e.source)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source)
    (hpos : ∀ x ∈ s, 0 < jacobian e x) (ω : TopForm d) :
    IntegrableOn (density ω) (e '' s) ↔ IntegrableOn (density (pullback e ω)) s := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (hasFDerivWithinAt_on_subset e he hse) (e.injOn.mono hse) (density ω)
  refine h.trans (integrableOn_congr_fun ?_ hs)
  intro x hx
  rw [density_pullback]
  change |jacobian e x| • density ω (e x) = jacobian e x * density ω (e x)
  rw [abs_of_pos (hpos x hx), smul_eq_mul]

/-- Positive coordinate changes preserve the actual signed integral on every measurable source subset. -/
theorem integral_pullback_eq_image (he : ContDiffOn ℝ 1 e e.source)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source)
    (hpos : ∀ x ∈ s, 0 < jacobian e x) (ω : TopForm d) :
    (∫ x in s, density (pullback e ω) x) = ∫ y in e '' s, density ω y := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (hasFDerivWithinAt_on_subset e he hse) (e.injOn.mono hse) (density ω)]
  apply setIntegral_congr_fun hs
  intro x hx
  rw [density_pullback]
  change jacobian e x * density ω (e x) = |jacobian e x| • density ω (e x)
  rw [abs_of_pos (hpos x hx), smul_eq_mul]

theorem integrableOn_target_iff_pullback (he : ContDiffOn ℝ 1 e e.source)
    (hpos : ∀ x ∈ e.source, 0 < jacobian e x) (ω : TopForm d) :
    IntegrableOn (density ω) e.target ↔ IntegrableOn (density (pullback e ω)) e.source := by
  simpa only [e.image_source_eq_target] using
    integrableOn_image_iff_pullback e he e.source e.open_source.measurableSet subset_rfl hpos ω

theorem integral_pullback_eq_target (he : ContDiffOn ℝ 1 e e.source)
    (hpos : ∀ x ∈ e.source, 0 < jacobian e x) (ω : TopForm d) :
    (∫ x in e.source, density (pullback e ω) x) = ∫ y in e.target, density ω y := by
  simpa only [e.image_source_eq_target] using
    integral_pullback_eq_image e he e.source e.open_source.measurableSet subset_rfl hpos ω


/-- The measurable source region has an actual measurable image. -/
theorem measurableSet_image (he : ContDiffOn ℝ 1 e e.source)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source) : MeasurableSet (e '' s) :=
  measurable_image_of_fderivWithin hs (hasFDerivWithinAt_on_subset e he hse) (e.injOn.mono hse)

/-- Negative orientation changes the signed integral by a minus sign. -/
theorem integral_pullback_eq_neg_image (he : ContDiffOn ℝ 1 e e.source)
    (s : Set (Coord d)) (hs : MeasurableSet s) (hse : s ⊆ e.source)
    (hneg : ∀ x ∈ s, jacobian e x < 0) (ω : TopForm d) :
    (∫ x in s, density (pullback e ω) x) = -(∫ y in e '' s, density ω y) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (hasFDerivWithinAt_on_subset e he hse) (e.injOn.mono hse) (density ω), ← integral_neg]
  apply setIntegral_congr_fun hs
  intro x hx
  rw [density_pullback]
  change jacobian e x * density ω (e x) = -(|jacobian e x| • density ω (e x))
  rw [abs_of_neg (hneg x hx), neg_smul, neg_neg, smul_eq_mul]

/-- The two actual derivatives of a C1 coordinate equivalence compose to the identity. -/
theorem inverse_derivative_comp (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (x : Coord d) (hx : x ∈ e.source) :
    (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ (Coord d) := by
  have hf : DifferentiableAt ℝ e x :=
    (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by decide)
  have hg : DifferentiableAt ℝ e.symm (e x) :=
    (hinv.contDiffAt (e.open_target.mem_nhds (e.mapsTo hx))).differentiableAt (by decide)
  have hleft : (fun y ↦ e.symm (e y)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have h := hleft.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_id] at h
  exact (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv.symm.trans h

theorem jacobian_inverse_mul (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (x : Coord d) (hx : x ∈ e.source) :
    jacobian e.symm (e x) * jacobian e x = 1 := by
  have h := congrArg (fun L : Coord d →L[ℝ] Coord d ↦ L.det) (inverse_derivative_comp e he hinv x hx)
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap) =
    LinearMap.det (LinearMap.id : Coord d →ₗ[ℝ] Coord d) at h
  rw [LinearMap.det_comp, LinearMap.det_id] at h
  exact h

/-- A positive C1 coordinate equivalence has a positive inverse coordinate change. -/
theorem jacobian_symm_positive (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (hpos : ∀ x ∈ e.source, 0 < jacobian e x)
    (y : Coord d) (hy : y ∈ e.target) : 0 < jacobian e.symm y := by
  have hx : e.symm y ∈ e.source := e.symm.mapsTo hy
  have h := jacobian_inverse_mul e he hinv (e.symm y) hx
  rw [e.right_inv hy] at h
  by_contra hn
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hpos (e.symm y) hx).le
  rw [h] at hnonpos
  norm_num at hnonpos

/-- Pullback by a coordinate equivalence and its inverse recovers the actual form on the source. -/
theorem pullback_inverse_eq (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (ω : TopForm d) (x : Coord d) (hx : x ∈ e.source) :
    pullback e (pullback e.symm ω) x = ω x := by
  apply ContinuousAlternatingMap.ext
  intro v
  change ω (e.symm (e x)) (fun i ↦ (fderiv ℝ e.symm (e x)) ((fderiv ℝ e x) (v i))) = ω x v
  rw [e.left_inv hx]
  congr 1
  funext i
  exact congrArg (fun L : Coord d →L[ℝ] Coord d ↦ L (v i)) (inverse_derivative_comp e he hinv x hx)

/-- The reverse-direction integral identity uses the actual inverse derivative and orientation. -/
theorem integral_inverse_pullback_eq_source (he : ContDiffOn ℝ 1 e e.source)
    (hinv : ContDiffOn ℝ 1 e.symm e.target) (hpos : ∀ x ∈ e.source, 0 < jacobian e x)
    (ω : TopForm d) :
    (∫ y in e.target, density (pullback e.symm ω) y) = ∫ x in e.source, density ω x :=
  integral_pullback_eq_target e.symm hinv (jacobian_symm_positive e he hinv hpos) ω

end EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
