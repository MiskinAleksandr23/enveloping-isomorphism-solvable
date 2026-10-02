import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterSmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterForms

/-! Angular forms of factored forest edges. Positive real monomial scales cancel
on the interior; the resulting form of nonvanishing units is smooth and closed
without any positivity or nonvanishing requirement on boundary scales.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The angular logarithmic derivative of a product is the sum of the two actual pullbacks. -/
theorem angularPullback_mul (u v : E → ℂ) (x : E)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) :
    angularPullback (fun y ↦ u y * v y) x = angularPullback u x + angularPullback v x := by
  rw [angularPullback, (hu.hasFDerivAt.fun_mul hv.hasFDerivAt).fderiv]
  ext w
  simp only [angularPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, ContinuousAlternatingMap.add_apply]
  change ((u x * fderiv ℝ v x (w 0) + v x * fderiv ℝ u x (w 0)) / (u x * v x)).im = _
  have h : (u x * fderiv ℝ v x (w 0) + v x * fderiv ℝ u x (w 0)) / (u x * v x) =
      fderiv ℝ u x (w 0) / u x + fderiv ℝ v x (w 0) / v x := by
    field_simp
    ring
  rw [h, Complex.add_im]
  rfl

theorem angularPullback_inv (u : E → ℂ) (x : E)
    (hu : DifferentiableAt ℝ u x) (hu0 : u x ≠ 0) :
    angularPullback (fun y ↦ (u y)⁻¹) x = -angularPullback u x := by
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hu0).comp x hu.hasFDerivAt
  change HasFDerivAt (fun y ↦ (u y)⁻¹)
    ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ) (u x)⁻¹) (u x)⁻¹).comp (fderiv ℝ u x)) x at hi
  rw [angularPullback, hi.fderiv]
  ext w
  simp only [angularPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, ContinuousAlternatingMap.neg_apply]
  change ((-((u x)⁻¹ * fderiv ℝ u x (w 0) * (u x)⁻¹)) / (u x)⁻¹).im =
    -(fderiv ℝ u x (w 0) / u x).im
  have h : (-((u x)⁻¹ * fderiv ℝ u x (w 0) * (u x)⁻¹)) / (u x)⁻¹ =
      -(fderiv ℝ u x (w 0) / u x) := by
    field_simp
  rw [h, Complex.neg_im]

/-- Quotient calculus for two independently varying nonzero complex factors. -/
theorem angularPullback_div (u v : E → ℂ) (x : E)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) :
    angularPullback (fun y ↦ u y / v y) x = angularPullback u x - angularPullback v x := by
  simp only [div_eq_mul_inv]
  rw [angularPullback_mul u (fun y ↦ (v y)⁻¹) x hu (hv.inv hv0) hu0 (inv_ne_zero hv0),
    angularPullback_inv v x hv hv0, sub_eq_add_neg]

/-- The scale-free edge form, defined even where all radial scale monomials vanish. -/
def forestUnitEdgeForm (u v : E → ℂ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback u x - angularPullback v x

/-- Distinct positive scales cancel independently; their quotient need not extend to a corner. -/
theorem angularPullback_scaled_div (s t : E → ℝ) (u v : E → ℂ) (x : E)
    (hs : DifferentiableAt ℝ s x) (ht : DifferentiableAt ℝ t x)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hspos : 0 < s x) (htpos : 0 < t x) (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) :
    angularPullback (fun y ↦ ((s y : ℂ) * u y) / ((t y : ℂ) * v y)) x =
      forestUnitEdgeForm u v x := by
  have hsC : DifferentiableAt ℝ (fun y ↦ (s y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hs
  have htC : DifferentiableAt ℝ (fun y ↦ (t y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x ht
  rw [angularPullback_div _ _ x (hsC.fun_mul hu) (htC.fun_mul hv)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hspos.ne') hu0)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') hv0),
    angularPullback_real_mul s u x hs hu hspos.ne' hu0,
    angularPullback_real_mul t v x ht hv htpos.ne' hv0]
  rfl

/-- A genuine harmonic edge with locally factored numerator and reflected denominator
has the regular unit form at every strictly positive radial point. -/
theorem harmonicAngleForm_factored_pullback (f : E → ℂ × ℂ)
    (s t : E → ℝ) (u v : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x)
    (hs : DifferentiableAt ℝ s x) (ht : DifferentiableAt ℝ t x)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hspos : 0 < s x) (htpos : 0 < t x) (hu0 : u x ≠ 0) (hv0 : v x ≠ 0)
    (hnum : (fun y ↦ (f y).2 - (f y).1) =ᶠ[𝓝 x] (fun y ↦ (s y : ℂ) * u y))
    (hden : (fun y ↦ (f y).2 - conj (f y).1) =ᶠ[𝓝 x] (fun y ↦ (t y : ℂ) * v y)) :
    (harmonicAngleForm (f x)).compContinuousLinearMap (fderiv ℝ f x) =
      forestUnitEdgeForm u v x := by
  have hd : (f x).2 - conj (f x).1 ≠ 0 := by
    rw [hden.eq_of_nhds]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') hv0
  rw [harmonicAngleForm_pullback f x hf hd]
  change angularPullback ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ f) x = _
  have heq : ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ f) =ᶠ[𝓝 x]
      (fun y ↦ ((s y : ℂ) * u y) / ((t y : ℂ) * v y)) := by
    filter_upwards [hnum, hden] with y hn hd
    change ((f y).2 - (f y).1) / ((f y).2 - conj (f y).1) = _
    rw [hn, hd]
  rw [angularPullback_congr_eventually heq]
  exact angularPullback_scaled_div s t u v x hs ht hu hv hspos htpos hu0 hv0

/-- Corner regularity depends only on the smooth nonzero units, not on radial scales. -/
theorem contDiffAt_forestUnitEdgeForm (u v : E → ℂ) (x : E)
    (hu : ContDiffAt ℝ ⊤ u x) (hv : ContDiffAt ℝ ⊤ v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) : ContDiffAt ℝ ⊤ (forestUnitEdgeForm u v) x :=
  (contDiffAt_angularPullback u x hu hu0).sub (contDiffAt_angularPullback v x hv hv0)

/-- The extended unit form is closed across every corner where its units remain nonzero. -/
theorem extDeriv_forestUnitEdgeForm (u v : E → ℂ) (x : E)
    (hu : ContDiffAt ℝ ⊤ u x) (hv : ContDiffAt ℝ ⊤ v x)
    (hu0 : u x ≠ 0) (hv0 : v x ≠ 0) : extDeriv (forestUnitEdgeForm u v) x = 0 := by
  have heq : forestUnitEdgeForm u v = angularPullback u + (-1 : ℝ) • angularPullback v := by
    funext y
    ext w
    change angularPullback u y w - angularPullback v y w =
      angularPullback u y w + (-1 : ℝ) * angularPullback v y w
    ring
  rw [heq, extDeriv_add
    ((contDiffAt_angularPullback u x hu hu0).differentiableAt (by simp))
    (((contDiffAt_angularPullback v x hv hv0).differentiableAt (by simp)).const_smul (-1 : ℝ)),
    extDeriv_smul, extDeriv_angularPullback u x hu hu0, extDeriv_angularPullback v x hv hv0,
    smul_zero, add_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich
