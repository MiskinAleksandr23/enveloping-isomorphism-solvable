import EnvelopingIsomorphism.Deformation.Kontsevich.LogDistanceRatio
import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Uniformly bounded coefficients in the actual differential of the global cutoff. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
open InteriorFiberAngleSplit Set Filter
open scoped Topology BigOperators ContDiff

theorem deriv_psi_zero_of_lt {s : ℝ} (hs : s < 1) : deriv psi s = 0 := by
  have h : psi =ᶠ[𝓝 s] (fun _ ↦ 0) := by
    filter_upwards [gt_mem_nhds hs] with t ht
    exact psi_zero ht.le
  simpa using h.deriv_eq

theorem deriv_psi_zero_of_gt {s : ℝ} (hs : 2 < s) : deriv psi s = 0 := by
  have h : psi =ᶠ[𝓝 s] (fun _ ↦ 1) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact psi_one ht.le
  simpa using h.deriv_eq

/-- A single bound works for every epsilon and every distance ratio. -/
theorem exists_bound_scaled_deriv_psi : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s * deriv psi s| ≤ C := by
  have hc : Continuous (fun s : ℝ ↦ |s * deriv psi s|) :=
    (continuous_id.mul (contDiff_psi.continuous_deriv (by simp))).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (hc.continuousOn : ContinuousOn (fun s : ℝ ↦ |s * deriv psi s|) (Icc 1 2))
  refine ⟨max C 0, le_max_right _ _, fun s ↦ ?_⟩
  by_cases hs : s ∈ Icc (1 : ℝ) 2
  · exact (hC (mem_image_of_mem _ hs)).trans (le_max_left _ _)
  · have hs' : s < 1 ∨ 2 < s := by simpa only [mem_Icc, not_and_or, not_le] using hs
    rcases hs' with hs' | hs'
    · simp [deriv_psi_zero_of_lt hs']
    · simp [deriv_psi_zero_of_gt hs']

/-- The coefficient in d psi(gamma/epsilon). -/
def radialCutoffCoefficient (ε γ : ℝ) : ℝ :=
  (γ / ε) * deriv psi (γ / ε) * (1 - γ)

theorem abs_radialCutoffCoefficient_le {C : ℝ} (hC : ∀ s : ℝ, |s * deriv psi s| ≤ C)
    (ε γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) : |radialCutoffCoefficient ε γ| ≤ C := by
  have h : |1 - γ| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hγ.2)]; linarith [hγ.1]
  calc
    |radialCutoffCoefficient ε γ| = |(γ / ε) * deriv psi (γ / ε)| * |1 - γ| := abs_mul _ _
    _ ≤ |(γ / ε) * deriv psi (γ / ε)| * 1 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ C := by simpa using hC (γ / ε)

/-- Actual radial edge form, represented as a continuous linear functional. -/
def shapeRadial {N : ℕ} (s t : Point N) (η : Shape N) : Shape N →L[ℝ] ℝ :=
  radialPullback (shapeDifference s t) (shapeDerivative s t) η

theorem hasFDerivAt_psi_gamma {N : ℕ} (ε : ℝ) (t : Triple N) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) :
    HasFDerivAt (fun ζ ↦ psi (gamma t ζ / ε))
      (radialCutoffCoefficient ε (gamma t η) •
        (shapeRadial t.val.1 t.val.2.1 η - shapeRadial t.val.1 t.val.2.2 η)) η := by
  exact hasFDerivAt_distanceRatio_cutoff
    (hasFDerivAt_shapeDifference _ _ η) (hasFDerivAt_shapeDifference _ _ η)
    (shapeDifference_ne_zero hη t.property.1) (shapeDifference_ne_zero hη t.property.2)
    ((contDiff_psi.differentiable (by simp)).differentiableAt.hasDerivAt)

/-- Product coefficients only use values of the other factors, all in [0,1]. -/
def productRadialCoefficient {N : ℕ} (ε : ℝ) (η : Shape N) (t : Triple N) : ℝ :=
  (∏ u ∈ Finset.univ.erase t, psi (gamma u η / ε)) * radialCutoffCoefficient ε (gamma t η)

/-- Native Fréchet derivative of the full finite cutoff. -/
theorem hasFDerivAt_chi_radial {N : ℕ} (ε : ℝ) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) :
    HasFDerivAt (chi (N := N) ε)
      (∑ t : Triple N, productRadialCoefficient ε η t •
        (shapeRadial t.val.1 t.val.2.1 η - shapeRadial t.val.1 t.val.2.2 η)) η := by
  convert! (HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Triple N)))
      (fun t _ ↦ hasFDerivAt_psi_gamma ε t hη)) using 1
  simp only [productRadialCoefficient, smul_smul]

theorem abs_productRadialCoefficient_le {C : ℝ} (hC : ∀ s : ℝ, |s * deriv psi s| ≤ C)
    {N : ℕ} (ε : ℝ) {η : Shape N} (hη : η ∈ shapeConfiguration N) (t : Triple N) :
    |productRadialCoefficient ε η t| ≤ C := by
  have hp : 0 ≤ ∏ u ∈ Finset.univ.erase t, psi (gamma u η / ε) :=
    Finset.prod_nonneg (fun _ _ ↦ psi_nonneg _)
  have hp' : (∏ u ∈ Finset.univ.erase t, psi (gamma u η / ε)) ≤ 1 :=
    Finset.prod_le_one (fun _ _ ↦ psi_nonneg _) (fun _ _ ↦ psi_le_one _)
  rw [productRadialCoefficient, abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ 1 * |radialCutoffCoefficient ε (gamma t η)| :=
      mul_le_mul_of_nonneg_right hp' (abs_nonneg _)
    _ ≤ C := by
      simpa using abs_radialCutoffCoefficient_le hC ε (gamma t η)
        ⟨(gamma_pos t hη).le, (gamma_lt_one t hη).le⟩

/-- The actual differential as a native degree-one alternating form. -/
theorem shapeRadial_as_logRadiusForm {N : ℕ} (s t : Point N) (η : Shape N) :
    ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (shapeRadial s t η) =
      (logRadiusForm (shapeDifference s t η)).compContinuousLinearMap (shapeDerivative s t) := by
  ext v
  rfl

/-- A signed index set turns the radial differences into a plain finite linear combination. -/
abbrev RadialIndex (N : ℕ) := Triple N ⊕ Triple N

def radialFunction {N : ℕ} : RadialIndex N → Shape N → ℂ :=
  Sum.elim (fun t ↦ shapeDifference t.val.1 t.val.2.1)
    (fun t ↦ shapeDifference t.val.1 t.val.2.2)

def signedCoefficient {N : ℕ} (ε : ℝ) (η : Shape N) : RadialIndex N → ℝ :=
  Sum.elim (productRadialCoefficient ε η) (fun t ↦ -productRadialCoefficient ε η t)

theorem fderiv_chi_eq_sum_radial {N : ℕ} (ε : ℝ) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) :
    fderiv ℝ (chi (N := N) ε) η =
      ∑ k : RadialIndex N, signedCoefficient ε η k •
        ((radialLinearCoefficient (radialFunction k η)⁻¹).comp
          (fderiv ℝ (radialFunction k) η)) := by
  rw [(hasFDerivAt_chi_radial ε hη).fderiv]
  ext v
  simp [Fintype.sum_sum_type, signedCoefficient, radialFunction, fderiv_shapeDifference,
    shapeRadial, radialPullback, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, smul_eq_mul, sub_eq_add_neg]

/-- Uniform in epsilon, the configuration, the index, and the number of points. -/
theorem exists_bound_signedCoefficient : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (ε : ℝ) (η : Shape N), η ∈ shapeConfiguration N →
      ∀ k : RadialIndex N, |signedCoefficient ε η k| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_scaled_deriv_psi
  refine ⟨C, hC0, fun N ε η hη k ↦ ?_⟩
  cases k with
  | inl t => exact abs_productRadialCoefficient_le hC ε hη t
  | inr t => simpa [signedCoefficient] using abs_productRadialCoefficient_le hC ε hη t

end EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
