import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadiusForm
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Actual logarithmic derivatives of distance ratios on the noncollision locus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback of the real radial logarithmic differential. -/
def radialPullback (f : E → ℂ) (D : E →L[ℝ] ℂ) (x : E) : E →L[ℝ] ℝ :=
  (radialLinearCoefficient (f x)⁻¹).comp D

/-- Bounded normalized distance ratio; no branch of complex log occurs. -/
def logDistanceRatio (f g : E → ℂ) (x : E) : ℝ := ‖f x‖ / (‖f x‖ + ‖g x‖)

theorem logDistanceRatio_pos {f g : E → ℂ} {x : E} (hf : f x ≠ 0) :
    0 < logDistanceRatio f g x :=
  div_pos (norm_pos_iff.mpr hf) (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hf) (norm_nonneg _))

theorem logDistanceRatio_lt_one {f g : E → ℂ} {x : E} (hg : g x ≠ 0) :
    logDistanceRatio f g x < 1 := by
  unfold logDistanceRatio
  exact (div_lt_one (add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.mpr hg))).mpr
    (lt_add_of_pos_right _ (norm_pos_iff.mpr hg))

theorem hasFDerivAt_norm_radial {f : E → ℂ} {D : E →L[ℝ] ℂ} {x : E}
    (hf : HasFDerivAt f D x) (hne : f x ≠ 0) :
    HasFDerivAt (fun y ↦ ‖f y‖) (‖f x‖ • radialPullback f D x) x := by
  have hn := (hf.differentiableAt.norm ℝ hne).hasFDerivAt
  have he := (hn.log (norm_ne_zero_iff.mpr hne)).unique (hasFDerivAt_log_norm_comp hf hne)
  have he' := congrArg (fun d : E →L[ℝ] ℝ ↦ ‖f x‖ • d) he
  simp only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul] at he'
  exact he' ▸ hn

theorem hasFDerivAt_logDistanceRatio {f g : E → ℂ} {Df Dg : E →L[ℝ] ℂ} {x : E}
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hfn : f x ≠ 0) (hgn : g x ≠ 0) :
    HasFDerivAt (logDistanceRatio f g)
      ((logDistanceRatio f g x * (1 - logDistanceRatio f g x)) •
        (radialPullback f Df x - radialPullback g Dg x)) x := by
  have hnf := hasFDerivAt_norm_radial hf hfn
  have hng := hasFDerivAt_norm_radial hg hgn
  have hden : ‖f x‖ + ‖g x‖ ≠ 0 := ne_of_gt
    (add_pos (norm_pos_iff.mpr hfn) (norm_pos_iff.mpr hgn))
  have hi := (hasDerivAt_inv hden).comp_hasFDerivAt x (hnf.add hng)
  convert! hnf.mul hi using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, logDistanceRatio, Function.comp_apply, Pi.add_apply]
  field_simp [hden]
  <;> ring

theorem hasFDerivAt_log_logDistanceRatio {f g : E → ℂ} {Df Dg : E →L[ℝ] ℂ} {x : E}
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hfn : f x ≠ 0) (hgn : g x ≠ 0) :
    HasFDerivAt (fun y ↦ Real.log (logDistanceRatio f g y))
      ((1 - logDistanceRatio f g x) •
        (radialPullback f Df x - radialPullback g Dg x)) x := by
  have h := (hasFDerivAt_logDistanceRatio hf hg hfn hgn).log
    (ne_of_gt (logDistanceRatio_pos hfn))
  simpa only [smul_smul, inv_mul_cancel_left₀ (ne_of_gt (logDistanceRatio_pos hfn))] using h

/-- Chain rule: the coefficient multiplies radial forms; its derivatives are never needed. -/
theorem hasFDerivAt_distanceRatio_cutoff {f g : E → ℂ} {Df Dg : E →L[ℝ] ℂ} {x : E}
    {ψ : ℝ → ℝ} {ε ψ' : ℝ}
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hfn : f x ≠ 0) (hgn : g x ≠ 0)
    (hψ : HasDerivAt ψ ψ' (logDistanceRatio f g x / ε)) :
    HasFDerivAt (fun y ↦ ψ (logDistanceRatio f g y / ε))
      (((logDistanceRatio f g x / ε) * ψ' * (1 - logDistanceRatio f g x)) •
        (radialPullback f Df x - radialPullback g Dg x)) x := by
  convert! hψ.comp_hasFDerivAt x ((hasFDerivAt_logDistanceRatio hf hg hfn hgn).mul_const ε⁻¹) using 1
  ext v
  simp only [smul_apply, sub_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich
