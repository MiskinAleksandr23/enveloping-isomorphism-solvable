import EnvelopingIsomorphism.Deformation.Kontsevich.ForestEdgeForms
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Angular one-forms depend only on the actual circle-valued phase.
This allows full-DR coordinate equalities to transport graph edge forms. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem angularPullback_complexPhase (f : E → ℂ) (x : E)
    (hf : ContDiffAt ℝ ⊤ f x) (hne : f x ≠ 0) :
    angularPullback (fun y ↦ (complexPhase (f y) : ℂ)) x = angularPullback f x := by
  have hs : DifferentiableAt ℝ (fun y ↦ ‖f y‖⁻¹) x :=
    ((hf.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).differentiableAt (by simp)
  have hloc : (fun y ↦ (complexPhase (f y) : ℂ)) =ᶠ[𝓝 x]
      (fun y ↦ ((‖f y‖⁻¹ : ℝ) : ℂ) * f y) := by
    filter_upwards [hf.continuousAt.eventually_ne hne] with y hy
    rw [complexPhase_coe hy, Complex.ofReal_inv]
    exact div_eq_inv_mul _ _
  rw [angularPullback_congr_eventually hloc]
  exact angularPullback_real_mul _ f x hs (hf.differentiableAt (by simp))
    (inv_ne_zero (norm_ne_zero_iff.mpr hne)) hne

/-- Equality of actual DR phases on a neighborhood transports the complete
angular derivative, including all derivatives of normalization factors. -/
theorem angularPullback_eq_of_complexPhase_eventually {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ⊤ f x) (hg : ContDiffAt ℝ ⊤ g x)
    (hfn : f x ≠ 0) (hgn : g x ≠ 0)
    (hphase : (fun y ↦ (complexPhase (f y) : ℂ)) =ᶠ[𝓝 x]
      (fun y ↦ (complexPhase (g y) : ℂ))) :
    angularPullback f x = angularPullback g x := by
  rw [← angularPullback_complexPhase f x hf hfn, ← angularPullback_complexPhase g x hg hgn]
  exact angularPullback_congr_eventually hphase

end EnvelopingIsomorphism.Deformation.Kontsevich
