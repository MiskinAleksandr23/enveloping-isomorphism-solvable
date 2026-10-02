import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Local logarithmic potentials for the actual angular form -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped Topology

/-- A local angle potential whose branch is rotated by the fixed nonzero
constant `c`. It is smooth where `c * z` lies in the principal logarithm's slit plane. -/
def rotatedAnglePotential (c : ℂ) (z : ℂ) : ℝ := (Complex.log (c * z)).im

theorem hasFDerivAt_rotatedAnglePotential {c z : ℂ} (hc : c ≠ 0)
    (hz : c * z ∈ Complex.slitPlane) :
    HasFDerivAt (rotatedAnglePotential c) (angularLinearCoefficient z⁻¹) z := by
  have hm := ((ContinuousLinearMap.mul ℝ ℂ) c).hasFDerivAt (x := z)
  have hl := (Complex.hasStrictFDerivAt_log_real hz).hasFDerivAt.comp z hm
  have hi := Complex.imCLM.hasFDerivAt.comp z hl
  have hder : angularLinearCoefficient z⁻¹ =
      Complex.imCLM.comp (((c * z)⁻¹ • (1 : ℂ →L[ℝ] ℂ)).comp
        ((ContinuousLinearMap.mul ℝ ℂ) c)) := by
    apply ContinuousLinearMap.ext
    intro v
    change (z⁻¹ * v).im = ((c * z)⁻¹ * (c * v)).im
    apply congrArg Complex.im
    have hz₀ : z ≠ 0 := right_ne_zero_of_mul (Complex.slitPlane_ne_zero hz)
    field_simp [hc, hz₀]
  rw [hder]
  exact hi

theorem contDiffAt_rotatedAnglePotential {c z : ℂ}
    (hz : c * z ∈ Complex.slitPlane) : ContDiffAt ℝ ⊤ (rotatedAnglePotential c) z := by
  have hlog : ContDiffAt ℝ ⊤ Complex.log (c * z) :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  exact Complex.imCLM.contDiff.contDiffAt.comp z
    (hlog.comp z (((ContinuousLinearMap.mul ℝ ℂ) c).contDiff.contDiffAt))

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalize the phase at a chosen base point before taking a logarithm. -/
def localAnglePotential (f : E → ℂ) (x₀ : E) (x : E) : ℝ :=
  rotatedAnglePotential (f x₀)⁻¹ (f x)

theorem hasFDerivAt_localAnglePotential {f : E → ℂ} {x₀ x : E}
    (h₀ : f x₀ ≠ 0) (hf : DifferentiableAt ℝ f x)
    (hslit : (f x₀)⁻¹ * f x ∈ Complex.slitPlane) :
    HasFDerivAt (localAnglePotential f x₀)
      ((angularLinearCoefficient (f x)⁻¹).comp (fderiv ℝ f x)) x :=
  (hasFDerivAt_rotatedAnglePotential (inv_ne_zero h₀) hslit).comp x hf.hasFDerivAt

theorem contDiffAt_localAnglePotential {f : E → ℂ} {x₀ : E}
    (h₀ : f x₀ ≠ 0) (hf : ContDiffAt ℝ ⊤ f x₀) :
    ContDiffAt ℝ ⊤ (localAnglePotential f x₀) x₀ := by
  have hslit : (f x₀)⁻¹ * f x₀ ∈ Complex.slitPlane := by simp [h₀]
  exact (contDiffAt_rotatedAnglePotential hslit).comp x₀ hf

omit [NormedSpace ℝ E] in
theorem eventually_localAngle_slit {f : E → ℂ} {x₀ : E}
    (h₀ : f x₀ ≠ 0) (hf : ContinuousAt f x₀) :
    ∀ᶠ x in 𝓝 x₀, (f x₀)⁻¹ * f x ∈ Complex.slitPlane := by
  have hslit : (f x₀)⁻¹ * f x₀ ∈ Complex.slitPlane := by simp [h₀]
  exact (continuousAt_const.mul hf) (Complex.isOpen_slitPlane.mem_nhds hslit)

end Pullback

end EnvelopingIsomorphism.Deformation.Kontsevich
