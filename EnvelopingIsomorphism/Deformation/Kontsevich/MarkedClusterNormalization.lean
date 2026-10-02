import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-! Actual marked cluster coordinates. The marked radii use one complex
distance, one imaginary coordinate, or one ordered real gap, with no supremum
over the configuration. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterRescaling

variable {I : Type*}

def pairRadius (b c : I) (p : I → ℂ) : ℝ := ‖p c - p b‖

def pairNormalized (b c : I) (p : I → ℂ) : I → ℂ :=
  fun j => (p j - p b) / (pairRadius b c p : ℂ)

def heightRadius (a : I) (p : I → ℂ) : ℝ := (p a).im

def heightNormalized (a : I) (p : I → ℂ) : I → ℂ :=
  fun j => (p j - ((p a).re : ℂ)) / (heightRadius a p : ℂ)

def orderedRealRadius (b c : I) (p : I → ℂ) : ℝ := (p c).re - (p b).re

def orderedRealNormalized (b c : I) (p : I → ℂ) : I → ℂ :=
  fun j => (p j - ((p b).re : ℂ)) / (orderedRealRadius b c p : ℂ)

theorem continuousAt_pairNormalized (b c : I) (p : I → ℂ) (hp : p b ≠ p c) :
    ContinuousAt (pairNormalized b c) p := by
  apply continuousAt_pi.mpr
  intro j
  apply ContinuousAt.div
  · exact ((continuous_apply j).sub (continuous_apply b)).continuousAt
  · exact (Complex.continuous_ofReal.comp
      ((continuous_apply c).sub (continuous_apply b)).norm).continuousAt
  · exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))

theorem continuousAt_heightNormalized (a : I) (p : I → ℂ) (hp : (p a).im ≠ 0) :
    ContinuousAt (heightNormalized a) p := by
  apply continuousAt_pi.mpr
  intro j
  apply ContinuousAt.div
  · exact ((continuous_apply j).sub
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_apply a)))).continuousAt
  · exact (Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_apply a))).continuousAt
  · exact Complex.ofReal_ne_zero.mpr hp

theorem continuousAt_orderedRealNormalized (b c : I) (p : I → ℂ)
    (hp : orderedRealRadius b c p ≠ 0) : ContinuousAt (orderedRealNormalized b c) p := by
  apply continuousAt_pi.mpr
  intro j
  apply ContinuousAt.div
  · exact ((continuous_apply j).sub
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_apply b)))).continuousAt
  · exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.comp (continuous_apply c)).sub
        (Complex.continuous_re.comp (continuous_apply b)))).continuousAt
  · exact Complex.ofReal_ne_zero.mpr hp

end EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterRescaling
