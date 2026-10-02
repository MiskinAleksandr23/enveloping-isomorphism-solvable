import EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterNormalization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Smooth and real-analytic marked cluster normalization maps on their actual
nonvanishing domains. No supremum-radius function is differentiated here. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterRescaling

open scoped ContDiff

variable {I : Type*} [Fintype I] {ν : ℕ∞ω}

/-- The genuine marked-pair radius is smooth of every order away from coincidence. -/
theorem contDiffAt_pairRadius (b c : I) (p : I → ℂ) (hp : p b ≠ p c) :
    ContDiffAt ℝ ν (pairRadius b c) p := by
  exact (show ContDiffAt ℝ ν (fun q : I → ℂ ↦ q c - q b) p by fun_prop).norm ℂ
    (sub_ne_zero.mpr hp.symm)

/-- The complete actual pair-normalized configuration map is smooth on the same domain. -/
theorem contDiffAt_pairNormalized (b c : I) (p : I → ℂ) (hp : p b ≠ p c) :
    ContDiffAt ℝ ν (pairNormalized b c) p := by
  apply contDiffAt_pi.mpr
  intro j
  simp only [pairNormalized, div_eq_mul_inv]
  apply ContDiffAt.mul
  · fun_prop
  · apply ContDiffAt.inv
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_pairRadius b c p hp)
    · exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))

/-- Height is a genuine continuous linear coordinate on the configuration space. -/
@[fun_prop] theorem contDiff_heightRadius (a : I) : ContDiff ℝ ν (heightRadius a) :=
  Complex.imCLM.contDiff.comp (by fun_prop)

/-- Real-centered height normalization is smooth away from zero height. -/
theorem contDiffAt_heightNormalized (a : I) (p : I → ℂ) (hp : (p a).im ≠ 0) :
    ContDiffAt ℝ ν (heightNormalized a) p := by
  apply contDiffAt_pi.mpr
  intro j
  simp only [heightNormalized, div_eq_mul_inv]
  apply ContDiffAt.mul
  · exact (show ContDiffAt ℝ ν (fun q : I → ℂ ↦ q j) p by fun_prop).sub
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (Complex.reCLM.contDiff.contDiffAt.comp p (by fun_prop)))
  · apply ContDiffAt.inv
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_heightRadius a).contDiffAt
    · exact Complex.ofReal_ne_zero.mpr hp

/-- The ordered real gap is a genuine linear coordinate, without an absolute value. -/
@[fun_prop] theorem contDiff_orderedRealRadius (b c : I) : ContDiff ℝ ν (orderedRealRadius b c) :=
  (Complex.reCLM.contDiff.comp (show ContDiff ℝ ν (fun q : I → ℂ ↦ q c) by fun_prop)).sub
    (Complex.reCLM.contDiff.comp (by fun_prop))

/-- Real-centered ordered normalization is smooth away from zero marked real gap. -/
theorem contDiffAt_orderedRealNormalized (b c : I) (p : I → ℂ)
    (hp : orderedRealRadius b c p ≠ 0) : ContDiffAt ℝ ν (orderedRealNormalized b c) p := by
  apply contDiffAt_pi.mpr
  intro j
  simp only [orderedRealNormalized, div_eq_mul_inv]
  apply ContDiffAt.mul
  · exact (show ContDiffAt ℝ ν (fun q : I → ℂ ↦ q j) p by fun_prop).sub
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (Complex.reCLM.contDiff.contDiffAt.comp p (by fun_prop)))
  · apply ContDiffAt.inv
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_orderedRealRadius b c).contDiffAt
    · exact Complex.ofReal_ne_zero.mpr hp

omit [Fintype I] in
/-- Nonvanishing marked-pair coordinates form an actual open chart domain. -/
theorem isOpen_pairDomain (b c : I) : IsOpen {p : I → ℂ | p b ≠ p c} :=
  isOpen_ne_fun (continuous_apply b) (continuous_apply c)

omit [Fintype I] in
theorem isOpen_heightDomain (a : I) : IsOpen {p : I → ℂ | (p a).im ≠ 0} :=
  isOpen_ne_fun (Complex.continuous_im.comp (continuous_apply a)) continuous_const

theorem isOpen_orderedRealDomain (b c : I) : IsOpen {p : I → ℂ | orderedRealRadius b c p ≠ 0} :=
  isOpen_ne_fun ((contDiff_orderedRealRadius (ν := ∞) b c).continuous) continuous_const

theorem contDiffOn_pairRadius (b c : I) :
    ContDiffOn ℝ ν (pairRadius b c) {p | p b ≠ p c} :=
  fun p hp ↦ (contDiffAt_pairRadius b c p hp).contDiffWithinAt

theorem contDiffOn_pairNormalized (b c : I) :
    ContDiffOn ℝ ν (pairNormalized b c) {p | p b ≠ p c} :=
  fun p hp ↦ (contDiffAt_pairNormalized b c p hp).contDiffWithinAt

theorem contDiffOn_heightNormalized (a : I) :
    ContDiffOn ℝ ν (heightNormalized a) {p | (p a).im ≠ 0} :=
  fun p hp ↦ (contDiffAt_heightNormalized a p hp).contDiffWithinAt

theorem contDiffOn_orderedRealNormalized (b c : I) :
    ContDiffOn ℝ ν (orderedRealNormalized b c) {p | orderedRealRadius b c p ≠ 0} :=
  fun p hp ↦ (contDiffAt_orderedRealNormalized b c p hp).contDiffWithinAt

/-- In the current native calculus API, top order is analytic order ω. -/
theorem analyticAt_pairRadius (b c : I) (p : I → ℂ) (hp : p b ≠ p c) :
    AnalyticAt ℝ (pairRadius b c) p := (contDiffAt_pairRadius (ν := ω) b c p hp).analyticAt

theorem analyticAt_pairNormalized (b c : I) (p : I → ℂ) (hp : p b ≠ p c) :
    AnalyticAt ℝ (pairNormalized b c) p := (contDiffAt_pairNormalized (ν := ω) b c p hp).analyticAt

theorem analyticAt_heightRadius (a : I) (p : I → ℂ) : AnalyticAt ℝ (heightRadius a) p :=
  (contDiff_heightRadius (ν := ω) a).contDiffAt.analyticAt

theorem analyticAt_heightNormalized (a : I) (p : I → ℂ) (hp : (p a).im ≠ 0) :
    AnalyticAt ℝ (heightNormalized a) p := (contDiffAt_heightNormalized (ν := ω) a p hp).analyticAt

theorem analyticAt_orderedRealRadius (b c : I) (p : I → ℂ) :
    AnalyticAt ℝ (orderedRealRadius b c) p := (contDiff_orderedRealRadius (ν := ω) b c).contDiffAt.analyticAt

theorem analyticAt_orderedRealNormalized (b c : I) (p : I → ℂ) (hp : orderedRealRadius b c p ≠ 0) :
    AnalyticAt ℝ (orderedRealNormalized b c) p :=
  (contDiffAt_orderedRealNormalized (ν := ω) b c p hp).analyticAt

end EnvelopingIsomorphism.Deformation.Kontsevich.MarkedClusterRescaling
