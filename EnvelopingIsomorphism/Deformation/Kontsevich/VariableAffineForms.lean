import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Harmonic-form invariance under a parameter-dependent real affine normalization.
All scale and translation derivatives are retained through the actual pullback derivative.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both points undergo the same affine change, with scale and shift depending on the input. -/
def variableAffinePair (f : E → ℂ × ℂ) (s b : E → ℝ) (y : E) : ℂ × ℂ :=
  s y • f y + ((b y : ℂ), (b y : ℂ))

theorem differentiableAt_variableAffinePair (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hs : DifferentiableAt ℝ s x)
    (hb : DifferentiableAt ℝ b x) : DifferentiableAt ℝ (variableAffinePair f s b) x := by
  have hbC : DifferentiableAt ℝ (fun y ↦ (b y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hb
  exact (hs.smul hf).add (hbC.prodMk hbC)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Pointwise cancellation of the common real affine change in the harmonic ratio. -/
theorem harmonicRatio_variableAffinePair (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hpos : 0 < s x) :
    harmonicRatio (variableAffinePair f s b x).1 (variableAffinePair f s b x).2 =
      harmonicRatio (f x).1 (f x).2 := by
  exact harmonicRatio_affinePair ⟨s x, b x, hpos⟩ (f x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The harmonic denominator scales by the actual, possibly variable, real scale. -/
theorem variableAffinePair_denominator (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E) :
    (variableAffinePair f s b x).2 - conj (variableAffinePair f s b x).1 =
      (s x : ℂ) * ((f x).2 - conj (f x).1) := by
  simp only [variableAffinePair, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem variableAffinePair_denominator_ne_zero (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hpos : 0 < s x) (hd : (f x).2 - conj (f x).1 ≠ 0) :
    (variableAffinePair f s b x).2 - conj (variableAffinePair f s b x).1 ≠ 0 := by
  rw [variableAffinePair_denominator]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') hd

omit [NormedSpace ℝ E] in
/-- Positivity at one point suffices: continuity supplies the neighborhood where the ratios agree. -/
theorem harmonicRatio_variableAffinePair_eventuallyEq (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hs : ContinuousAt s x) (hpos : 0 < s x) :
    ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ variableAffinePair f s b) =ᶠ[𝓝 x]
      ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ f) := by
  filter_upwards [hs.eventually (Ioi_mem_nhds hpos)] with y hy
  exact harmonicRatio_variableAffinePair f s b y hy

/-- The full derivatives of the two ratio functions agree, including every ds and db term. -/
theorem fderiv_harmonicRatio_variableAffinePair (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hs : ContinuousAt s x) (hpos : 0 < s x) :
    fderiv ℝ ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ variableAffinePair f s b) x =
      fderiv ℝ ((fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ f) x :=
  (harmonicRatio_variableAffinePair_eventuallyEq f s b x hs hpos).fderiv_eq

/-- Genuine one-form pullback invariance for a varying real affine normalization.
There is no globally positive-scale assumption and no omission of normalization derivatives. -/
theorem harmonicAngleForm_variableAffine_pullback (f : E → ℂ × ℂ) (s b : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hs : DifferentiableAt ℝ s x)
    (hb : DifferentiableAt ℝ b x) (hpos : 0 < s x)
    (hd : (f x).2 - conj (f x).1 ≠ 0) :
    (harmonicAngleForm (variableAffinePair f s b x)).compContinuousLinearMap
        (fderiv ℝ (variableAffinePair f s b) x) =
      (harmonicAngleForm (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  rw [harmonicAngleForm_pullback _ _ (differentiableAt_variableAffinePair f s b x hf hs hb)
      (variableAffinePair_denominator_ne_zero f s b x hpos hd),
    harmonicAngleForm_pullback _ _ hf hd, harmonicRatio_variableAffinePair f s b x hpos,
    fderiv_harmonicRatio_variableAffinePair f s b x hs.continuousAt hpos]

end EnvelopingIsomorphism.Deformation.Kontsevich
