import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import EnvelopingIsomorphism.Deformation.Kontsevich.Phase
import Mathlib.Tactic.FinCases

/-! The two-interior-point collision at the normalized point `I`. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped UpperHalfPlane Topology

theorem twoInterior_im_pos (r : ℝ) (u : Circle) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 < (Complex.I + (r : ℂ) * (u : ℂ)).im := by
  have hu : -1 ≤ (u : ℂ).im := by
    have h := Complex.abs_im_le_norm (u : ℂ)
    rw [Circle.norm_coe] at h
    exact (abs_le.mp h).1
  simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  nlinarith

/-- The moving upper-half-plane point in the elementary collision chart. -/
def twoInteriorMovingPoint (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) : ℍ :=
  ⟨Complex.I + (r : ℂ) * (u : ℂ), twoInterior_im_pos r u hr.le hr1⟩

@[simp] theorem twoInteriorMovingPoint_coe (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    (twoInteriorMovingPoint r u hr hr1 : ℂ) = Complex.I + (r : ℂ) * (u : ℂ) := rfl

theorem twoInteriorMovingPoint_ne_I (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    twoInteriorMovingPoint r u hr hr1 ≠ UpperHalfPlane.I := by
  intro h
  have h' := congrArg (fun z : ℍ ↦ (z : ℂ)) h
  change Complex.I + (r : ℂ) * (u : ℂ) = Complex.I at h'
  have hz : (r : ℂ) * (u : ℂ) = 0 := add_left_cancel (h'.trans (add_zero Complex.I).symm)
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') u.coe_ne_zero hz

/-- An actual configuration with two distinct interior points and no boundary points. -/
def twoInteriorConfiguration (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    Configuration 2 0 where
  interior := ![UpperHalfPlane.I, twoInteriorMovingPoint r u hr hr1]
  boundary := Fin.elim0
  interior_injective := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (twoInteriorMovingPoint_ne_I r u hr hr1 (by simpa using h.symm)).elim
    · exact (twoInteriorMovingPoint_ne_I r u hr hr1 (by simpa using h)).elim
    · rfl
  boundary_strictMono := by intro i; exact Fin.elim0 i

/-- The collision curve is already normalized at its first interior label. -/
def twoInteriorNormalized (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    Configuration.Normalized (0 : Fin 2) 0 :=
  ⟨twoInteriorConfiguration r u hr hr1, rfl⟩

@[simp] theorem twoInteriorConfiguration_zero (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    ((twoInteriorConfiguration r u hr hr1).interior 0 : ℂ) = Complex.I := rfl

@[simp] theorem twoInteriorConfiguration_one (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    ((twoInteriorConfiguration r u hr hr1).interior 1 : ℂ) = Complex.I + (r : ℂ) * (u : ℂ) := rfl

/-- The analytic chart before restricting the direction to the unit circle. -/
def twoInteriorPair (x : ℝ × ℂ) : ℂ × ℂ :=
  (Complex.I, Complex.I + (x.1 : ℂ) * x.2)

/-- Divide out the positive radial factor from the harmonic ratio. -/
def twoInteriorRegularizedRatio (x : ℝ × ℂ) : ℂ :=
  x.2 / (2 * Complex.I + (x.1 : ℂ) * x.2)

theorem harmonicRatio_twoInteriorPair (r : ℝ) (z : ℂ) :
    harmonicRatio (twoInteriorPair (r, z)).1 (twoInteriorPair (r, z)).2 =
      (r : ℂ) * z / (2 * Complex.I + (r : ℂ) * z) := by
  simp only [twoInteriorPair, harmonicRatio, Complex.conj_I, add_sub_cancel_left,
    sub_neg_eq_add]
  congr 1
  ring

theorem harmonicRatio_twoInteriorPair_factor (x : ℝ × ℂ) :
    harmonicRatio (twoInteriorPair x).1 (twoInteriorPair x).2 =
      (x.1 : ℂ) * twoInteriorRegularizedRatio x := by
  rw [harmonicRatio_twoInteriorPair, twoInteriorRegularizedRatio, mul_div_assoc]

@[simp] theorem twoInteriorRegularizedRatio_zero (z : ℂ) :
    twoInteriorRegularizedRatio (0, z) = z / (2 * Complex.I) := by
  simp [twoInteriorRegularizedRatio]

theorem two_mul_I_ne_zero : (2 : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (by norm_num) Complex.I_ne_zero

theorem twoInteriorRegularizedRatio_zero_ne_zero {z : ℂ} (hz : z ≠ 0) :
    twoInteriorRegularizedRatio (0, z) ≠ 0 := by
  rw [twoInteriorRegularizedRatio_zero]
  exact div_ne_zero hz two_mul_I_ne_zero

theorem complexPhase_twoInteriorPair (r : ℝ) (z : ℂ) (hr : 0 < r) :
    complexPhase (harmonicRatio (twoInteriorPair (r, z)).1 (twoInteriorPair (r, z)).2) =
      complexPhase (twoInteriorRegularizedRatio (r, z)) := by
  rw [harmonicRatio_twoInteriorPair_factor]
  exact complexPhase_pos_real_mul hr _

/-- The boundary direction differs from `u` by the constant quarter turn `1/I`. -/
theorem complexPhase_twoInteriorRegularizedRatio_zero (u : Circle) :
    (complexPhase (twoInteriorRegularizedRatio (0, (u : ℂ))) : ℂ) = (u : ℂ) / Complex.I := by
  rw [twoInteriorRegularizedRatio_zero, complexPhase_div u.coe_ne_zero two_mul_I_ne_zero]
  have hphase : complexPhase ((2 : ℂ) * Complex.I) = complexPhase Complex.I :=
    complexPhase_pos_real_mul (r := 2) (by norm_num) Complex.I
  rw [hphase, Circle.coe_div, complexPhase_circle, complexPhase_coe Complex.I_ne_zero]
  simp

theorem contDiffAt_twoInteriorRegularizedRatio (x : ℝ × ℂ)
    (hd : 2 * Complex.I + (x.1 : ℂ) * x.2 ≠ 0) :
    ContDiffAt ℝ ⊤ twoInteriorRegularizedRatio x := by
  have hr : ContDiffAt ℝ ⊤ (fun y : ℝ × ℂ ↦ (y.1 : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x contDiffAt_fst
  have hden : ContDiffAt ℝ ⊤ (fun y : ℝ × ℂ ↦ 2 * Complex.I + (y.1 : ℂ) * y.2) x :=
    contDiffAt_const.add (hr.mul contDiffAt_snd)
  have hnum : ContDiffAt ℝ ⊤ (fun y : ℝ × ℂ ↦ y.2) x := contDiffAt_snd
  change ContDiffAt ℝ ⊤ (fun y : ℝ × ℂ ↦ y.2 / (2 * Complex.I + (y.1 : ℂ) * y.2)) x
  simpa only [div_eq_mul_inv, Pi.inv_apply] using hnum.mul (hden.inv hd)

theorem contDiffAt_twoInteriorRegularizedRatio_zero (z : ℂ) :
    ContDiffAt ℝ ⊤ twoInteriorRegularizedRatio (0, z) :=
  contDiffAt_twoInteriorRegularizedRatio (0, z) (by simp)

theorem continuousAt_twoInteriorPhase_zero (u : Circle) :
    ContinuousAt (fun x : ℝ × ℂ ↦ complexPhase (twoInteriorRegularizedRatio x)) (0, (u : ℂ)) :=
  (continuousAt_complexPhase (twoInteriorRegularizedRatio_zero_ne_zero u.coe_ne_zero)).comp
    (contDiffAt_twoInteriorRegularizedRatio_zero (u : ℂ)).continuousAt

/-- The actual ambient one-form obtained after cancelling the radial factor. -/
def twoInteriorExtendedForm (x : ℝ × ℂ) : (ℝ × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (twoInteriorRegularizedRatio x)).compContinuousLinearMap
    (fderiv ℝ twoInteriorRegularizedRatio x)

theorem twoInteriorExtendedForm_eq (x : ℝ × ℂ) :
    twoInteriorExtendedForm x = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((angularLinearCoefficient (twoInteriorRegularizedRatio x)⁻¹).comp
        (fderiv ℝ twoInteriorRegularizedRatio x)) := by
  ext v
  rfl

theorem contDiffAt_twoInteriorExtendedForm (x : ℝ × ℂ)
    (hd : 2 * Complex.I + (x.1 : ℂ) * x.2 ≠ 0) (hz : x.2 ≠ 0) :
    ContDiffAt ℝ ⊤ twoInteriorExtendedForm x := by
  have hf := contDiffAt_twoInteriorRegularizedRatio x hd
  have hr : twoInteriorRegularizedRatio x ≠ 0 := div_ne_zero hz hd
  rw [funext twoInteriorExtendedForm_eq]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℝ × ℂ) (F := ℝ)
    (0 : Fin 1)).contDiff.contDiffAt.comp x
      ((angularLinearCoefficient.contDiff.contDiffAt.comp x (hf.inv hr)).clm_comp
        (hf.fderiv_right (by simp)))

/-- The one-form is smooth at every point of the circle face, including radius zero. -/
theorem contDiffAt_twoInteriorExtendedForm_zero (u : Circle) :
    ContDiffAt ℝ ⊤ twoInteriorExtendedForm (0, (u : ℂ)) :=
  contDiffAt_twoInteriorExtendedForm (0, (u : ℂ)) (by simp) u.coe_ne_zero

/-- Inclusion of the collision face into the ambient radial-direction chart. -/
def twoInteriorFaceEmbedding : ℂ →L[ℝ] ℝ × ℂ :=
  (0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)

@[simp] theorem twoInteriorFaceEmbedding_apply (z : ℂ) :
    twoInteriorFaceEmbedding z = (0, z) := rfl

/-- The collision-face restriction is exactly the global angular form in the direction variable. -/
theorem twoInteriorExtendedForm_face (z : ℂ) :
    (twoInteriorExtendedForm (0, z)).compContinuousLinearMap twoInteriorFaceEmbedding =
      angularForm z := by
  let C : ℂ →L[ℝ] ℂ := (2 * Complex.I)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hfun : twoInteriorRegularizedRatio ∘ twoInteriorFaceEmbedding = (C : ℂ → ℂ) := by
    funext u
    simp [twoInteriorRegularizedRatio, C, div_eq_mul_inv, mul_comm]
  have hchain : fderiv ℝ (twoInteriorRegularizedRatio ∘ twoInteriorFaceEmbedding) z =
      (fderiv ℝ twoInteriorRegularizedRatio (0, z)).comp
        (fderiv ℝ (twoInteriorFaceEmbedding : ℂ → ℝ × ℂ) z) :=
    fderiv_comp z
      ((contDiffAt_twoInteriorRegularizedRatio_zero z).differentiableAt (by simp))
      twoInteriorFaceEmbedding.differentiableAt
  rw [hfun] at hchain
  simp only [ContinuousLinearMap.fderiv] at hchain
  ext v
  have heval := congrArg (fun f : ℂ →L[ℝ] ℂ ↦ f (v 0)) hchain.symm
  change fderiv ℝ twoInteriorRegularizedRatio (0, z) (twoInteriorFaceEmbedding (v 0)) =
    (2 * Complex.I)⁻¹ * v 0 at heval
  simp only [twoInteriorExtendedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, Function.comp_apply, heval, twoInteriorRegularizedRatio_zero]
  rw [mul_comm (2 * Complex.I)⁻¹ (v 0), ← div_eq_mul_inv, div_div_div_comm,
    div_self two_mul_I_ne_zero, div_one]

theorem differentiableAt_twoInteriorPair (x : ℝ × ℂ) : DifferentiableAt ℝ twoInteriorPair x := by
  have hr : DifferentiableAt ℝ (fun y : ℝ × ℂ ↦ (y.1 : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x differentiableAt_fst
  have hq : DifferentiableAt ℝ (fun y : ℝ × ℂ ↦ Complex.I + (y.1 : ℂ) * y.2) x :=
    (differentiableAt_const Complex.I).add (hr.mul differentiableAt_snd)
  exact (differentiableAt_const Complex.I).prodMk hq

/-- The extra radial logarithmic derivative is real, so contributes no angular one-form. -/
theorem twoInterior_logDerivative (r dr : ℝ) (z dz : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) :
    (((r : ℂ) * dz + z * (dr : ℂ)) / ((r : ℂ) * z)).im = (dz / z).im := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have heq : ((r : ℂ) * dz + z * (dr : ℂ)) / ((r : ℂ) * z) =
      dz / z + ((dr / r : ℝ) : ℂ) := by
    push_cast
    field_simp [hrC, hz]
  rw [heq, Complex.add_im, Complex.ofReal_im, add_zero]

/-- Away from radius zero, the smooth extended form is exactly the actual harmonic pullback. -/
theorem harmonicAngleForm_twoInteriorPair (x : ℝ × ℂ) (hr : x.1 ≠ 0) (hz : x.2 ≠ 0)
    (hd : 2 * Complex.I + (x.1 : ℂ) * x.2 ≠ 0) :
    (harmonicAngleForm (twoInteriorPair x)).compContinuousLinearMap (fderiv ℝ twoInteriorPair x) =
      twoInteriorExtendedForm x := by
  have hpden : (twoInteriorPair x).2 - conj (twoInteriorPair x).1 ≠ 0 := by
    have heq : (twoInteriorPair x).2 - conj (twoInteriorPair x).1 =
        2 * Complex.I + (x.1 : ℂ) * x.2 := by
      simp only [twoInteriorPair, Complex.conj_I, sub_neg_eq_add]
      ring
    rwa [heq]
  have hcomp : (fun z : ℂ × ℂ ↦ harmonicRatio z.1 z.2) ∘ twoInteriorPair =
      fun y : ℝ × ℂ ↦ (y.1 : ℂ) * twoInteriorRegularizedRatio y :=
    funext harmonicRatio_twoInteriorPair_factor
  have hreal : HasFDerivAt (fun y : ℝ × ℂ ↦ (y.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℂ)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hasFDerivAt_fst
  have hreg : HasFDerivAt twoInteriorRegularizedRatio (fderiv ℝ twoInteriorRegularizedRatio x) x :=
    ((contDiffAt_twoInteriorRegularizedRatio x hd).differentiableAt (by simp)).hasFDerivAt
  rw [harmonicAngleForm_pullback _ _ (differentiableAt_twoInteriorPair x) hpden,
    hcomp, (hreal.fun_mul hreg).fderiv, harmonicRatio_twoInteriorPair_factor]
  ext v
  simp only [twoInteriorExtendedForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply]
  change (((x.1 : ℂ) * (fderiv ℝ twoInteriorRegularizedRatio x (v 0)) +
      twoInteriorRegularizedRatio x * ((v 0).1 : ℂ)) /
        ((x.1 : ℂ) * twoInteriorRegularizedRatio x)).im =
      ((fderiv ℝ twoInteriorRegularizedRatio x (v 0)) / twoInteriorRegularizedRatio x).im
  exact twoInterior_logDerivative x.1 (v 0).1 _ _ hr (div_ne_zero hz hd)

theorem twoInteriorDenominator_ne_zero (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    2 * Complex.I + (r : ℂ) * (u : ℂ) ≠ 0 := by
  have h := harmonicDenominator_ne_zero (p := Complex.I)
    (q := Complex.I + (r : ℂ) * (u : ℂ)) (by norm_num)
    (twoInterior_im_pos r u hr.le hr1).le
  have heq : Complex.I + (r : ℂ) * (u : ℂ) - conj Complex.I =
      2 * Complex.I + (r : ℂ) * (u : ℂ) := by
    rw [Complex.conj_I]
    ring
  rwa [heq] at h

/-- The regularized form agrees with the actual configuration edge form for every `0<r<1`. -/
theorem harmonicAngleForm_twoInteriorCircle (r : ℝ) (u : Circle) (hr : 0 < r) (hr1 : r < 1) :
    (harmonicAngleForm (twoInteriorPair (r, (u : ℂ)))).compContinuousLinearMap
      (fderiv ℝ twoInteriorPair (r, (u : ℂ))) = twoInteriorExtendedForm (r, (u : ℂ)) :=
  harmonicAngleForm_twoInteriorPair (r, (u : ℂ)) hr.ne' u.coe_ne_zero
    (twoInteriorDenominator_ne_zero r u hr hr1)

end EnvelopingIsomorphism.Deformation.Kontsevich
