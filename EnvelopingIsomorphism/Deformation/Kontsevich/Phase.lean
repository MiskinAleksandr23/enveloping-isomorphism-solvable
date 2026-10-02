import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Normalize
import EnvelopingIsomorphism.Deformation.Kontsevich.AngleRatio

/-!
# Complex directions without an argument branch

The phase of a nonzero complex number is its actual normalization on `Circle`.
The value at zero is fixed to one; continuity is asserted only away from zero.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped Topology

/-- The direction of a complex number, with the harmless total value `1` at zero. -/
def complexPhase (z : ℂ) : Circle :=
  if hz : z = 0 then 1
  else ⟨NormedSpace.normalize z, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hz)⟩

@[simp] theorem complexPhase_zero : complexPhase 0 = 1 := by simp [complexPhase]

theorem complexPhase_coe_normalize {z : ℂ} (hz : z ≠ 0) :
    (complexPhase z : ℂ) = NormedSpace.normalize z := by simp [complexPhase, hz]

/-- The exact normalized complex representative of a nonzero phase. -/
theorem complexPhase_coe {z : ℂ} (hz : z ≠ 0) :
    (complexPhase z : ℂ) = z / (‖z‖ : ℂ) := by
  rw [complexPhase_coe_normalize hz]
  simp only [NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

@[simp] theorem complexPhase_one : complexPhase 1 = 1 := by
  apply Circle.ext
  simp [complexPhase_coe one_ne_zero]

/-- Normalization fixes every point already on the unit circle. -/
@[simp] theorem complexPhase_circle (z : Circle) : complexPhase (z : ℂ) = z := by
  apply Circle.ext
  rw [complexPhase_coe z.coe_ne_zero, Circle.norm_coe]
  simp

/-- The total phase map is continuous at every nonzero complex number. -/
theorem continuousAt_complexPhase {z : ℂ} (hz : z ≠ 0) : ContinuousAt complexPhase z := by
  apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hc : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
    continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn
  have hloc : ∀ᶠ w : ℂ in 𝓝 z, w ≠ 0 :=
    (isOpen_ne_fun continuous_id continuous_const).mem_nhds hz
  exact hc.congr_of_eventuallyEq (hloc.mono fun w hw => complexPhase_coe hw)

theorem continuousOn_complexPhase : ContinuousOn complexPhase ({0}ᶜ : Set ℂ) := by
  intro z hz
  exact (continuousAt_complexPhase (by simpa using hz)).continuousWithinAt

/-- Positive real scaling does not change a complex direction, including the chosen value at zero. -/
theorem complexPhase_pos_real_smul {r : ℝ} (hr : 0 < r) (z : ℂ) :
    complexPhase (r • z) = complexPhase z := by
  by_cases hz : z = 0
  · simp [hz]
  · apply Circle.ext
    rw [complexPhase_coe_normalize (smul_ne_zero hr.ne' hz), complexPhase_coe_normalize hz,
      NormedSpace.normalize_smul_of_pos hr]

theorem complexPhase_pos_real_mul {r : ℝ} (hr : 0 < r) (z : ℂ) :
    complexPhase ((r : ℂ) * z) = complexPhase z :=
  complexPhase_pos_real_smul hr z

/-- Negation reverses every nonzero direction. -/
theorem complexPhase_neg {z : ℂ} (hz : z ≠ 0) : complexPhase (-z) = -complexPhase z := by
  apply Circle.ext
  rw [Circle.coe_neg, complexPhase_coe_normalize (neg_ne_zero.mpr hz),
    complexPhase_coe_normalize hz, NormedSpace.normalize_neg]

/-- Complex conjugation reverses the phase in the circle group. -/
theorem complexPhase_conj (z : ℂ) : complexPhase (conj z) = (complexPhase z)⁻¹ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hcz : conj z ≠ 0 := by
      intro h
      apply hz
      have he := congrArg (starRingEnd ℂ) h
      simpa using he
    apply Circle.ext
    rw [complexPhase_coe hcz, Circle.coe_inv_eq_conj, complexPhase_coe hz, Complex.norm_conj]
    simp only [map_div₀, Complex.conj_ofReal]

/-- Division of nonzero complex numbers becomes division of their actual unit directions. -/
theorem complexPhase_div {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    complexPhase (z / w) = complexPhase z / complexPhase w := by
  apply Circle.ext
  rw [complexPhase_coe (div_ne_zero hz hw), Circle.coe_div, complexPhase_coe hz,
    complexPhase_coe hw, norm_div, Complex.ofReal_div]
  exact div_div_div_comm _ _ _ _

/-- Multiplication also respects the unit directions of nonzero complex numbers. -/
theorem complexPhase_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    complexPhase (z * w) = complexPhase z * complexPhase w := by
  apply Circle.ext
  rw [complexPhase_coe (mul_ne_zero hz hw), Circle.coe_mul, complexPhase_coe hz,
    complexPhase_coe hw, norm_mul, Complex.ofReal_mul]
  exact mul_div_mul_comm _ _ _ _

/-- The harmonic angle phase is the quotient of the two pair directions. -/
theorem complexPhase_harmonicRatio {p q : ℂ} (hnum : q - p ≠ 0) (hden : q - conj p ≠ 0) :
    complexPhase (harmonicRatio p q) = complexPhase (q - p) / complexPhase (q - conj p) :=
  complexPhase_div hnum hden

theorem complexPhase_harmonicRatio_upper {p q : ℂ} (hp : 0 < p.im) (hq : 0 ≤ q.im)
    (hne : q ≠ p) :
    complexPhase (harmonicRatio p q) = complexPhase (q - p) / complexPhase (q - conj p) :=
  complexPhase_harmonicRatio (sub_ne_zero.mpr hne) (harmonicDenominator_ne_zero hp hq)

/-- Quotient of directions is continuous everywhere on the product of the two circles. -/
theorem continuous_circle_direction_quotient : Continuous (fun p : Circle × Circle => p.1 / p.2) := by
  exact continuous_mul.comp (continuous_fst.prodMk (continuous_inv.comp continuous_snd))

end EnvelopingIsomorphism.Deformation.Kontsevich
