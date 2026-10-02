import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialMatrix
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialBoundaryDeterminant
import EnvelopingIsomorphism.Deformation.Kontsevich.CircleAngleForm

/-! Boundary-frame factorization of actual logarithmic monomial derivatives.
The shared radial rows and the radial factor of the smooth column are derived
from the actual circle tangent, before invoking the determinant identity.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The unit angular tangent in the distinguished complex coordinate. -/
def unitAngularTangent (ν₀ : J) (θ : ℝ) : J → ℂ := Pi.single ν₀ (Complex.I * circleParameter θ)

/-- A literal boundary frame, replacing its first column by the actual radius-r angular tangent. -/
def boundaryFrame (j₀ : I) (ν₀ : J) (r θ : ℝ) (w : I → J → ℂ) : I → J → ℂ :=
  Function.update w j₀ (r • unitAngularTangent ν₀ θ)

omit [Fintype I] [Fintype J] in
@[simp] theorem boundaryFrame_first (j₀ : I) (ν₀ : J) (r θ : ℝ) (w : I → J → ℂ) :
    boundaryFrame j₀ ν₀ r θ w j₀ = r • unitAngularTangent ν₀ θ := Function.update_self ..

omit [Fintype I] [Fintype J] in
theorem boundaryFrame_rest (j₀ : I) (ν₀ : J) (r θ : ℝ) (w : I → J → ℂ)
    (j : I) (hj : j ≠ j₀) : boundaryFrame j₀ ν₀ r θ w j = w j :=
  Function.update_of_ne hj ..

/-- The actual radial covector annihilates the angular direction, even at r=0. -/
theorem unitRadial_circle_tangent (r θ : ℝ) :
    unitRadial ((r : ℂ) * circleParameter θ) ((r : ℂ) * (Complex.I * circleParameter θ)) = 0 := by
  by_cases hr : r = 0
  · simp [hr, unitRadial]
  · have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have heq : ((r : ℂ) * (Complex.I * circleParameter θ)) / ((r : ℂ) * circleParameter θ) =
        Complex.I := by
      rw [mul_div_mul_left _ _ hrC, mul_div_cancel_right₀ _ (circleParameter_ne_zero θ)]
    rw [unitRadial, heq, Complex.I_re, mul_zero]

omit [Fintype I] [DecidableEq I] [Fintype J] in
/-- Every radial row annihilates the actual first boundary tangent. -/
theorem unitRadialRows_boundary_first (v : I → J → ℂ) (x : J → ℂ)
    (j₀ : I) (ν₀ : J) (r θ : ℝ)
    (hx₀ : x ν₀ = (r : ℂ) * circleParameter θ)
    (hv₀ : v j₀ = r • unitAngularTangent ν₀ θ) :
    ∀ ν, unitRadialRows v x ν j₀ = 0 := by
  intro ν
  by_cases hν : ν = ν₀
  · subst ν
    simp only [unitRadialRows, hv₀, Pi.smul_apply, unitAngularTangent, Pi.single_eq_same,
      Complex.real_smul, hx₀]
    exact unitRadial_circle_tangent r θ
  · simp [unitRadialRows, hv₀, unitAngularTangent, hν, unitRadial]

omit [Fintype I] [Fintype J] in
/-- The distinguished radial row vanishes on the entire tangent frame. -/
theorem unitRadialRows_boundary_distinguished (v : I → J → ℂ) (x : J → ℂ)
    (j₀ : I) (ν₀ : J) (r θ : ℝ)
    (hx₀ : x ν₀ = (r : ℂ) * circleParameter θ)
    (hv₀ : v j₀ = r • unitAngularTangent ν₀ θ)
    (hvrest : ∀ j, j ≠ j₀ → v j ν₀ = 0) : unitRadialRows v x ν₀ = 0 := by
  funext j
  by_cases hj : j = j₀
  · subst j
    exact unitRadialRows_boundary_first v x j₀ ν₀ r θ hx₀ hv₀ ν₀
  · simp [unitRadialRows, unitRadial, hvrest j hj]

/-- The smooth coefficient after extracting the radius from the actual angular column. -/
def angularUnitColumn (u : I → (J → ℂ) → ℂ) (ν₀ : J) (θ : ℝ) (x : J → ℂ) : I → ℝ :=
  fun i ↦ (fderiv ℝ (u i) x (unitAngularTangent ν₀ θ) / u i x).re

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem smoothRows_boundary_first (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (x : J → ℂ)
    (j₀ : I) (ν₀ : J) (r θ : ℝ) (hv₀ : v j₀ = r • unitAngularTangent ν₀ θ) :
    ∀ i, smoothRows u v x i j₀ = r * angularUnitColumn u ν₀ θ x i := by
  intro i
  unfold smoothRows angularUnitColumn
  rw [hv₀, map_smul]
  simp only [Complex.real_smul, mul_div_assoc, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Exact boundary determinant of the actual integer-monomial logarithmic forms.
The distinguished inverse radial parameter is deleted, not merely bounded. -/
theorem det_actualRadialMatrix_boundary
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (x : J → ℂ)
    (j₀ : I) (ν₀ : J) (r θ : ℝ)
    (hx₀ : x ν₀ = (r : ℂ) * circleParameter θ)
    (hv₀ : v j₀ = r • unitAngularTangent ν₀ θ)
    (hvrest : ∀ j, j ≠ j₀ → v j ν₀ = 0)
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    Matrix.det (actualRadialMatrix a u v x) = r * Matrix.det
      (RadialPoleDeterminant.matrix
        ((smoothRows u v x).updateCol j₀ (angularUnitColumn u ν₀ θ x))
        (unitRadialRows v x) (integerCoefficients a) (Function.update (fun ν ↦ 1 / ‖x ν‖) ν₀ 0)) := by
  rw [actualRadialMatrix_eq a u v hu hu0 hx]
  exact RadialBoundaryDeterminant.det_eq_radius_mul_without_pole _ _ _ _ j₀ ν₀ r _
    (smoothRows_boundary_first u v x j₀ ν₀ r θ hv₀)
    (unitRadialRows_boundary_first v x j₀ ν₀ r θ hx₀ hv₀)
    (unitRadialRows_boundary_distinguished v x j₀ ν₀ r θ hx₀ hv₀ hvrest)

/-- The actual monomial-form boundary determinant has radial gain r and only the other simple poles. -/
theorem abs_actualRadialMatrix_boundary_le
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (x : J → ℂ)
    (j₀ : I) (ν₀ : J) (r θ : ℝ) (hr : 0 ≤ r)
    (hx₀ : x ν₀ = (r : ℂ) * circleParameter θ)
    (hv₀ : v j₀ = r • unitAngularTangent ν₀ θ)
    (hvrest : ∀ j, j ≠ j₀ → v j ν₀ = 0)
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    |Matrix.det (actualRadialMatrix a u v x)| ≤
      r * RadialPoleDeterminant.coefficientBound
        ((smoothRows u v x).updateCol j₀ (angularUnitColumn u ν₀ θ x))
        (unitRadialRows v x) (integerCoefficients a) *
          ∏ ν ∈ Finset.univ.erase ν₀, max 1 (1 / ‖x ν‖) := by
  rw [actualRadialMatrix_eq a u v hu hu0 hx]
  simpa only [abs_of_nonneg hr] using
    RadialBoundaryDeterminant.abs_det_le_radius_simple_poles _ _ _ _ j₀ ν₀ r _
      (smoothRows_boundary_first u v x j₀ ν₀ r θ hv₀)
      (unitRadialRows_boundary_first v x j₀ ν₀ r θ hx₀ hv₀)
      (unitRadialRows_boundary_distinguished v x j₀ ν₀ r θ hx₀ hv₀ hvrest)
      (fun ν _ ↦ div_nonneg zero_le_one (norm_nonneg (x ν)))

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
