import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialForms
import EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant

/-!
Actual logarithmic monomial differentials have the shared-radial-row matrix
form required by the simple-pole cancellation theorem. The normalized radial
rows have uniform norm bounds even as a normal coordinate tends to zero.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open scoped BigOperators

def unitRadial (z v : ℂ) : ℝ := ‖z‖ * (v / z).re

theorem radial_eq_inv_norm_mul_unitRadial (z v : ℂ) :
    (v / z).re = (1 / ‖z‖) * unitRadial z v := by
  by_cases hz : z = 0
  · simp [hz, unitRadial]
  · rw [unitRadial, ← mul_assoc, one_div_mul_cancel (norm_ne_zero_iff.mpr hz), one_mul]

theorem abs_unitRadial_le (z v : ℂ) : |unitRadial z v| ≤ ‖v‖ := by
  by_cases hz : z = 0
  · simp [hz, unitRadial]
  · rw [unitRadial, abs_mul, abs_of_nonneg (norm_nonneg z)]
    calc
      ‖z‖ * |(v / z).re| ≤ ‖z‖ * (‖v‖ / ‖z‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [norm_div] using Complex.abs_re_le_norm (v / z))
          (norm_nonneg z)
      _ = ‖v‖ := mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coordinateMonomial (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (i : I) (x : J → ℂ) : ℂ :=
  value (a i) (u i x) x

def smoothRows (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (x : J → ℂ) : Matrix I I ℝ :=
  fun i j => (fderiv ℝ (u i) x (v j) / u i x).re

def unitRadialRows (v : I → J → ℂ) (x : J → ℂ) : J → I → ℝ :=
  fun ν j => unitRadial (x ν) (v j ν)

def integerCoefficients (a : I → J → ℤ) : I → J → ℝ := fun i ν => (a i ν : ℝ)

def actualRadialMatrix (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) (x : J → ℂ) : Matrix I I ℝ :=
  fun i j => (fderiv ℝ (coordinateMonomial a u i) x (v j) / coordinateMonomial a u i x).re

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem actualRadialMatrix_eq (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) {x : J → ℂ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0)
    (hx : ∀ ν, x ν ≠ 0) :
    actualRadialMatrix a u v x = RadialPoleDeterminant.matrix (smoothRows u v x)
      (unitRadialRows v x) (integerCoefficients a) (fun ν => 1 / ‖x ν‖) := by
  ext i j
  have hcoord (ν : J) : DifferentiableAt ℝ (fun y : J → ℂ => y ν) x :=
    (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ).differentiableAt
  have h := radial_pullback_apply (a i) (u i) (fun ν (y : J → ℂ) => y ν)
    (hu i) hcoord (hu0 i) hx (fun _ : Fin 1 => v j)
  have hproj (ν : J) : fderiv ℝ (fun y : J → ℂ => y ν) x =
      (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ) := by
    have he : (fun y : J → ℂ => y ν) =
        (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ) := rfl
    rw [he]
    exact (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ).fderiv
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, logRadiusForm_apply,
    hproj, ContinuousLinearMap.proj_apply] at h
  simp only [RadialPoleDeterminant.matrix, smoothRows, unitRadialRows, integerCoefficients,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (fderiv ℝ (coordinateMonomial a u i) x (v j) / coordinateMonomial a u i x).re = _
  change (fderiv ℝ (coordinateMonomial a u i) x (v j) / coordinateMonomial a u i x).re =
    (fderiv ℝ (u i) x (v j) / u i x).re +
      ∑ ν, ((a i ν : ℝ) * (1 / ‖x ν‖)) * unitRadial (x ν) (v j ν)
  change (fderiv ℝ (coordinateMonomial a u i) x (v j) / coordinateMonomial a u i x).re =
    (fderiv ℝ (u i) x (v j) / u i x).re + ∑ ν, (a i ν : ℝ) * (v j ν / x ν).re at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro ν _
  rw [radial_eq_inv_norm_mul_unitRadial]
  ring

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem unitRadialRows_bound (v : I → J → ℂ) (x : J → ℂ) (ν : J) (j : I) :
    |unitRadialRows v x ν j| ≤ ‖v j ν‖ := abs_unitRadial_le _ _

/-- The pole estimate applies to the actual derivatives of the monomials. -/
theorem abs_actualRadialMatrix_det_le (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (v : I → J → ℂ) {x : J → ℂ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0)
    (hx : ∀ ν, x ν ≠ 0) :
    |Matrix.det (actualRadialMatrix a u v x)| ≤
      RadialPoleDeterminant.coefficientBound (smoothRows u v x)
        (unitRadialRows v x) (integerCoefficients a) * ∏ ν, max 1 (1 / ‖x ν‖) := by
  rw [actualRadialMatrix_eq a u v hu hu0 hx]
  exact RadialPoleDeterminant.abs_det_le_simple_poles _ _ _ _
    (fun ν => div_nonneg zero_le_one (norm_nonneg _))

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
