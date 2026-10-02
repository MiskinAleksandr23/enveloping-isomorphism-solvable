import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadiusForm
import EnvelopingIsomorphism.Deformation.Kontsevich.AngularRadialDeterminant
import EnvelopingIsomorphism.Deformation.Kontsevich.AlternatingPullbackSmooth

/-!
An explicit primitive for a determinant of logarithmic radial differentials.
This proves exactness on the complement of the zero loci. Integrability and
vanishing of boundary integrals are separate analytic obligations.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive

open ContinuousAlternatingMap

abbrev Coord (n : ℕ) := Fin n → ℝ

def tailProjection (n : ℕ) : Coord (n + 1) →L[ℝ] Coord n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

def coordinatePrimitive (n : ℕ) (x : Coord (n + 1)) :
    Coord (n + 1) [⋀^Fin n]→L[ℝ] ℝ :=
  x 0 • (coordinateVolume n).compContinuousLinearMap (tailProjection n)

theorem contDiff_coordinatePrimitive (n : ℕ) : ContDiff ℝ ⊤ (coordinatePrimitive n) :=
  (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).smul contDiff_const

theorem extDeriv_coordinatePrimitive (n : ℕ) (x : Coord (n + 1)) :
    extDeriv (coordinatePrimitive n) x = coordinateVolume (n + 1) := by
  have hd := (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
    Coord (n + 1) →L[ℝ] ℝ).hasFDerivAt (x := x) |>.smul_const
      ((coordinateVolume n).compContinuousLinearMap (tailProjection n))
  simp only [ContinuousLinearMap.proj_apply] at hd
  unfold extDeriv coordinatePrimitive
  rw [hd.fderiv]
  ext v
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val *
    (v i 0 * Matrix.det (fun a b : Fin n => v (i.succAbove a) b.succ))) =
      Matrix.det (fun a b : Fin (n + 1) => v a b)
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Matrix.submatrix (fun a b : Fin (n + 1) => v a b) i.succAbove Fin.succ =
      (fun a b : Fin n => v (i.succAbove a) b.succ) := rfl
  rw [hm]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def logarithms (f : Fin (n + 1) → E → ℂ) (x : E) : Coord (n + 1) :=
  fun i => Real.log ‖f i x‖

def logarithmDerivative (f : Fin (n + 1) → E → ℂ) (x : E) :
    E →L[ℝ] Coord (n + 1) :=
  ContinuousLinearMap.pi fun i =>
    (radialLinearCoefficient (f i x)⁻¹).comp (fderiv ℝ (f i) x)

theorem contDiffAt_logarithms (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, ContDiffAt ℝ ⊤ (f i) x) (hne : ∀ i, f i x ≠ 0) :
    ContDiffAt ℝ ⊤ (logarithms f) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((hf i).norm ℂ (hne i)).log (norm_ne_zero_iff.mpr (hne i))

theorem hasFDerivAt_logarithms (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (hne : ∀ i, f i x ≠ 0) :
    HasFDerivAt (logarithms f) (logarithmDerivative f x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_log_norm_comp (hf i).hasFDerivAt (hne i)

def primitive (f : Fin (n + 1) → E → ℂ) (x : E) : E [⋀^Fin n]→L[ℝ] ℝ :=
  (coordinatePrimitive n (logarithms f x)).compContinuousLinearMap
    (fderiv ℝ (logarithms f) x)

def radialForm (f : Fin (n + 1) → E → ℂ) (x : E) :
    E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  (coordinateVolume (n + 1)).compContinuousLinearMap (logarithmDerivative f x)

theorem primitive_apply (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (hne : ∀ i, f i x ≠ 0)
    (v : Fin n → E) :
    primitive f x v = Real.log ‖f 0 x‖ * Matrix.det (fun i j =>
      (fderiv ℝ (f j.succ) x (v i) / f j.succ x).re) := by
  unfold primitive
  rw [(hasFDerivAt_logarithms f hf hne).fderiv]
  change Real.log ‖f 0 x‖ * Matrix.det
    (fun i j => ((f j.succ x)⁻¹ * fderiv ℝ (f j.succ) x (v i)).re) = _
  simp only [div_eq_inv_mul]

theorem contDiffAt_primitive (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, ContDiffAt ℝ ⊤ (f i) x) (hne : ∀ i, f i x ≠ 0) :
    ContDiffAt ℝ ⊤ (primitive f) x := by
  have hlog := contDiffAt_logarithms f hf hne
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ (logarithms f)) x :=
    hlog.fderiv_right (by simp)
  have hP := (contDiff_compContinuousLinearMap
    ((coordinateVolume n).compContinuousLinearMap (tailProjection n))).contDiffAt.comp x hD
  have hfirst : ContDiffAt ℝ ⊤ (fun y => logarithms f y 0) x :=
    (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).contDiffAt.comp x hlog
  convert hfirst.smul hP using 1
  funext y
  ext v
  rfl

theorem extDeriv_primitive (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, ContDiffAt ℝ ⊤ (f i) x) (hne : ∀ i, f i x ≠ 0) :
    extDeriv (primitive f) x = radialForm f x := by
  unfold primitive
  rw [extDeriv_pullback
    ((contDiff_coordinatePrimitive n).differentiable (by simp)).differentiableAt
    (contDiffAt_logarithms f hf hne) (by simp), extDeriv_coordinatePrimitive,
    (hasFDerivAt_logarithms f (fun i => (hf i).differentiableAt (by simp)) hne).fderiv]
  rfl

theorem radialForm_apply (f : Fin (n + 1) → E → ℂ) (x : E)
    (v : Fin (n + 1) → E) :
    radialForm f x v = Matrix.det (fun i j =>
      (fderiv ℝ (f j) x (v i) / f j x).re) := by
  change Matrix.det (fun i j => ((f j x)⁻¹ * fderiv ℝ (f j) x (v i)).re) = _
  simp only [div_eq_inv_mul]

/-- Reindexing the angular/radial identity to any explicitly matching top degree. -/
theorem det_im_eq_det_re_of_dimension {N : ℕ} (hdim : n + 1 = N * 2)
    (ℓ : Fin (n + 1) → AngularRadial.Coordinates N →ₗ[ℂ] ℂ)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) :
    Matrix.det (fun i j => (ℓ j (v i)).im) = Matrix.det (fun i j => (ℓ j (v i)).re) := by
  let e : Fin (n + 1) ≃ Fin (N * 2) := finCongr hdim
  have h := AngularRadial.det_im_eq_det_re (fun j => ℓ (e.symm j)) (fun i => v (e.symm i))
  have hi := Matrix.det_submatrix_equiv_self e.symm (fun i j => (ℓ j (v i)).im)
  have hr := Matrix.det_submatrix_equiv_self e.symm (fun i j => (ℓ j (v i)).re)
  exact hi.symm.trans (h.trans hr)

/-- For complex-linear differentials in actual top degree, the primitive's
derivative is precisely the determinant of the angular pullbacks. -/
theorem extDeriv_primitive_angular_apply {N : ℕ} (hdim : n + 1 = N * 2)
    (f : Fin (n + 1) → AngularRadial.Coordinates N → ℂ)
    (D : Fin (n + 1) → AngularRadial.Coordinates N →ₗ[ℂ] ℂ)
    {x : AngularRadial.Coordinates N}
    (hf : ∀ j, ContDiffAt ℝ ⊤ (f j) x) (hne : ∀ j, f j x ≠ 0)
    (hD : ∀ j, HasFDerivAt (f j) ((D j).toContinuousLinearMap.restrictScalars ℝ) x)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) :
    extDeriv (primitive f) x v = Matrix.det (fun i j =>
      ((angularForm (f j x)).compContinuousLinearMap
        ((D j).toContinuousLinearMap.restrictScalars ℝ)) (fun _ : Fin 1 => v i)) := by
  rw [extDeriv_primitive f hf hne, radialForm_apply]
  have heval (j : Fin (n + 1)) (w : AngularRadial.Coordinates N) :
      fderiv ℝ (f j) x w = D j w := by
    rw [(hD j).fderiv]
    rfl
  simp only [heval, ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  change Matrix.det (fun i j => (D j (v i) / f j x).re) =
    Matrix.det (fun i j => (D j (v i) / f j x).im)
  have h := det_im_eq_det_re_of_dimension hdim (fun j => (f j x)⁻¹ • D j) v
  simpa only [LinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul] using h.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive
