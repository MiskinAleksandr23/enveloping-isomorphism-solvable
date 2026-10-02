import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorJacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Actual angular/radial insertion Jacobians

The native convention is angle before radius. Its polar determinant is `-r`;
swapping to radius before angle gives `+r`. Additional real shape coordinates
contribute one factor of `r` each. These signs are computed from actual Fréchet
derivatives, not supplied as orientation hypotheses.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian

open scoped Matrix ContDiff BigOperators

def polarInsertion (center : ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (center.1 + p.2 * Real.cos p.1, center.2 + p.2 * Real.sin p.1)

theorem contDiff_polarInsertion (center : ℝ × ℝ) : ContDiff ℝ ∞ (polarInsertion center) := by
  unfold polarInsertion
  fun_prop

def polarDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (p.2 • ((-Real.sin p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      Real.cos p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (p.2 • (Real.cos p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      Real.sin p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_polarInsertion (center p : ℝ × ℝ) :
    HasFDerivAt (polarInsertion center) (polarDerivative p) p := by
  have ht := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hr := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hc := (Real.hasDerivAt_cos p.1).comp_hasFDerivAt p ht
  have hs := (Real.hasDerivAt_sin p.1).comp_hasFDerivAt p ht
  have h := ((hr.mul hc).const_add center.1).prodMk ((hr.mul hs).const_add center.2)
  change HasFDerivAt (fun q : ℝ × ℝ ↦
    (center.1 + q.2 * Real.cos q.1, center.2 + q.2 * Real.sin q.1)) (polarDerivative p) p
  simpa only [polarDerivative, Function.comp_def, Pi.mul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h

theorem polarDerivative_apply (p v : ℝ × ℝ) :
    polarDerivative p v =
      (-p.2 * Real.sin p.1 * v.1 + Real.cos p.1 * v.2,
        p.2 * Real.cos p.1 * v.1 + Real.sin p.1 * v.2) := by
  apply Prod.ext <;> simp [polarDerivative, smul_eq_mul] <;> ring

def polarMatrix (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-p.2 * Real.sin p.1, Real.cos p.1; p.2 * Real.cos p.1, Real.sin p.1]

theorem toMatrix_polarDerivative (p : ℝ × ℝ) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (polarDerivative p).toLinearMap = polarMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, polarDerivative_apply, polarMatrix,
      Module.Basis.coe_finTwoProd_repr]

theorem det_polarMatrix (p : ℝ × ℝ) : (polarMatrix p).det = -p.2 := by
  rw [Matrix.det_fin_two]
  change (-p.2 * Real.sin p.1) * Real.sin p.1 - Real.cos p.1 * (p.2 * Real.cos p.1) = -p.2
  calc
    _ = -p.2 * (Real.sin p.1 ^ 2 + Real.cos p.1 ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Oriented Jacobian in the actual angle-then-radius convention. -/
theorem det_fderiv_polarInsertion (center p : ℝ × ℝ) :
    LinearMap.det (fderiv ℝ (polarInsertion center) p).toLinearMap = -p.2 := by
  rw [(hasFDerivAt_polarInsertion center p).fderiv,
    ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), toMatrix_polarDerivative, det_polarMatrix]

/-- Remaining real shape coordinates followed by `(angle,radius)`. -/
abbrev Space (d : ℕ) := (Fin d → ℝ) × (ℝ × ℝ)

variable {d : ℕ}

def radialInsertion (offset : Fin d → ℝ) (center : ℝ × ℝ) (p : Space d) : Space d :=
  (fun j ↦ offset j + p.2.2 * p.1 j, polarInsertion center p.2)

theorem contDiff_radialInsertion (offset : Fin d → ℝ) (center : ℝ × ℝ) :
    ContDiff ℝ ∞ (radialInsertion offset center) := by
  unfold radialInsertion polarInsertion
  fun_prop

def shapeProjection (j : Fin d) : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (ℝ × ℝ))

def radiusProjection : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (ℝ × ℝ))

@[simp] theorem shapeProjection_apply (j : Fin d) (p : Space d) : shapeProjection j p = p.1 j := rfl
@[simp] theorem radiusProjection_apply (p : Space d) : radiusProjection p = p.2.2 := rfl

def radialDerivative (p : Space d) : Space d →L[ℝ] Space d :=
  (ContinuousLinearMap.pi fun j ↦ p.2.2 • shapeProjection j + p.1 j • radiusProjection).prod
    ((polarDerivative p.2).comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (ℝ × ℝ)))

theorem hasFDerivAt_radialInsertion (offset : Fin d → ℝ) (center : ℝ × ℝ) (p : Space d) :
    HasFDerivAt (radialInsertion offset center) (radialDerivative p) p := by
  have hr := (radiusProjection (d := d)).hasFDerivAt (x := p)
  have hz (j : Fin d) := (shapeProjection j).hasFDerivAt (x := p)
  have hp := (hasFDerivAt_polarInsertion center p.2).comp p
    (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (ℝ × ℝ)).hasFDerivAt
  have h := (hasFDerivAt_pi.mpr fun j ↦ (hr.mul (hz j)).const_add (offset j)).prodMk hp
  change HasFDerivAt (fun q : Space d ↦
    (fun j ↦ offset j + q.2.2 * q.1 j, polarInsertion center q.2)) (radialDerivative p) p
  simpa only [radialDerivative, Function.comp_def, Pi.mul_apply,
    radiusProjection_apply, shapeProjection_apply, ContinuousLinearMap.coe_snd'] using h

theorem radialDerivative_apply (p v : Space d) :
    radialDerivative p v =
      (fun j ↦ p.2.2 * v.1 j + p.1 j * v.2.2, polarDerivative p.2 v.2) := by
  apply Prod.ext
  · funext j
    simp [radialDerivative, smul_eq_mul]
  · rfl

def coordinateBasis (d : ℕ) : Module.Basis (Fin d ⊕ Fin 2) ℝ (Space d) :=
  (Pi.basisFun ℝ (Fin d)).prod (Module.Basis.finTwoProd ℝ)

@[simp] theorem coordinateBasis_repr_inl (p : Space d) (i : Fin d) :
    (coordinateBasis d).repr p (.inl i) = p.1 i := by
  rw [coordinateBasis, Module.Basis.prod_repr_inl, ← Module.Basis.equivFun_apply,
    Pi.basisFun_equivFun]
  rfl

@[simp] theorem coordinateBasis_repr_inr (p : Space d) (i : Fin 2) :
    (coordinateBasis d).repr p (.inr i) = ![p.2.1, p.2.2] i := by
  rw [coordinateBasis, Module.Basis.prod_repr_inr]
  exact congrFun (Module.Basis.coe_finTwoProd_repr p.2) i

@[simp] theorem coordinateBasis_inl (i : Fin d) :
    coordinateBasis d (.inl i) = (Pi.single i 1, (0, 0)) := by
  simp [coordinateBasis, Pi.basisFun_apply]
  rfl

@[simp] theorem coordinateBasis_inr_zero : coordinateBasis d (.inr 0) = (0, (1, 0)) := by
  simp [coordinateBasis]

@[simp] theorem coordinateBasis_inr_one : coordinateBasis d (.inr 1) = (0, (0, 1)) := by
  simp [coordinateBasis]

def radialMatrix (p : Space d) : Matrix (Fin d ⊕ Fin 2) (Fin d ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin d ↦ p.2.2))
    (fun j i ↦ if i = 0 then 0 else p.1 j) 0 (polarMatrix p.2)

theorem toMatrix_radialDerivative (p : Space d) :
    LinearMap.toMatrix (coordinateBasis d) (coordinateBasis d) (radialDerivative p).toLinearMap =
      radialMatrix p := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [LinearMap.toMatrix_apply, radialDerivative_apply, radialMatrix,
          Matrix.diagonal_apply, Pi.single_apply, eq_comm]
      | inr j => fin_cases j <;> simp [LinearMap.toMatrix_apply, radialDerivative_apply, radialMatrix]
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> simp [LinearMap.toMatrix_apply, radialDerivative_apply,
          polarDerivative_apply, radialMatrix]
      | inr j => fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply,
          radialDerivative_apply, polarDerivative_apply, radialMatrix, polarMatrix]

theorem det_radialMatrix (p : Space d) : (radialMatrix p).det = -p.2.2 ^ (d + 1) := by
  rw [radialMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, det_polarMatrix]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_succ]
  ring

theorem det_radialDerivative (p : Space d) :
    LinearMap.det (radialDerivative p).toLinearMap = -p.2.2 ^ (d + 1) := by
  rw [← LinearMap.det_toMatrix (coordinateBasis d), toMatrix_radialDerivative, det_radialMatrix]

/-- `d` real shape coordinates contribute `r^d`, and the polar block contributes `-r`. -/
theorem det_fderiv_radialInsertion (offset : Fin d → ℝ) (center : ℝ × ℝ) (p : Space d) :
    LinearMap.det (fderiv ℝ (radialInsertion offset center) p).toLinearMap = -p.2.2 ^ (d + 1) := by
  rw [(hasFDerivAt_radialInsertion offset center p).fderiv,
    ← LinearMap.det_toMatrix (coordinateBasis d), toMatrix_radialDerivative, det_radialMatrix]

theorem abs_det_fderiv_radialInsertion (offset : Fin d → ℝ) (center : ℝ × ℝ)
    (p : Space d) (hr : 0 < p.2.2) :
    |LinearMap.det (fderiv ℝ (radialInsertion offset center) p).toLinearMap| = p.2.2 ^ (d + 1) := by
  rw [det_fderiv_radialInsertion, abs_neg, abs_of_pos (pow_pos hr _)]

/-- The explicit coordinate permutation changing `(angle,radius)` to `(radius,angle)`. -/
def exchangeAngleRadius (d : ℕ) : Space d ≃L[ℝ] Space d :=
  (ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)).prodCongr (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

@[simp] theorem exchangeAngleRadius_apply (p : Space d) :
    exchangeAngleRadius d p = (p.1, (p.2.2, p.2.1)) := rfl

theorem toMatrix_exchangeAngleRadius :
    LinearMap.toMatrix (coordinateBasis d) (coordinateBasis d)
      (exchangeAngleRadius d).toLinearMap =
      Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℝ) 0 0 !![0, 1; 1, 0] := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [LinearMap.toMatrix_apply, Matrix.one_apply, Pi.single_apply]
      | inr j => fin_cases j <;> simp [LinearMap.toMatrix_apply]
  | inr i =>
      cases j with
      | inl j => fin_cases i <;> simp [LinearMap.toMatrix_apply]
      | inr j => fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

theorem det_exchangeAngleRadius : LinearMap.det (exchangeAngleRadius d).toLinearMap = -1 := by
  rw [← LinearMap.det_toMatrix (coordinateBasis d), toMatrix_exchangeAngleRadius,
    Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_fin_two]

def radialInsertionRadiusFirst (offset : Fin d → ℝ) (center : ℝ × ℝ) : Space d → Space d :=
  radialInsertion offset center ∘ exchangeAngleRadius d

/-- In the explicit radius-before-angle order the Jacobian is positive. -/
theorem det_fderiv_radialInsertionRadiusFirst (offset : Fin d → ℝ) (center : ℝ × ℝ)
    (p : Space d) :
    LinearMap.det (fderiv ℝ (radialInsertionRadiusFirst offset center) p).toLinearMap =
      p.2.1 ^ (d + 1) := by
  have h := (hasFDerivAt_radialInsertion offset center (exchangeAngleRadius d p)).comp p
    (exchangeAngleRadius d).toContinuousLinearMap.hasFDerivAt
  change LinearMap.det (fderiv ℝ (radialInsertion offset center ∘ exchangeAngleRadius d) p).toLinearMap = _
  rw [h.fderiv]
  change LinearMap.det ((radialDerivative (exchangeAngleRadius d p)).toLinearMap.comp
    (exchangeAngleRadius d).toLinearMap) = _
  rw [LinearMap.det_comp, det_radialDerivative, det_exchangeAngleRadius]
  simp

theorem det_fderiv_radialInsertionRadiusFirst_pos (offset : Fin d → ℝ) (center : ℝ × ℝ)
    (p : Space d) (hr : 0 < p.2.1) :
    0 < LinearMap.det (fderiv ℝ (radialInsertionRadiusFirst offset center) p).toLinearMap := by
  rw [det_fderiv_radialInsertionRadiusFirst]
  exact pow_pos hr _

/-- For `s` cluster points the free complex shapes contribute `2(s-2)` real
coordinates, so the magnitude is precisely `r^(2s-3)`. -/
theorem det_fderiv_complexCluster (s : ℕ) (hs : 2 ≤ s)
    (offset : Fin (2 * (s - 2)) → ℝ) (center : ℝ × ℝ) (p : Space (2 * (s - 2))) :
    LinearMap.det (fderiv ℝ (radialInsertion offset center) p).toLinearMap = -p.2.2 ^ (2 * s - 3) := by
  rw [det_fderiv_radialInsertion]
  have he : 2 * (s - 2) + 1 = 2 * s - 3 := by omega
  rw [he]

/-- Actual outward radial normal on the half-plane `r≥0`. -/
def outwardNormal : ℝ × ℝ := (0, -1)

def positiveAngleTangent : ℝ × ℝ := (1, 0)

theorem radius_outwardNormal : (ContinuousLinearMap.snd ℝ ℝ ℝ) outwardNormal = -1 := rfl
theorem radius_positiveAngleTangent :
    (ContinuousLinearMap.snd ℝ ℝ ℝ) positiveAngleTangent = 0 := rfl

/-- In the angle-then-radius parameter orientation, the outward-normal-first
frame `(-∂r,+∂θ)` is positive. The insertion's negative Jacobian is a separate factor. -/
theorem outward_angle_frame_det :
    (Module.Basis.finTwoProd ℝ).det ![outwardNormal, positiveAngleTangent] = 1 := by
  simp [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Matrix.det_fin_two,
    Module.Basis.coe_finTwoProd_repr, outwardNormal, positiveAngleTangent]

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian
