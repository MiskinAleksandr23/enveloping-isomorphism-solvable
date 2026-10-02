import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases

/-!
# Oriented Jacobian of an actual anchor normalization change

The ordered coordinates are `(x,y)` followed by the remaining real coordinates.
The map is an involution away from `y=0`, is smooth there, and has positive
Jacobian `1 / y^(d+3)` on the upper half-space.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.AnchorJacobian

open scoped Matrix ContDiff BigOperators

/-- The anchor's two real coordinates precede the remaining coordinate block. -/
abbrev Space (d : ℕ) := (ℝ × ℝ) × (Fin d → ℝ)

variable {d : ℕ} (c : Fin d → ℝ)

/-- The actual normalized-anchor swap. -/
def anchorSwap (p : Space d) : Space d :=
  ((-p.1.1 / p.1.2, 1 / p.1.2), fun j ↦ (p.2 j - c j * p.1.1) / p.1.2)

theorem anchorSwap_involutive_at (p : Space d) (hy : p.1.2 ≠ 0) :
    anchorSwap c (anchorSwap c p) = p := by
  apply Prod.ext
  · apply Prod.ext <;> simp [anchorSwap, hy]
  · funext j
    simp only [anchorSwap]
    field_simp
    ring

theorem anchorSwap_y_pos (p : Space d) (hy : 0 < p.1.2) :
    0 < (anchorSwap c p).1.2 := one_div_pos.mpr hy

theorem contDiffAt_anchorSwap (p : Space d) (hy : p.1.2 ≠ 0) :
    ContDiffAt ℝ ∞ (anchorSwap c) p := by
  unfold anchorSwap
  fun_prop (disch := assumption)

theorem contDiffOn_anchorSwap : ContDiffOn ℝ ∞ (anchorSwap c) {p | 0 < p.1.2} :=
  fun p hp ↦ (contDiffAt_anchorSwap c p (ne_of_gt hp)).contDiffWithinAt

def xProjection : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin d → ℝ))

def yProjection : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin d → ℝ))

def zProjection (j : Fin d) : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Fin d → ℝ))

@[simp] theorem xProjection_apply (p : Space d) : xProjection p = p.1.1 := rfl
@[simp] theorem yProjection_apply (p : Space d) : yProjection p = p.1.2 := rfl
@[simp] theorem zProjection_apply (j : Fin d) (p : Space d) : zProjection j p = p.2 j := rfl

def reciprocalDerivative (p : Space d) : Space d →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (-(p.1.2 ^ 2)⁻¹)).comp yProjection

theorem hasFDerivAt_reciprocal (p : Space d) (hy : p.1.2 ≠ 0) :
    HasFDerivAt (fun q : Space d ↦ q.1.2⁻¹) (reciprocalDerivative p) p := by
  exact (hasFDerivAt_inv hy).comp p (yProjection (d := d)).hasFDerivAt

/-- The genuine Fréchet derivative, expressed using continuous coordinate projections. -/
def derivative (p : Space d) : Space d →L[ℝ] Space d :=
  (((-p.1.1) • reciprocalDerivative p + p.1.2⁻¹ • (-xProjection)).prod
      (reciprocalDerivative p)).prod
    (ContinuousLinearMap.pi fun j ↦
      (p.2 j - c j * p.1.1) • reciprocalDerivative p +
        p.1.2⁻¹ • (zProjection j - c j • xProjection))

theorem hasFDerivAt_anchorSwap (p : Space d) (hy : p.1.2 ≠ 0) :
    HasFDerivAt (anchorSwap c) (derivative c p) p := by
  have hx := (xProjection (d := d)).hasFDerivAt (x := p)
  have hr := hasFDerivAt_reciprocal p hy
  have hz (j : Fin d) := (zProjection j).hasFDerivAt (x := p)
  have hn (j : Fin d) := (hz j).sub (hx.const_smul (c j))
  have h := ((hx.neg.mul hr).prodMk hr).prodMk (hasFDerivAt_pi.mpr fun j ↦ (hn j).mul hr)
  have hf : anchorSwap c = fun q : Space d ↦
      ((-q.1.1 * q.1.2⁻¹, q.1.2⁻¹), fun j ↦ (q.2 j - c j * q.1.1) * q.1.2⁻¹) := by
    funext q
    simp only [anchorSwap, div_eq_mul_inv, one_mul]
  rw [hf]
  simpa only [derivative,
    Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply,
    xProjection_apply, zProjection_apply, smul_eq_mul] using h

theorem fderiv_anchorSwap (p : Space d) (hy : p.1.2 ≠ 0) :
    fderiv ℝ (anchorSwap c) p = derivative c p := (hasFDerivAt_anchorSwap c p hy).fderiv

theorem derivative_apply (p v : Space d) :
    derivative c p v =
      ((-p.1.2⁻¹ * v.1.1 + p.1.1 * (p.1.2⁻¹)^2 * v.1.2,
        -(p.1.2⁻¹)^2 * v.1.2),
       fun j ↦ -c j * p.1.2⁻¹ * v.1.1 -
         (p.2 j - c j * p.1.1) * (p.1.2⁻¹)^2 * v.1.2 + p.1.2⁻¹ * v.2 j) := by
  apply Prod.ext
  · apply Prod.ext <;>
      simp [derivative, reciprocalDerivative, smul_eq_mul, inv_pow] <;> ring
  · funext j
    simp [derivative, reciprocalDerivative, smul_eq_mul, inv_pow]
    ring

/-- Explicit ordered real basis: `x,y`, followed by the `d` remaining coordinates. -/
def coordinateBasis (d : ℕ) : Module.Basis (Fin 2 ⊕ Fin d) ℝ (Space d) :=
  (Module.Basis.finTwoProd ℝ).prod (Pi.basisFun ℝ (Fin d))

@[simp] theorem coordinateBasis_repr_inl (p : Space d) (i : Fin 2) :
    (coordinateBasis d).repr p (.inl i) = ![p.1.1, p.1.2] i := by
  rw [coordinateBasis, Module.Basis.prod_repr_inl]
  exact congrFun (Module.Basis.coe_finTwoProd_repr p.1) i

@[simp] theorem coordinateBasis_repr_inr (p : Space d) (j : Fin d) :
    (coordinateBasis d).repr p (.inr j) = p.2 j := by
  rw [coordinateBasis, Module.Basis.prod_repr_inr, ← Module.Basis.equivFun_apply,
    Pi.basisFun_equivFun]
  rfl

@[simp] theorem coordinateBasis_inl_zero : coordinateBasis d (.inl 0) = ((1, 0), 0) := by
  simp [coordinateBasis]

@[simp] theorem coordinateBasis_inl_one : coordinateBasis d (.inl 1) = ((0, 1), 0) := by
  simp [coordinateBasis]

@[simp] theorem coordinateBasis_inr (j : Fin d) :
    coordinateBasis d (.inr j) = ((0, 0), Pi.single j 1) := by
  simp [coordinateBasis, Pi.basisFun_apply]
  rfl

/-- The actual derivative matrix, in lower block-triangular form. -/
def jacobianMatrix (p : Space d) : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℝ :=
  Matrix.fromBlocks
    !![-p.1.2⁻¹, p.1.1 * (p.1.2⁻¹)^2; 0, -(p.1.2⁻¹)^2]
    0
    (fun j i ↦ if i = 0 then -c j * p.1.2⁻¹ else -(p.2 j - c j * p.1.1) * (p.1.2⁻¹)^2)
    (Matrix.diagonal (fun _ : Fin d ↦ p.1.2⁻¹))

theorem toMatrix_derivative (p : Space d) :
    LinearMap.toMatrix (coordinateBasis d) (coordinateBasis d) (derivative c p).toLinearMap =
      jacobianMatrix c p := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;>
          simp [LinearMap.toMatrix_apply, derivative_apply, jacobianMatrix]
      | inr j => fin_cases i <;>
          simp [LinearMap.toMatrix_apply, derivative_apply, jacobianMatrix]
  | inr i =>
      cases j with
      | inl j =>
          fin_cases j <;> simp [LinearMap.toMatrix_apply, derivative_apply, jacobianMatrix]
          ring
      | inr j =>
          simp [LinearMap.toMatrix_apply, derivative_apply, jacobianMatrix,
            Matrix.diagonal_apply, Pi.single_apply, eq_comm]

theorem det_jacobianMatrix (p : Space d) :
    (jacobianMatrix c p).det = 1 / p.1.2 ^ (d + 3) := by
  calc
    (jacobianMatrix c p).det = (p.1.2⁻¹)^3 * (p.1.2⁻¹)^d := by
      rw [jacobianMatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fin_two, Matrix.det_diagonal]
      change ((-p.1.2⁻¹) * (-(p.1.2⁻¹)^2) - (p.1.1 * (p.1.2⁻¹)^2) * 0) *
        (∏ _ : Fin d, p.1.2⁻¹) = _
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ = (p.1.2⁻¹)^(d + 3) := by rw [pow_add]; ring
    _ = 1 / p.1.2 ^ (d + 3) := by rw [inv_pow, one_div]

/-- The oriented real Jacobian of the actual Fréchet derivative. -/
theorem det_fderiv_anchorSwap (p : Space d) (hy : p.1.2 ≠ 0) :
    LinearMap.det (fderiv ℝ (anchorSwap c) p).toLinearMap = 1 / p.1.2 ^ (d + 3) := by
  rw [fderiv_anchorSwap c p hy, ← LinearMap.det_toMatrix (coordinateBasis d),
    toMatrix_derivative, det_jacobianMatrix]

theorem det_fderiv_anchorSwap_pos (p : Space d) (hy : 0 < p.1.2) :
    0 < LinearMap.det (fderiv ℝ (anchorSwap c) p).toLinearMap := by
  rw [det_fderiv_anchorSwap c p (ne_of_gt hy)]
  exact one_div_pos.mpr (pow_pos hy _)

theorem abs_det_fderiv_anchorSwap (p : Space d) (hy : 0 < p.1.2) :
    |LinearMap.det (fderiv ℝ (anchorSwap c) p).toLinearMap| = 1 / p.1.2 ^ (d + 3) := by
  rw [abs_of_pos (det_fderiv_anchorSwap_pos c p hy)]
  exact det_fderiv_anchorSwap c p (ne_of_gt hy)

end EnvelopingIsomorphism.Deformation.Kontsevich.AnchorJacobian
