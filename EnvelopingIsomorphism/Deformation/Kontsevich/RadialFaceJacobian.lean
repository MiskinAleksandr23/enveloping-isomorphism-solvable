import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceImmersion

/-! Exact cofactor relation between a full Jacobian and the native face
Jacobian, with both original coordinate-axis signs retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian
open BoxStokes ForestRadialFaceImmersion

variable {r : ℕ}

def faceDerivative (a b : Fin (r + 1)) (D : Coord (r + 1) →L[ℝ] Coord (r + 1)) :
    Coord r →L[ℝ] Coord r := (faceProjection b).comp (D.comp (faceTangent a))

/-- The scalar is the actual derivative of the target defining radius in the
source normal direction. No absolute Jacobian or orientation is substituted. -/
theorem det_eq_normal_mul_face (a b : Fin (r + 1))
    (D : Coord (r + 1) →L[ℝ] Coord (r + 1)) (c : ℝ)
    (hnormal : ∀ v, D v b = c * v a) :
    D.det = (-1 : ℝ) ^ (b.val + a.val) * c * (faceDerivative a b D).det := by
  let M := LinearMap.toMatrix (Pi.basisFun ℝ (Fin (r + 1))) (Pi.basisFun ℝ (Fin (r + 1))) D.toLinearMap
  have hM : M.det = D.det := LinearMap.det_toMatrix _ _
  have hrow (j : Fin (r + 1)) : M b j = c * (standardBasis (r + 1) j a) := by
    simpa only [M, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
      ContinuousLinearMap.coe_coe, standardBasis] using hnormal (standardBasis (r + 1) j)
  have hminor : M.submatrix b.succAbove a.succAbove =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin r)) (Pi.basisFun ℝ (Fin r)) (faceDerivative a b D).toLinearMap := by
    ext j k
    simp only [M, Matrix.submatrix_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      Pi.basisFun_apply, ContinuousLinearMap.coe_coe]
    change D (standardBasis (r + 1) (a.succAbove k)) (b.succAbove j) =
      faceDerivative a b D (standardBasis r k) j
    simp only [faceDerivative, ContinuousLinearMap.comp_apply, faceTangent_standardBasis]
    rfl
  rw [← hM, Matrix.det_succ_row M b, Finset.sum_eq_single a]
  · rw [hrow, hminor, LinearMap.det_toMatrix]
    simp [standardBasis]
  · intro j _ hja
    rw [hrow]
    simp [standardBasis, Pi.single_apply, Ne.symm hja]
  · intro h
    exact False.elim (h (Finset.mem_univ a))

/-- Positive normal rescaling transports the *native* outward face signs,
including their distinct deleted-coordinate positions. -/
theorem outward_sign_transport (a b : Fin (r + 1))
    (D : Coord (r + 1) →L[ℝ] Coord (r + 1)) (c : ℝ) (hc : 0 < c)
    (hnormal : ∀ v, D v b = c * v a) (ε δ : ℝ)
    (hfull : ε * D.det = δ * |D.det|) :
    ε * (-((-1 : ℝ) ^ a.val)) * (faceDerivative a b D).det =
      δ * (-((-1 : ℝ) ^ b.val)) * |(faceDerivative a b D).det| := by
  rw [det_eq_normal_mul_face a b D c hnormal] at hfull
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hc] at hfull
  have hb : (-1 : ℝ) ^ b.val * (-1 : ℝ) ^ b.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have h := congrArg (fun t : ℝ ↦ -((-1 : ℝ) ^ b.val) * t) hfull
  rw [pow_add] at h
  have he : -((-1 : ℝ) ^ b.val) * (ε * (((-1 : ℝ) ^ b.val * (-1 : ℝ) ^ a.val) * c * (faceDerivative a b D).det)) =
      c * (ε * (-((-1 : ℝ) ^ a.val)) * (faceDerivative a b D).det) := by
    calc
      _ = c * (ε * (-((-1 : ℝ) ^ a.val)) * (faceDerivative a b D).det) *
          ((-1 : ℝ) ^ b.val * (-1 : ℝ) ^ b.val) := by ring
      _ = _ := by rw [hb, mul_one]
  rw [he] at h
  apply mul_left_cancel₀ hc.ne'
  calc
    _ = -((-1 : ℝ) ^ b.val) * (δ * (c * |(faceDerivative a b D).det|)) := h
    _ = _ := by ring

end EnvelopingIsomorphism.Deformation.Kontsevich.RadialFaceJacobian
