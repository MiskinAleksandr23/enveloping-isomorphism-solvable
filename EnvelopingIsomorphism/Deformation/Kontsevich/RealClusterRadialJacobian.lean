import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian

/-! The actual diagonal radial model for a real cluster. Unselected coordinates
are passive. The final two coordinates are the center and radius themselves. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterRadialJacobian

open scoped ContDiff

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

abbrev Space (Q : Type*) := (Q → ℝ) × (ℝ × ℝ)

def insertion (A : Finset Q) (c : Q → ℝ) (x : Space Q) : Space Q :=
  (fun j => c j * x.2.1 + (if j ∈ A then x.2.2 else 1) * x.1 j, x.2)

@[fun_prop] theorem contDiff_insertion (A : Finset Q) (c : Q → ℝ) :
    ContDiff ℝ ∞ (insertion A c) := by
  unfold insertion
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    split_ifs <;> fun_prop
  · fun_prop

def coordinateProjection (j : Q) : Space Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Q → ℝ) (ℝ × ℝ))

def centerProjection : Space Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (Q → ℝ) (ℝ × ℝ))

def radiusProjection : Space Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (Q → ℝ) (ℝ × ℝ))

def derivative (A : Finset Q) (c : Q → ℝ) (x : Space Q) : Space Q →L[ℝ] Space Q :=
  (ContinuousLinearMap.pi fun j => c j • centerProjection +
    (if j ∈ A then x.2.2 • coordinateProjection j + x.1 j • radiusProjection
      else coordinateProjection j)).prod
    (ContinuousLinearMap.snd ℝ (Q → ℝ) (ℝ × ℝ))

theorem hasFDerivAt_insertion (A : Finset Q) (c : Q → ℝ) (x : Space Q) :
    HasFDerivAt (insertion A c) (derivative A c x) x := by
  apply HasFDerivAt.prodMk
  · apply hasFDerivAt_pi.mpr
    intro j
    have hc := (centerProjection (Q := Q)).hasFDerivAt (x := x)
    have hr := (radiusProjection (Q := Q)).hasFDerivAt (x := x)
    have hq := (coordinateProjection j).hasFDerivAt (x := x)
    by_cases hj : j ∈ A
    · have h := (hc.const_mul (c j)).add (hr.mul hq)
      change HasFDerivAt (fun y : Space Q => c j * y.2.1 + y.2.2 * y.1 j) _ x at h
      simpa only [if_pos hj, derivative, radiusProjection, coordinateProjection,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply] using h
    · have h := (hc.const_mul (c j)).add hq
      change HasFDerivAt (fun y : Space Q => c j * y.2.1 + y.1 j) _ x at h
      simpa only [if_neg hj, derivative, one_mul] using h
  · exact (ContinuousLinearMap.snd ℝ (Q → ℝ) (ℝ × ℝ)).hasFDerivAt

omit [Fintype Q] in
theorem derivative_apply (A : Finset Q) (c : Q → ℝ) (x v : Space Q) :
    derivative A c x v =
      (fun j => c j * v.2.1 + (if j ∈ A then x.2.2 * v.1 j + x.1 j * v.2.2
        else v.1 j), v.2) := by
  apply Prod.ext
  · ext j
    by_cases hj : j ∈ A <;>
      simp [derivative, centerProjection, radiusProjection, coordinateProjection, hj, smul_eq_mul]
  · rfl

def coordinateBasis : Module.Basis (Q ⊕ Fin 2) ℝ (Space Q) :=
  (Pi.basisFun ℝ Q).prod (Module.Basis.finTwoProd ℝ)

theorem toMatrix_derivative (A : Finset Q) (c : Q → ℝ) (x : Space Q) :
    LinearMap.toMatrix coordinateBasis coordinateBasis (derivative A c x).toLinearMap =
      Matrix.fromBlocks (Matrix.diagonal (fun j => if j ∈ A then x.2.2 else 1))
        (fun j k => if k = 0 then c j else if j ∈ A then x.1 j else 0) 0 1 := by
  ext j k
  cases j with
  | inl j =>
    cases k with
    | inl k =>
      by_cases hj : j ∈ A <;>
        simp [LinearMap.toMatrix_apply, coordinateBasis, derivative_apply, hj,
          Pi.basisFun_apply, Pi.single_apply, Matrix.diagonal_apply, eq_comm]
    | inr k =>
      fin_cases k <;> by_cases hj : j ∈ A <;>
        simp [LinearMap.toMatrix_apply, coordinateBasis, derivative_apply, hj]
  | inr j =>
    cases k with
    | inl k => fin_cases j <;> simp [LinearMap.toMatrix_apply, coordinateBasis, derivative_apply]
    | inr k => fin_cases j <;> fin_cases k <;>
        simp [LinearMap.toMatrix_apply, coordinateBasis, derivative_apply]

/-- The true Fréchet determinant counts precisely the scaled coordinates. -/
theorem det_fderiv_insertion (A : Finset Q) (c : Q → ℝ) (x : Space Q) :
    LinearMap.det (fderiv ℝ (insertion A c) x).toLinearMap = x.2.2 ^ A.card := by
  rw [(hasFDerivAt_insertion A c x).fderiv, ← LinearMap.det_toMatrix coordinateBasis,
    toMatrix_derivative, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    Matrix.det_diagonal]
  simp

end EnvelopingIsomorphism.Deformation.Kontsevich.RealClusterRadialJacobian
