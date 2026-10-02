import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorJacobian
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCoordinateSplit
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! The oriented determinant of the actual change of normalized anchor. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

namespace GraphForms

/-- A simultaneous linear coordinate change preserves the oriented derivative determinant. -/
theorem det_fderiv_linearConjugate
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (f : E → E) (x : E) (hf : DifferentiableAt ℝ f x) :
    LinearMap.det (fderiv ℝ (fun y => e (f (e.symm y))) (e x)).toLinearMap =
      LinearMap.det (fderiv ℝ f x).toLinearMap := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
    simpa using hf.hasFDerivAt
  have h := e.hasFDerivAt.comp (e x)
    (hf'.comp (e x) e.symm.hasFDerivAt)
  change LinearMap.det (fderiv ℝ (e ∘ f ∘ e.symm) (e x)).toLinearMap = _
  rw [h.fderiv]
  exact LinearMap.det_conj (fderiv ℝ f x).toLinearMap e.toLinearEquiv

/-- Transport the computed model Jacobian through an explicit linear conjugacy. -/
theorem det_fderiv_of_anchorModel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (e : E ≃L[ℝ] AnchorJacobian.Space d) (f : E → E) (c : Fin d → ℝ)
    (hmodel : ∀ y, e (f y) = AnchorJacobian.anchorSwap c (e y))
    (x : E) (hf : DifferentiableAt ℝ f x) (hy : (e x).1.2 ≠ 0) :
    LinearMap.det (fderiv ℝ f x).toLinearMap = 1 / (e x).1.2 ^ (d + 3) := by
  have hfun : (fun y => e (f (e.symm y))) = AnchorJacobian.anchorSwap c := by
    funext y
    simpa using hmodel (e.symm y)
  rw [← det_fderiv_linearConjugate e f x hf, hfun]
  exact AnchorJacobian.det_fderiv_anchorSwap c (e x) hy

variable {n m : ℕ}

/-- The standard real coordinates, bundled with their automatic finite-dimensional continuity. -/
def realCoordinatesContinuous (n m : ℕ) :
    Coordinates n m ≃L[ℝ] (Fin (dimension n m) → ℝ) := by
  letI := (realBasis n m).finiteDimensional_of_finite
  exact (realCoordinates n m).toContinuousLinearEquiv

/-- Actual anchor change written in the standard `1,I`/boundary real coordinates. -/
def anchorChangeReal (j : Fin (n + 1)) (x : Fin (dimension n m) → ℝ) :
    Fin (dimension n m) → ℝ :=
  realCoordinates n m (anchorChangeRaw j ((realCoordinates n m).symm x))

theorem det_fderiv_anchorChangeReal_eq (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    LinearMap.det (fderiv ℝ (anchorChangeReal j) (realCoordinates n m x)).toLinearMap =
      LinearMap.det (fderiv ℝ (anchorChangeRaw j) x).toLinearMap := by
  exact det_fderiv_linearConjugate (realCoordinatesContinuous n m) (anchorChangeRaw j) x
    ((contDiffAt_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))).differentiableAt
      (by simp))

theorem det_fderiv_anchorChangeRaw_zero (x : Coordinates n m) :
    LinearMap.det (fderiv ℝ (anchorChangeRaw (0 : Fin (n + 1))) x).toLinearMap = 1 := by
  have hzero : anchorChangeRaw (m := m) (0 : Fin (n + 1)) = id :=
    funext anchorChangeRaw_zero
  rw [hzero, fderiv_id]
  simp

/-- Exact determinant at a selected free interior point, in the native coordinate space. -/
theorem det_fderiv_anchorChangeRaw_succ (i : Fin (n + 1))
    (x : Coordinates (n + 1) m) (hy : (x.1 i).im ≠ 0) :
    LinearMap.det (fderiv ℝ (anchorChangeRaw i.succ) x).toLinearMap =
      1 / (x.1 i).im ^ (dimension (n + 1) m + 1) := by
  have h := det_fderiv_of_anchorModel (AnchorCoordinateSplit.split i)
    (anchorChangeRaw i.succ) (AnchorCoordinateSplit.shiftMask n m)
    (AnchorCoordinateSplit.split_anchorChangeRaw i) x
    ((contDiffAt_anchorChangeRaw i.succ x hy).differentiableAt (by simp)) hy
  have hdim : dimension n m + 3 = dimension (n + 1) m + 1 := by
    unfold dimension
    omega
  simpa only [AnchorCoordinateSplit.split_y, hdim] using h

/-- Exact Jacobian of changing any anchor. The zero-anchor case is the identity. -/
theorem det_fderiv_anchorChangeRaw (j : Fin (n + 1)) (x : Coordinates n m)
    (hy : (interiorPoint j x).im ≠ 0) :
    LinearMap.det (fderiv ℝ (anchorChangeRaw j) x).toLinearMap =
      1 / (interiorPoint j x).im ^ (dimension n m + 1) := by
  cases n with
  | zero =>
      have hj : j = 0 := by apply Fin.ext; omega
      subst j
      simpa using det_fderiv_anchorChangeRaw_zero x
  | succ n =>
      cases j using Fin.cases with
      | zero => simpa using det_fderiv_anchorChangeRaw_zero x
      | succ i => exact det_fderiv_anchorChangeRaw_succ i x hy

theorem det_fderiv_anchorChangeRaw_pos (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    0 < LinearMap.det (fderiv ℝ (anchorChangeRaw j) x).toLinearMap := by
  rw [det_fderiv_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))]
  exact one_div_pos.mpr (pow_pos (hx.interiorPoint_im_pos j) _)

/-- The determinant in the standard real-coordinate chart has the same exact positive formula. -/
theorem det_fderiv_anchorChangeReal (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    LinearMap.det (fderiv ℝ (anchorChangeReal j) (realCoordinates n m x)).toLinearMap =
      1 / (interiorPoint j x).im ^ (dimension n m + 1) := by
  rw [det_fderiv_anchorChangeReal_eq j hx]
  exact det_fderiv_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))

theorem det_fderiv_anchorChangeReal_pos (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    0 < LinearMap.det (fderiv ℝ (anchorChangeReal j) (realCoordinates n m x)).toLinearMap := by
  rw [det_fderiv_anchorChangeReal_eq j hx]
  exact det_fderiv_anchorChangeRaw_pos j hx

theorem abs_det_fderiv_anchorChangeRaw (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    |LinearMap.det (fderiv ℝ (anchorChangeRaw j) x).toLinearMap| =
      1 / (interiorPoint j x).im ^ (dimension n m + 1) := by
  rw [abs_of_pos (det_fderiv_anchorChangeRaw_pos j hx)]
  exact det_fderiv_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))

theorem abs_det_fderiv_anchorChangeReal (j : Fin (n + 1))
    {x : Coordinates n m} (hx : Admissible x) :
    |LinearMap.det (fderiv ℝ (anchorChangeReal j) (realCoordinates n m x)).toLinearMap| =
      1 / (interiorPoint j x).im ^ (dimension n m + 1) := by
  rw [abs_of_pos (det_fderiv_anchorChangeReal_pos j hx)]
  exact det_fderiv_anchorChangeReal j hx

/-- The form covariance holds for an arbitrary ordered edge list before taking its density. -/
theorem topForm_anchorChangeRaw {r : ℕ} (j : Fin (n + 1))
    (edges : Fin r → Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    (topForm edges (anchorChangeRaw j x)).compContinuousLinearMap
        (fderiv ℝ (anchorChangeRaw j) x) =
      topForm (fun a => anchorSwapEdge j (edges a)) x := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, topForm_apply]
  congr 1
  ext i a
  exact congrArg (fun ω : Coordinates n m [⋀^Fin 1]→L[ℝ] ℝ => ω (fun _ => v i))
    (edgeForm_anchorChangeRaw j (edges a) hx)

/-- The ordered top density transforms by the actual oriented derivative determinant. -/
theorem topDensity_anchorChangeRaw_det (j : Fin (n + 1))
    (edges : Fin (dimension n m) → Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    topDensity (fun a => anchorSwapEdge j (edges a)) x =
      LinearMap.det (fderiv ℝ (anchorChangeRaw j) x).toLinearMap *
        topDensity edges (anchorChangeRaw j x) := by
  have h := congrArg (fun ω : Coordinates n m [⋀^Fin (dimension n m)]→L[ℝ] ℝ =>
    ω (realBasis n m)) (topForm_anchorChangeRaw j edges hx)
  change (topForm (fun a => anchorSwapEdge j (edges a)) x) (realBasis n m) = _
  rw [← h]
  change (topForm edges (anchorChangeRaw j x)).toAlternatingMap
    (fun i => (fderiv ℝ (anchorChangeRaw j) x) (realBasis n m i)) = _
  rw [(topForm edges (anchorChangeRaw j x)).toAlternatingMap.eq_smul_basis_det (realBasis n m)]
  change topDensity edges (anchorChangeRaw j x) *
    (realBasis n m).det ((fderiv ℝ (anchorChangeRaw j) x).toLinearMap ∘ realBasis n m) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one, mul_comm]

theorem topDensity_anchorChangeRaw (j : Fin (n + 1))
    (edges : Fin (dimension n m) → Edge n m) {x : Coordinates n m} (hx : Admissible x) :
    topDensity (fun a => anchorSwapEdge j (edges a)) x =
      (1 / (interiorPoint j x).im ^ (dimension n m + 1)) *
        topDensity edges (anchorChangeRaw j x) := by
  rw [topDensity_anchorChangeRaw_det j edges hx,
    det_fderiv_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))]

end GraphForms

end EnvelopingIsomorphism.Deformation.Kontsevich
