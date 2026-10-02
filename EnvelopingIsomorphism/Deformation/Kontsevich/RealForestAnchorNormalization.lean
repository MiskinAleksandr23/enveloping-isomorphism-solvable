import EnvelopingIsomorphism.Deformation.Kontsevich.FixedAnchorPermutation
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster

/-! Positive determinant of outside-anchor normalization with the actual
Fin.succAbove label order. All extra complex-pair permutations have sign +1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestAnchorNormalization
open GraphForms
open scoped Classical
variable {n m : ℕ}

def outsidePermutation (b : Fin (n+1)) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv b).trans
    (((Equiv.swap 0 b).subtypeEquiv (fun j => by
      have h : Equiv.swap 0 b j = 0 ↔ j = b := by
        rw [Equiv.apply_eq_iff_eq_symm_apply]
        simp
      exact (not_congr h).symm)).trans (finSuccAboveEquiv 0).symm)

theorem outsidePermutation_label (b : Fin (n+1)) (j : Fin n) :
    Equiv.swap 0 b (outsidePermutation b j).succ = b.succAbove j := by
  have h : (outsidePermutation b j).succ = Equiv.swap 0 b (b.succAbove j) := by
    change ((finSuccAboveEquiv 0) (outsidePermutation b j)).val = _
    simp only [outsidePermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [h, Equiv.swap_apply_self]

def outsideAnchorRaw (b : Fin (n+1)) (p : Coordinates n m) : Coordinates n m :=
  (fun j => RealForestSimpleCluster.normalize (interiorPoint b p) (interiorPoint (b.succAbove j) p),
    fun j => RealForestSimpleCluster.normalizeReal (interiorPoint b p) (p.2 j))

theorem outsideAnchorRaw_eq (b : Fin (n+1)) :
    outsideAnchorRaw (m := m) b = fixedAnchorCoordinates (outsidePermutation b) ∘ anchorChangeRaw b := by
  funext p
  apply Prod.ext
  · funext j
    change RealForestSimpleCluster.normalize _ _ =
      (interiorPoint (Equiv.swap 0 b (outsidePermutation b j).succ) p - ((interiorPoint b p).re : ℂ)) /
        ((interiorPoint b p).im : ℂ)
    rw [outsidePermutation_label]
    rfl
  · rfl

theorem det_fixedAnchorCoordinates (σ : Equiv.Perm (Fin n)) :
    (fixedAnchorCoordinates (m := m) σ).toLinearMap.det = 1 := by
  have h := det_fderiv_linearConjugate (realCoordinatesContinuous n m)
    (fixedAnchorCoordinates (m := m) σ) (0 : Coordinates n m) (fixedAnchorCoordinates σ).differentiableAt
  have he : (fun y => realCoordinatesContinuous n m
      (fixedAnchorCoordinates σ ((realCoordinatesContinuous n m).symm y))) = fixedAnchorReal σ := by
    funext y
    change realCoordinates n m (fixedAnchorCoordinates σ ((realCoordinates n m).symm y)) = _
    simpa only [LinearEquiv.apply_symm_apply] using realCoordinates_fixedAnchor σ ((realCoordinates n m).symm y)
  rw [he, det_fderiv_fixedAnchorReal, ContinuousLinearEquiv.fderiv] at h
  exact h.symm

theorem differentiableAt_outsideAnchorRaw (b : Fin (n+1)) (p : Coordinates n m)
    (hp : (interiorPoint b p).im ≠ 0) : DifferentiableAt ℝ (outsideAnchorRaw b) p := by
  rw [outsideAnchorRaw_eq]
  exact (fixedAnchorCoordinates (outsidePermutation b)).differentiableAt.comp p
    ((contDiffAt_anchorChangeRaw b p hp).differentiableAt (by simp))

/-- Literal rational normalization determinant; no admissibility or sign
contract is required beyond nonvanishing of the actual chosen height. -/
theorem det_outsideAnchorRaw (b : Fin (n+1)) (p : Coordinates n m)
    (hp : (interiorPoint b p).im ≠ 0) :
    (fderiv ℝ (outsideAnchorRaw b) p).det = 1 / (interiorPoint b p).im ^ (dimension n m + 1) := by
  rw [outsideAnchorRaw_eq,
    fderiv_comp p (fixedAnchorCoordinates (outsidePermutation b)).differentiableAt
      ((contDiffAt_anchorChangeRaw b p hp).differentiableAt (by simp)), ContinuousLinearEquiv.fderiv]
  change LinearMap.det ((fixedAnchorCoordinates (outsidePermutation b)).toLinearMap.comp
    (fderiv ℝ (anchorChangeRaw b) p).toLinearMap) = _
  rw [LinearMap.det_comp, det_fixedAnchorCoordinates, one_mul]
  exact det_fderiv_anchorChangeRaw b p hp

theorem det_outsideAnchorRaw_pos (b : Fin (n+1)) (p : Coordinates n m)
    (hp : 0 < (interiorPoint b p).im) : 0 < (fderiv ℝ (outsideAnchorRaw b) p).det := by
  rw [det_outsideAnchorRaw b p hp.ne']
  positivity

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestAnchorNormalization
