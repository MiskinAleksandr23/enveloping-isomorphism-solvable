import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeJacobian
import Mathlib.GroupTheory.Perm.Fin

/-! Fixed-anchor internal permutations act by even permutations of real
coordinate blocks, since every complex coordinate contributes two real slots. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms

open scoped Matrix

variable {n m : ℕ}

def extendFixedAnchor (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

@[simp] theorem extendFixedAnchor_zero (σ : Equiv.Perm (Fin n)) : extendFixedAnchor σ 0 = 0 := by
  simp [extendFixedAnchor]

@[simp] theorem extendFixedAnchor_succ (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendFixedAnchor σ i.succ = (σ i).succ := by simp [extendFixedAnchor]

theorem exists_extendFixedAnchor (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
    ∃ τ : Equiv.Perm (Fin n), extendFixedAnchor τ = σ := by
  have hzero : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h := congrArg (fun π : Equiv.Perm (Fin (n + 1)) => π 0)
      (Equiv.Perm.decomposeFin.symm_apply_apply σ)
    exact (Equiv.Perm.decomposeFin_symm_apply_zero _ _).symm.trans (h.trans hσ)
  refine ⟨(Equiv.Perm.decomposeFin σ).2, ?_⟩
  rw [extendFixedAnchor, ← hzero]
  exact Equiv.Perm.decomposeFin.symm_apply_apply σ

def fixedAnchorCoordinates (σ : Equiv.Perm (Fin n)) : Coordinates n m ≃L[ℝ] Coordinates n m where
  toFun x := (fun i => x.1 (σ i), x.2)
  invFun x := (fun i => x.1 (σ.symm i), x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (continuous_pi fun i => (continuous_apply (σ i)).comp continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_pi fun i => (continuous_apply (σ.symm i)).comp continuous_fst).prodMk continuous_snd

def fixedAnchorCoordinatePerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (dimension n m)) :=
  (coordinateIndexEquiv n m).permCongr
    (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl (Fin 2))) (Equiv.refl (Fin m)))

/-- Swapping complex blocks has even real sign, including an arbitrary permutation. -/
theorem sign_fixedAnchorCoordinatePerm (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (fixedAnchorCoordinatePerm (m := m) σ) = 1 := by
  have hprod : Equiv.prodCongr σ (Equiv.refl (Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 => σ) := by ext x <;> rfl
  rw [fixedAnchorCoordinatePerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    hprod, Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]
  simp [Int.units_mul_self]

def fixedAnchorReal (σ : Equiv.Perm (Fin n)) :
    (Fin (dimension n m) → ℝ) ≃L[ℝ] (Fin (dimension n m) → ℝ) where
  toFun x := fun i => x (fixedAnchorCoordinatePerm σ i)
  invFun x := fun i => x ((fixedAnchorCoordinatePerm σ).symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

/-- These real-coordinate blocks describe the actual native complex-coordinate permutation. -/
theorem realCoordinates_fixedAnchor (σ : Equiv.Perm (Fin n)) (x : Coordinates n m) :
    realCoordinates n m (fixedAnchorCoordinates σ x) = fixedAnchorReal σ (realCoordinates n m x) := by
  funext j
  obtain ⟨j, rfl⟩ := (coordinateIndexEquiv n m).surjective j
  cases j with
  | inl p =>
      obtain ⟨i, a⟩ := p
      simp [realCoordinates_internal, fixedAnchorReal, fixedAnchorCoordinatePerm,
        Equiv.permCongr_def, fixedAnchorCoordinates]
  | inr j =>
      change realCoordinates n m (fixedAnchorCoordinates σ x) (externalBasisIndex n j) = _
      rw [realCoordinates_external]
      change x.2 j = realCoordinates n m x (fixedAnchorCoordinatePerm σ (externalBasisIndex n j))
      have hi : fixedAnchorCoordinatePerm (m := m) σ (externalBasisIndex n j) = externalBasisIndex n j := by
        simp [fixedAnchorCoordinatePerm, Equiv.permCongr_def, externalBasisIndex]
      rw [hi, realCoordinates_external]

theorem det_fixedAnchorReal (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (fixedAnchorReal (m := m) σ).toLinearEquiv.toLinearMap = 1 := by
  let b := Pi.basisFun ℝ (Fin (dimension n m))
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b (fixedAnchorReal σ).toLinearEquiv.toLinearMap =
      (1 : Matrix (Fin (dimension n m)) (Fin (dimension n m)) ℝ).submatrix
        (fixedAnchorCoordinatePerm σ) id := by
    ext i j
    simp [b, fixedAnchorReal, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_permute, sign_fixedAnchorCoordinatePerm]
  simp

theorem det_fderiv_fixedAnchorReal (σ : Equiv.Perm (Fin n)) (x : Fin (dimension n m) → ℝ) :
    LinearMap.det (fderiv ℝ (fixedAnchorReal σ) x).toLinearMap = 1 := by
  rw [(fixedAnchorReal σ).fderiv]
  exact det_fixedAnchorReal σ

theorem interiorPoint_fixedAnchor (σ : Equiv.Perm (Fin n)) (x : Coordinates n m) (i : Fin (n + 1)) :
    interiorPoint i (fixedAnchorCoordinates σ x) = interiorPoint (extendFixedAnchor σ i) x := by
  cases i using Fin.cases <;> simp [fixedAnchorCoordinates]

theorem fixedAnchorCoordinates_admissible (σ : Equiv.Perm (Fin n)) {x : Coordinates n m}
    (hx : Admissible x) : Admissible (fixedAnchorCoordinates σ x) := by
  refine ⟨fun i => hx.1 (σ i), ?_, hx.2.2⟩
  intro i j hij
  apply (extendFixedAnchor σ).injective
  apply hx.2.1
  simpa only [interiorPoint_fixedAnchor] using hij

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
