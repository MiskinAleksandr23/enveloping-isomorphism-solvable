import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorChangeSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorJacobian
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual coordinate splitting for a selected interior anchor

The selected complex coordinate contributes the first pair `(Re,Im)`.
The remaining complex and boundary coordinates use the existing native real
coordinate chart. In these exact coordinates the native anchor change is
the rational model whose oriented Jacobian was computed in `AnchorJacobian`.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCoordinateSplit

open GraphForms

variable {n m : ℕ}

/-- Select one complex coordinate and retain all others in `succAbove` order. -/
def selectComplex (i : Fin (n + 1)) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℝ] ℂ × (Fin n → ℂ) :=
  { (Fin.insertNthEquiv (fun _ : Fin (n + 1) ↦ ℂ) i).symm with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp] theorem selectComplex_apply (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) :
    selectComplex i z = (z i, fun j ↦ z (i.succAbove j)) := rfl

@[simp] theorem selectComplex_symm_apply (i : Fin (n + 1)) (z : ℂ × (Fin n → ℂ)) :
    (selectComplex i).symm z = Fin.insertNth i z.1 z.2 := rfl

/-- The explicit real linear coordinate split before invoking finite-dimensional continuity. -/
def splitLinear (i : Fin (n + 1)) :
    Coordinates (n + 1) m ≃ₗ[ℝ] AnchorJacobian.Space (dimension n m) :=
  ((selectComplex i).prodCongr (LinearEquiv.refl ℝ (Fin m → ℝ))).trans
    ((LinearEquiv.prodAssoc ℝ ℂ (Fin n → ℂ) (Fin m → ℝ)).trans
      (Complex.equivRealProdLm.prodCongr (realCoordinates n m)))

/-- A genuine continuous real linear equivalence of the actual coordinate spaces. -/
def split (i : Fin (n + 1)) :
    Coordinates (n + 1) m ≃L[ℝ] AnchorJacobian.Space (dimension n m) := by
  letI : FiniteDimensional ℝ (Coordinates (n + 1) m) := Module.Finite.of_basis (realBasis (n + 1) m)
  exact (splitLinear i).toContinuousLinearEquiv

theorem split_apply (i : Fin (n + 1)) (x : Coordinates (n + 1) m) :
    split i x = (((x.1 i).re, (x.1 i).im),
      realCoordinates n m (fun j ↦ x.1 (i.succAbove j), x.2)) := rfl

@[simp] theorem split_x (i : Fin (n + 1)) (x : Coordinates (n + 1) m) :
    (split i x).1.1 = (x.1 i).re := rfl

@[simp] theorem split_y (i : Fin (n + 1)) (x : Coordinates (n + 1) m) :
    (split i x).1.2 = (x.1 i).im := rfl

theorem split_internal (i : Fin (n + 1)) (x : Coordinates (n + 1) m)
    (j : Fin n) (a : Fin 2) :
    (split i x).2 (coordinateIndexEquiv n m (.inl (j, a))) =
      ![(x.1 (i.succAbove j)).re, (x.1 (i.succAbove j)).im] a :=
  realCoordinates_internal _ j a

theorem split_external (i : Fin (n + 1)) (x : Coordinates (n + 1) m) (j : Fin m) :
    (split i x).2 (externalBasisIndex n j) = x.2 j := realCoordinates_external _ j

/-- The inverse reinserts the selected complex number and reverses the existing real chart. -/
theorem split_symm_apply (i : Fin (n + 1)) (p : AnchorJacobian.Space (dimension n m)) :
    (split i).symm p =
      (Fin.insertNth i (Complex.equivRealProdLm.symm p.1) ((realCoordinates n m).symm p.2).1,
        ((realCoordinates n m).symm p.2).2) := rfl

@[simp] theorem split_symm_selected_re (i : Fin (n + 1))
    (p : AnchorJacobian.Space (dimension n m)) : (((split i).symm p).1 i).re = p.1.1 := by
  have h := congrArg (fun q : AnchorJacobian.Space (dimension n m) ↦ q.1.1)
    ((split i).apply_symm_apply p)
  exact h

@[simp] theorem split_symm_selected_im (i : Fin (n + 1))
    (p : AnchorJacobian.Space (dimension n m)) : (((split i).symm p).1 i).im = p.1.2 := by
  have h := congrArg (fun q : AnchorJacobian.Space (dimension n m) ↦ q.1.2)
    ((split i).apply_symm_apply p)
  exact h

@[simp] theorem split_symm_other (i : Fin (n + 1))
    (p : AnchorJacobian.Space (dimension n m)) (j : Fin n) :
    ((split i).symm p).1 (i.succAbove j) = ((realCoordinates n m).symm p.2).1 j := by
  simp only [split_symm_apply, Fin.insertNth_apply_succAbove]

@[simp] theorem split_symm_boundary (i : Fin (n + 1))
    (p : AnchorJacobian.Space (dimension n m)) (j : Fin m) :
    ((split i).symm p).2 j = ((realCoordinates n m).symm p.2).2 j := rfl

/-- Real and boundary coordinates shift by `x`; imaginary coordinates do not. -/
def shiftMask (n m : ℕ) (r : Fin (dimension n m)) : ℝ :=
  match (coordinateIndexEquiv n m).symm r with
  | .inl (_, a) => if a = 0 then 1 else 0
  | .inr _ => 1

@[simp] theorem shiftMask_internal (j : Fin n) (a : Fin 2) :
    shiftMask n m (coordinateIndexEquiv n m (.inl (j, a))) = if a = 0 then 1 else 0 := by
  simp [shiftMask]

@[simp] theorem shiftMask_external (j : Fin m) :
    shiftMask n m (externalBasisIndex n j) = 1 := by
  simp [shiftMask, externalBasisIndex]

/-- Global conjugacy of the actual rational anchor change with the explicit
Jacobian model. No admissibility or nonvanishing premise is needed for this identity. -/
theorem split_anchorChangeRaw (i : Fin (n + 1)) (x : Coordinates (n + 1) m) :
    split i (anchorChangeRaw i.succ x) = AnchorJacobian.anchorSwap (shiftMask n m) (split i x) := by
  apply Prod.ext
  · apply Prod.ext
    · change ((anchorChangeRaw i.succ x).1 i).re = -(x.1 i).re / (x.1 i).im
      exact anchorChangeRaw_selected_re i x
    · change ((anchorChangeRaw i.succ x).1 i).im = 1 / (x.1 i).im
      exact anchorChangeRaw_selected_im i x
  · funext r
    obtain ⟨q, rfl⟩ := (coordinateIndexEquiv n m).surjective r
    cases q with
    | inl q =>
        obtain ⟨j, a⟩ := q
        change (split i (anchorChangeRaw i.succ x)).2 (coordinateIndexEquiv n m (.inl (j, a))) =
          ((split i x).2 (coordinateIndexEquiv n m (.inl (j, a))) -
            shiftMask n m (coordinateIndexEquiv n m (.inl (j, a))) * (split i x).1.1) / (split i x).1.2
        rw [split_internal, split_internal, shiftMask_internal, split_x, split_y,
          anchorChangeRaw_other i (i.succAbove j) (Fin.succAbove_ne i j)]
        fin_cases a <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
    | inr j =>
        change (split i (anchorChangeRaw i.succ x)).2 (externalBasisIndex n j) =
          ((split i x).2 (externalBasisIndex n j) -
            shiftMask n m (externalBasisIndex n j) * (split i x).1.1) / (split i x).1.2
        rw [split_external, split_external, shiftMask_external, split_x, split_y,
          anchorChangeRaw_snd]
        simp

theorem anchorChangeRaw_conjugate (i : Fin (n + 1))
    (p : AnchorJacobian.Space (dimension n m)) :
    split i (anchorChangeRaw i.succ ((split i).symm p)) = AnchorJacobian.anchorSwap (shiftMask n m) p := by
  rw [split_anchorChangeRaw, ContinuousLinearEquiv.apply_symm_apply]

end EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCoordinateSplit
