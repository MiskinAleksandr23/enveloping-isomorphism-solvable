import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Explicit volume-preserving Cartesian coordinates: angle first, interleaved
planar real/imaginary pairs, then coarse real/imaginary pairs and boundaries. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian
open MeasureTheory BoxStokes
open scoped Classical

def interleaved (N : ℕ) : Fin N ⊕ Fin N ≃ Fin (N * 2) where
  toFun := Sum.elim (fun j ↦ finProdFinEquiv (j, 0)) (fun j ↦ finProdFinEquiv (j, 1))
  invFun k := if ((finProdFinEquiv.symm k).2 : Fin 2) = 0 then Sum.inl (finProdFinEquiv.symm k).1
    else Sum.inr (finProdFinEquiv.symm k).1
  left_inv j := by cases j <;> simp
  right_inv k := by
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective k
    fin_cases b <;> simp

def split (A B : ℕ) : Coord (A + B) ≃L[ℝ] Coord A × Coord B :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (A + B) ↦ ℝ) finSumFinEquiv).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin A) (Fin B) (fun _ ↦ ℝ))

def splitMeas (A B : ℕ) : Coord (A + B) ≃ᵐ Coord A × Coord B :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (A + B) ↦ ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin A ⊕ Fin B ↦ ℝ))

@[simp] theorem splitMeas_eq (A B : ℕ) : (splitMeas A B : _ → _) = split A B := rfl

theorem volume_preserving_split (A B : ℕ) : MeasurePreserving (splitMeas A B) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin A ⊕ Fin B ↦ ℝ)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (A+B) ↦ ℝ) finSumFinEquiv).symm _)

def pairPi (N : ℕ) : ((Fin N → ℝ) × (Fin N → ℝ)) ≃L[ℝ] (Fin N → ℝ × ℝ) where
  toFun p j := (p.1 j, p.2 j)
  invFun f := (fun j ↦ (f j).1, fun j ↦ (f j).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def complex (N : ℕ) : Coord (N * 2) ≃L[ℝ] (Fin N → ℂ) :=
  ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (N * 2) ↦ ℝ) (interleaved N)).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin N) (Fin N) (fun _ ↦ ℝ))).trans
      ((pairPi N).trans (ContinuousLinearEquiv.piCongrRight fun _ ↦ Complex.equivRealProdCLM.symm))

def complexMeas (N : ℕ) : Coord (N * 2) ≃ᵐ (Fin N → ℂ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (N * 2) ↦ ℝ) (interleaved N)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N ↦ ℝ))).trans
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm.trans
        (MeasurableEquiv.piCongrRight fun _ ↦ Complex.measurableEquivRealProd.symm))

@[simp] theorem complexMeas_eq (N : ℕ) : (complexMeas N : _ → _) = complex N := rfl

theorem volume_preserving_complex (N : ℕ) : MeasurePreserving (complexMeas N) :=
  ((volume_preserving_pi (fun _ : Fin N ↦ Complex.volume_preserving_equiv_real_prod.symm)).comp
    ((volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _)).comp
      ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N ↦ ℝ)).comp
        ((volume_measurePreserving_piCongrLeft (fun _ : Fin (N * 2) ↦ ℝ) (interleaved N)).symm _))

def shape (N : ℕ) : Coord (1 + N * 2) ≃L[ℝ] InteriorFiberAngleSplit.Parameters N :=
  (split 1 (N * 2)).trans ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr (complex N))

def shapeMeas (N : ℕ) : Coord (1 + N * 2) ≃ᵐ InteriorFiberAngleSplit.Parameters N :=
  (splitMeas 1 (N * 2)).trans ((MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (complexMeas N))

@[simp] theorem shapeMeas_eq (N : ℕ) : (shapeMeas N : _ → _) = shape N := rfl

theorem volume_preserving_shape (N : ℕ) : MeasurePreserving (shapeMeas N) :=
  ((volume_preserving_funUnique (Fin 1) ℝ).prod (volume_preserving_complex N)).comp (volume_preserving_split 1 (N * 2))

def coarse (M m : ℕ) : Coord (M * 2 + m) ≃L[ℝ] GraphForms.Coordinates M m :=
  (split (M * 2) m).trans ((complex M).prodCongr (ContinuousLinearEquiv.refl ℝ (Coord m)))

def coarseMeas (M m : ℕ) : Coord (M * 2 + m) ≃ᵐ GraphForms.Coordinates M m :=
  (splitMeas (M * 2) m).trans ((complexMeas M).prodCongr (MeasurableEquiv.refl (Coord m)))

@[simp] theorem coarseMeas_eq (M m : ℕ) : (coarseMeas M m : _ → _) = coarse M m := rfl

theorem volume_preserving_coarse (M m : ℕ) : MeasurePreserving (coarseMeas M m) :=
  ((volume_preserving_complex M).prod (MeasurePreserving.id _)).comp (volume_preserving_split (M * 2) m)

abbrev Dim (N M m : ℕ) := (1 + N * 2) + (M * 2 + m)
abbrev Product (N M m : ℕ) := InteriorFiberAngleSplit.Parameters N × GraphForms.Coordinates M m

def cartesian (N M m : ℕ) : Coord (Dim N M m) ≃L[ℝ] Product N M m :=
  (split (1 + N * 2) (M * 2 + m)).trans ((shape N).prodCongr (coarse M m))

def cartesianMeas (N M m : ℕ) : Coord (Dim N M m) ≃ᵐ Product N M m :=
  (splitMeas (1 + N * 2) (M * 2 + m)).trans ((shapeMeas N).prodCongr (coarseMeas M m))

@[simp] theorem cartesianMeas_eq (N M m : ℕ) : (cartesianMeas N M m : _ → _) = cartesian N M m := rfl

theorem volume_preserving_cartesian (N M m : ℕ) : MeasurePreserving (cartesianMeas N M m) :=
  ((volume_preserving_shape N).prod (volume_preserving_coarse M m)).comp
    (volume_preserving_split (1 + N * 2) (M * 2 + m))

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarCoarseCartesian
