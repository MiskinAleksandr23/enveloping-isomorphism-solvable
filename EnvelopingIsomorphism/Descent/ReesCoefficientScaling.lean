import EnvelopingIsomorphism.Descent.ReesMatrixArc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Coefficient equations for the original Lie brackets follow from the Rees
matrix equations by diagonal Laurent scaling. -/

namespace EnvelopingIsomorphism.Descent.MatrixGroup

open scoped BigOperators

noncomputable section

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Conjugating a matrix transports bracket equations under compatible diagonal
rescalings of the structure coefficients. -/
theorem diagonalConjugate_structure_equation
    (s : n → Kˣ) (P : Matrix.GeneralLinearGroup n K)
    (cL cM dL dM : n → n → n → K)
    (hL : ∀ i j r, dL i j r * (s r : K) = (s i : K) * (s j : K) * cL i j r)
    (hM : ∀ i j r, dM i j r * (s r : K) = (s i : K) * (s j : K) * cM i j r)
    (hP : ∀ i j r, (∑ a, ∑ b, dM a b r * (P.val a i * P.val b j)) =
      ∑ d, dL i j d * P.val r d)
    (i j r : n) :
    (∑ a, ∑ b, cM a b r *
      ((diagonalConjugate s P).val a i * (diagonalConjugate s P).val b j)) =
      ∑ d, cL i j d * (diagonalConjugate s P).val r d := by
  have hs : ∀ a, (s a : K) ≠ 0 := fun a => (s a).ne_zero
  have hL' : ∀ a b d, dL a b d = (s a : K) * (s b : K) * cL a b d / (s d : K) :=
    fun a b d => (eq_div_iff (hs d)).mpr (hL a b d)
  have hM' : ∀ a b d, dM a b d = (s a : K) * (s b : K) * cM a b d / (s d : K) :=
    fun a b d => (eq_div_iff (hs d)).mpr (hM a b d)
  let factor : K := (s i : K) * (s j : K) / (s r : K)
  have hfactor : factor ≠ 0 := div_ne_zero (mul_ne_zero (hs i) (hs j)) (hs r)
  apply mul_left_cancel₀ hfactor
  rw [Finset.mul_sum, Finset.mul_sum]
  calc
    (∑ a, factor * ∑ b, cM a b r *
        ((diagonalConjugate s P).val a i * (diagonalConjugate s P).val b j)) =
        ∑ a, ∑ b, dM a b r * (P.val a i * P.val b j) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [diagonalConjugate_entry, diagonalConjugate_entry, hM']
      simp only [Units.val_inv_eq_inv_val]
      dsimp [factor]
      field_simp
    _ = ∑ d, dL i j d * P.val r d := hP i j r
    _ = ∑ d, factor * (cL i j d * (diagonalConjugate s P).val r d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [diagonalConjugate_entry, hL']
      simp only [Units.val_inv_eq_inv_val]
      dsimp [factor]
      field_simp

section Laurent

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- A Rees structure coefficient in the actual regular coefficient ring. -/
def reesCoefficient (weight : n → ℕ) (c : n → n → n → k) (i j r : n) : PowerSeries E :=
  PowerSeries.C (algebraMap k E (c i j r)) *
    PowerSeries.X ^ (weight r - (weight i + weight j))

theorem reesCoefficient_scale (weight : n → ℕ) (c : n → n → n → k)
    (hc : ∀ i j r, c i j r ≠ 0 → weight i + weight j ≤ weight r)
    (i j r : n) :
    algebraMap (PowerSeries E) (LaurentSeries E) (reesCoefficient weight c i j r) *
        (weightScale (E := E) weight r : LaurentSeries E) =
      (weightScale (E := E) weight i : LaurentSeries E) *
        (weightScale (E := E) weight j : LaurentSeries E) *
        algebraMap k (LaurentSeries E) (c i j r) := by
  by_cases hzero : c i j r = 0
  · simp [reesCoefficient, hzero]
  · have hw := hc i j r hzero
    have he : ((weight r - (weight i + weight j) : ℕ) : ℤ) + -(weight r : ℤ) =
        -(weight i : ℤ) + -(weight j : ℤ) := by omega
    simp [reesCoefficient, weightScale, LaurentSeries.coe_algebraMap,
      PowerSeries.algebraMap_apply, HahnSeries.algebraMap_apply', HahnSeries.C_apply,
      HahnSeries.single_mul_single, he]

theorem originalGenericMatrix_structure_equation
    (weight : n → ℕ) (cL cM : n → n → n → k)
    (hcL : ∀ i j r, cL i j r ≠ 0 → weight i + weight j ≤ weight r)
    (hcM : ∀ i j r, cM i j r ≠ 0 → weight i + weight j ≤ weight r)
    (P : Matrix.GeneralLinearGroup n (PowerSeries E))
    (hP : ∀ i j r, (∑ a, ∑ b, reesCoefficient weight cM a b r * (P.val a i * P.val b j)) =
      ∑ d, reesCoefficient weight cL i j d * P.val r d)
    (i j r : n) :
    (∑ a, ∑ b, algebraMap k (LaurentSeries E) (cM a b r) *
      ((originalGenericMatrix weight P).val a i * (originalGenericMatrix weight P).val b j)) =
      ∑ d, algebraMap k (LaurentSeries E) (cL i j d) *
        (originalGenericMatrix weight P).val r d := by
  apply diagonalConjugate_structure_equation (weightScale weight)
    (Matrix.GeneralLinearGroup.map (algebraMap (PowerSeries E) (LaurentSeries E)) P)
    (fun i j r => algebraMap k (LaurentSeries E) (cL i j r))
    (fun i j r => algebraMap k (LaurentSeries E) (cM i j r))
    (fun i j r => algebraMap (PowerSeries E) (LaurentSeries E) (reesCoefficient weight cL i j r))
    (fun i j r => algebraMap (PowerSeries E) (LaurentSeries E) (reesCoefficient weight cM i j r))
    (reesCoefficient_scale weight cL hcL) (reesCoefficient_scale weight cM hcM)
  intro a b d
  have h := congrArg (algebraMap (PowerSeries E) (LaurentSeries E)) (hP a b d)
  convert h using 1 <;> simp only [map_sum, map_mul] <;> rfl

end Laurent

end

end EnvelopingIsomorphism.Descent.MatrixGroup
