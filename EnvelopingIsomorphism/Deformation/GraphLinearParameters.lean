import EnvelopingIsomorphism.Deformation.GraphBaseChange
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Homogeneity of actual linear-Poisson graph formulas in their structural
coefficients. Each internal vertex contributes exactly one scalar factor. -/

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph

open scoped BigOperators

variable {R : Type*} [CommRing R] {n d : ℕ}

theorem linearCoefficient_mul (a : R) (c : Fin d → R) :
    linearCoefficient (fun r ↦ a * c r) = a • linearCoefficient c := by
  simp [linearCoefficient, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- Scale the tensor independently at each internal vertex. -/
def scaleCoefficients (a : Fin n → R) (α : Coefficients n d R) : Coefficients n d R :=
  fun v i j r ↦ a v * α v i j r

theorem labelledOperator_scaleCoefficients (Γ : KontsevichGraph n)
    (a : Fin n → R) (α : Coefficients n d R) (lab : Edge n → Fin d)
    (f g : Polynomial d R) :
    Γ.labelledOperator (scaleCoefficients a α) lab f g =
      (∏ v, a v) • Γ.labelledOperator α lab f g := by
  unfold scaleCoefficients
  rw [labelledOperator_apply, labelledOperator_apply]
  simp only [Fintype.prod_sum_type, vertexInput,
    linearCoefficient_mul, map_smul, Finset.prod_smul, smul_mul_assoc]

theorem operator_scaleCoefficients (Γ : KontsevichGraph n)
    (a : Fin n → R) (α : Coefficients n d R) (f g : Polynomial d R) :
    Γ.operator (scaleCoefficients a α) f g = (∏ v, a v) • Γ.operator α f g := by
  simp only [operator_apply, labelledOperator_scaleCoefficients, Finset.smul_sum]

/-- A common scalar is raised to the number of internal vertices. -/
theorem operator_mul_coefficients (Γ : KontsevichGraph n)
    (a : R) (α : Coefficients n d R) (f g : Polynomial d R) :
    Γ.operator (fun v i j r ↦ a * α v i j r) f g = a ^ n • Γ.operator α f g := by
  have h := operator_scaleCoefficients Γ (fun _ ↦ a) α f g
  unfold scaleCoefficients at h
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem weightedOperator_mul_coefficients
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → R)
    (a : R) (α : Coefficients n d R) (f g : Polynomial d R) :
    weightedOperator s w (fun v i j r ↦ a * α v i j r) f g =
      a ^ n • weightedOperator s w α f g := by
  simp only [weightedOperator_apply, operator_mul_coefficients, Finset.smul_sum,
    smul_comm (w _) (a ^ n)]

theorem operator_zero_coefficients (Γ : KontsevichGraph n) (hn : 0 < n)
    (f g : Polynomial d R) : Γ.operator (fun _ _ _ _ ↦ 0) f g = 0 := by
  have h := operator_mul_coefficients Γ 0 (fun _ _ _ _ ↦ (0 : R)) f g
  simpa only [zero_mul, zero_pow (Nat.ne_of_gt hn), zero_smul] using h

theorem weightedOperator_zero_coefficients
    (s : Finset (KontsevichGraph n)) (w : KontsevichGraph n → R) (hn : 0 < n)
    (f g : Polynomial d R) : weightedOperator s w (fun _ _ _ _ ↦ 0) f g = 0 := by
  simp only [weightedOperator_apply, operator_zero_coefficients _ hn, smul_zero, Finset.sum_const_zero]

/-- The full graph series at the zero linear Poisson tensor is exactly ordinary multiplication. -/
theorem graphStarSeries_zero_coefficients
    (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
    (w : (j : ℕ) → KontsevichGraph (j + 1) → R) (f g : Polynomial d R) :
    graphStarSeries s w (fun _ _ _ ↦ 0) f g = PowerSeries.C (f * g) := by
  apply PowerSeries.ext
  intro r
  cases r with
  | zero => simp only [coeff_graphStarSeries_zero, PowerSeries.coeff_C, if_true]
  | succ r =>
    rw [coeff_graphStarSeries_succ, weightedOperator_zero_coefficients _ _ (Nat.succ_pos r)]
    simp

end EnvelopingIsomorphism.Deformation.KontsevichGraph
