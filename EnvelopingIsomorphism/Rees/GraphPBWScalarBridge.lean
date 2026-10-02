import EnvelopingIsomorphism.Deformation.GraphPBWComparison
import EnvelopingIsomorphism.FormalSeries.CompletedPolynomialInputs

/-!
The two polynomial parameters of the finite graph comparison enter the genuine
completion in their specified order: the coefficient variable stays outer,
whereas the polynomial variable becomes the inner Laurent parameter.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.GraphPBWScalarBridge

open FormalSeries PolynomialCoefficientOperators
open scoped LaurentPolynomialCoefficients CompletedOperator CompletedPolynomialInputs

variable (k : Type*) [Field k]

/-- The outer variable of `k[t][h]` becomes the inner Laurent parameter `h`.
The coefficient polynomial variable remains the outer parameter `t`. -/
def scalarMap : Polynomial (Polynomial k) →+* LaurentPolynomialCoefficients.ScalarRing k :=
  Polynomial.eval₂RingHom (LaurentPolynomialCoefficients.parameterMap k)
    (Polynomial.C (HahnSeries.single 1 (1 : k)))

@[simp] theorem scalarMap_C (p : Polynomial k) :
    scalarMap k (Polynomial.C p) = LaurentPolynomialCoefficients.parameterMap k p := by
  simp [scalarMap]

@[simp] theorem scalarMap_X :
    scalarMap k Polynomial.X = Polynomial.C (HahnSeries.single 1 (1 : k)) := by
  simp [scalarMap]

theorem scalarMap_monomial (n : ℕ) (p : Polynomial k) :
    scalarMap k (Polynomial.monomial n p) =
      Homogenization.unitPower (LaurentPolynomialCoefficients.hbarPolynomialUnit k) (n : ℤ) *
        LaurentPolynomialCoefficients.parameterMap k p := by
  rw [Homogenization.unitPower_nat, LaurentPolynomialCoefficients.hbarPolynomialUnit_val]
  simp only [scalarMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  exact mul_comm _ _

/-- Extracting both output coefficients is exactly extraction in the opposite
order from the two finite polynomial parameters. -/
theorem doubleCoeff_scalarMap (p : Polynomial (Polynomial k)) (r : ℕ) (j : ℤ) :
    LaurentPolynomialCoefficients.doubleCoeff k r j (scalarMap k p) =
      if j < 0 then 0 else (p.coeff j.natAbs).coeff r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
      by_cases hj : j < 0 <;> simp [hj, Polynomial.coeff_add]
  | monomial n p =>
      rw [scalarMap_monomial, LaurentPolynomialCoefficients.doubleCoeff_apply]
      change ((Homogenization.unitPower (LaurentPolynomialCoefficients.hbarPolynomialUnit k)
        (n : ℤ) * algebraMap (Polynomial k) (LaurentPolynomialCoefficients.ScalarRing k) p).coeff r).coeff j = _
      rw [LaurentPolynomialCoefficients.doubleCoeff_unitPower_parameter]
      by_cases hj : j < 0
      · have hn : j ≠ (n : ℤ) := by omega
        simp [hj, hn]
      · have ha : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg (le_of_not_gt hj)
        by_cases hn : j = (n : ℤ)
        · simp [hn]
        · have hnat : n ≠ j.natAbs := by omega
          simp [hj, hn, Polynomial.coeff_monomial, hnat]

@[simp] theorem scalarMap_algebraMap (a : k) :
    scalarMap k (algebraMap k (Polynomial (Polynomial k)) a) =
      algebraMap k (LaurentPolynomialCoefficients.ScalarRing k) a := by
  simp [Polynomial.algebraMap_apply]

theorem map_includePolynomial {ι : Type*} (a : Coordinates ι k) :
    MvPolynomial.map (scalarMap k)
        (includePolynomial (S := Polynomial (Polynomial k)) a) =
      includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) a := by
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_map]
  change scalarMap k (algebraMap k (Polynomial (Polynomial k)) (a m)) =
    algebraMap k (LaurentPolynomialCoefficients.ScalarRing k) (a m)
  exact scalarMap_algebraMap k (a m)

section Comparison

variable [CharZero k] {d : ℕ}
  (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 1)))
  (wTH : (j : ℕ) → Deformation.KontsevichGraph (j + 1) → Polynomial (Polynomial k))
  (cTH : Fin d → Fin d → Fin d → Polynomial (Polynomial k))

/-- The same finite graph comparison after the specified two-parameter map. -/
def comparisonFinite :
    MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k) →ₗ[
      LaurentPolynomialCoefficients.ScalarRing k]
      MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k) :=
  Deformation.KontsevichGraph.comparisonMap s
    (fun j Γ ↦ scalarMap k (wTH j Γ))
    (fun i j r ↦ scalarMap k (Polynomial.X * cTH i j r))

/-- Scalar naturality includes the original coefficient vectors by their actual
algebra map into each of the two finite coefficient rings. -/
theorem map_comparison_input (a : Coordinates (Fin d) k) :
    MvPolynomial.map (scalarMap k)
      (Deformation.KontsevichGraph.comparisonMap s wTH
        (fun i j r ↦ Polynomial.X * cTH i j r)
        (includePolynomial (S := Polynomial (Polynomial k)) a)) =
      comparisonFinite k s wTH cTH
        (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) a) := by
  rw [Deformation.KontsevichGraph.map_comparisonMap, map_includePolynomial]
  rfl

/-- Actual completed operator coefficients coincide with extraction from the
finite comparison over Laurent-polynomial scalars. -/
theorem completed_coefficient (r : ℕ) (j : ℤ)
    (a : Coordinates (Fin d) k) (m : Fin d →₀ ℕ) :
    (PowerSeries.coeff r
      (Deformation.KontsevichGraph.comparisonCompleted s wTH cTH)).coeff j a m =
      LaurentPolynomialCoefficients.doubleCoeff k r j
        (MvPolynomial.coeff m (comparisonFinite k s wTH cTH
          (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) a))) := by
  have hm := congrArg (MvPolynomial.coeff m) (map_comparison_input k s wTH cTH a)
  rw [MvPolynomial.coeff_map] at hm
  rw [← hm, doubleCoeff_scalarMap]
  by_cases hj : j < 0
  · rw [if_pos hj, Deformation.KontsevichGraph.comparisonCompleted_coefficient_neg
      s wTH cTH r j hj]
    rfl
  · rw [if_neg hj]
    have ha : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg (le_of_not_gt hj)
    have hc := Deformation.KontsevichGraph.comparisonCompleted_coefficient_nat
      s wTH cTH r j.natAbs
    rw [ha] at hc
    rw [hc]
    exact Deformation.KontsevichGraph.comparisonRows_coefficient s wTH cTH r j.natAbs a m

/-- The genuine completed graph operator agrees on constant coordinate inputs
with the embedded finite polynomial comparison. -/
theorem completedAction_constant (a : Coordinates (Fin d) k) :
    CompletedOperator.actionHom
        (Deformation.KontsevichGraph.comparisonCompleted s wTH cTH)
        (CompletedOperator.constant a) =
      CompletedPolynomialInputs.embed (comparisonFinite k s wTH cTH
        (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) a)) := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply Finsupp.ext
  intro m
  rw [CompletedOperator.coeff_action_constant, CompletedPolynomialInputs.coeff_embed]
  exact completed_coefficient k s wTH cTH r j a m

/-- Full scalar linearity extends the constant-input formula to every finite
polynomial with Laurent-polynomial coefficients. -/
theorem completedAction_polynomial
    (p : MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k)) :
    CompletedOperator.actionHom
        (Deformation.KontsevichGraph.comparisonCompleted s wTH cTH)
        (CompletedPolynomialInputs.embed p) =
      CompletedPolynomialInputs.embed (comparisonFinite k s wTH cTH p) :=
  CompletedPolynomialInputs.linear_extension _ _
    (completedAction_constant k s wTH cTH) p

theorem completedUnitAction_constant (a : Coordinates (Fin d) k) :
    CompletedOperator.actionEquiv
        (Deformation.KontsevichGraph.comparisonCompletedUnit s wTH cTH)
        (CompletedOperator.constant a) =
      CompletedPolynomialInputs.embed (comparisonFinite k s wTH cTH
        (includePolynomial (S := LaurentPolynomialCoefficients.ScalarRing k) a)) := by
  rw [CompletedOperator.actionEquiv_apply,
    Deformation.KontsevichGraph.comparisonCompletedUnit_val]
  exact completedAction_constant k s wTH cTH a

theorem completedUnitAction_polynomial
    (p : MvPolynomial (Fin d) (LaurentPolynomialCoefficients.ScalarRing k)) :
    CompletedOperator.actionEquiv
        (Deformation.KontsevichGraph.comparisonCompletedUnit s wTH cTH)
        (CompletedPolynomialInputs.embed p) =
      CompletedPolynomialInputs.embed (comparisonFinite k s wTH cTH p) := by
  rw [CompletedOperator.actionEquiv_apply,
    Deformation.KontsevichGraph.comparisonCompletedUnit_val]
  exact completedAction_polynomial k s wTH cTH p

end Comparison

end EnvelopingIsomorphism.Rees.GraphPBWScalarBridge
