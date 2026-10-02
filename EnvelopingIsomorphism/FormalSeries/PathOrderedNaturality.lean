import EnvelopingIsomorphism.FormalSeries.PathOrderedExp

/-! Naturality of the actual path-ordered exponential under coefficient ring homomorphisms.
Both coefficient rings may be noncommutative rational algebras.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PathOrderedExp

open PowerSeries

variable {R S : Type*} [Ring R] [Ring S]

/-- Apply a coefficient homomorphism while preserving both formal parameters. -/
def mapPath (ρ : R →+* S) : PathSeries R →+* PathSeries S :=
  PowerSeries.map (Polynomial.mapRingHom ρ)

@[simp] theorem coeff_mapPath (ρ : R →+* S) (F : PathSeries R) (n : ℕ) :
    coeff n (mapPath ρ F) = (coeff n F).map ρ := rfl

@[simp] theorem constantCoeff_mapPath (ρ : R →+* S) (F : PathSeries R) :
    constantCoeff (mapPath ρ F) = (constantCoeff F).map ρ := rfl

theorem mapPath_positive (ρ : R →+* S) {X : PathSeries R} (hX : constantCoeff X = 0) :
    constantCoeff (mapPath ρ X) = 0 := by simp [hX]

theorem mapPath_coeff_zero (ρ : R →+* S) {X : PathSeries R} {N : ℕ}
    (hX : ∀ n < N, coeff n X = 0) : ∀ n < N, coeff n (mapPath ρ X) = 0 := by
  intro n hn
  simp [hX n hn]

theorem mapPath_toJet_eq (ρ : R →+* S) {X Y : PathSeries R} {N : ℕ}
    (h : toJet N X = toJet N Y) : toJet N (mapPath ρ X) = toJet N (mapPath ρ Y) := by
  apply toJet_eq_iff.mpr
  intro n hn
  rw [coeff_mapPath, coeff_mapPath, toJet_eq_iff.mp h n hn]

theorem mapPath_nearIdentity (ρ : R →+* S) {X : PathSeries R} {N : ℕ}
    (h : toJet N X = 1) : toJet N (mapPath ρ X) = 1 := by
  have hh : toJet N X = toJet N 1 := by simpa using h
  simpa using mapPath_toJet_eq ρ hh

variable [Algebra ℚ R] [Algebra ℚ S]

theorem mapPath_parameterDerivative (ρ : R →+* S) (F : PathSeries R) :
    mapPath ρ (parameterDerivative F) = parameterDerivative (mapPath ρ F) := by
  ext n
  simp [Polynomial.derivative_map]

omit [Algebra ℚ R] [Algebra ℚ S] in
@[simp] theorem atZero_mapPath (ρ : R →+* S) (F : PathSeries R) :
    atZero (mapPath ρ F) = PowerSeries.map ρ (atZero F) := by
  ext n
  simp

theorem polynomialIntegral_map (ρ : R →+* S) (p : Polynomial R) :
    (PolynomialIntegral.integral p).map ρ = PolynomialIntegral.integral (p.map ρ) := by
  apply PolynomialIntegral.integral_unique
  · rw [Polynomial.derivative_map, PolynomialIntegral.derivative_integral]
  · simp

theorem map_solutionCoeff (ρ : R →+* S) (X : PathSeries R) (n : ℕ) :
    (solutionCoeff X n).map ρ = solutionCoeff (mapPath ρ X) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [solutionCoeff_succ, polynomialIntegral_map, solutionCoeff_succ]
      congr 1
      simp only [Polynomial.map_sum, Polynomial.map_mul, coeff_mapPath]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (n - i) (by omega)]

/-- Naturality holds for the constructed recursion itself, even before positivity is supplied. -/
@[simp] theorem mapPath_solution (ρ : R →+* S) (X : PathSeries R) :
    mapPath ρ (solution X) = solution (mapPath ρ X) := by
  ext n
  simp [map_solutionCoeff]

@[simp] theorem mapPath_pathUnit (ρ : R →+* S) (X : PathSeries R) :
    Units.map (mapPath ρ).toMonoidHom (pathUnit X) = pathUnit (mapPath ρ X) := by
  apply Units.ext
  exact mapPath_solution ρ X

@[simp] theorem mapPath_inverse (ρ : R →+* S) (X : PathSeries R) :
    mapPath ρ (inverseOne (solution X)) = inverseOne (solution (mapPath ρ X)) := by
  have h := congrArg (fun u : (PathSeries S)ˣ ↦ (↑(u⁻¹) : PathSeries S))
    (mapPath_pathUnit ρ X)
  exact h

@[simp] theorem evaluation_one_mapPath (ρ : R →+* S) (F : PathSeries R) :
    evaluation 1 (mapPath ρ F) = PowerSeries.map ρ (evaluation 1 F) := by
  ext n
  simp only [coeff_evaluation, coeff_mapPath, coeff_map, map_one,
    Polynomial.eval₂_at_one, RingHom.id_apply]
  exact Polynomial.eval_one_map ρ _

/-- The endpoint is the image of the original genuine unit, not an independently chosen gauge. -/
theorem endpointUnit_mapPath (ρ : R →+* S) (X : PathSeries R) :
    endpointUnit (mapPath ρ X) =
      Units.map (PowerSeries.map ρ).toMonoidHom (endpointUnit X) := by
  apply Units.ext
  change evaluation 1 (solution (mapPath ρ X)) = PowerSeries.map ρ (evaluation 1 (solution X))
  rw [← mapPath_solution, evaluation_one_mapPath]

end EnvelopingIsomorphism.FormalSeries.PathOrderedExp
