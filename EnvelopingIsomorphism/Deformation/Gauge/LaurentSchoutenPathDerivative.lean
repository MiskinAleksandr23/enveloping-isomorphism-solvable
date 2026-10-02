import EnvelopingIsomorphism.Deformation.Gauge.LaurentSchoutenPath

/-! Actual polynomial-parameter ODE for the monomial exponential and Laurent Schouten source path. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.Gauge.MonomialOperatorPath
open EnvelopingIsomorphism.FormalSeries PowerSeries
open scoped BigOperators Classical

section Ring
variable {R : Type*} [Ring R] [Algebra ℚ R]

omit [Algebra ℚ R] in
/-- Left multiplication by a genuine monomial shifts the outer formal degree. -/
theorem coeff_monomial_left (F : PowerSeries R) (D : R) (N n : ℕ) :
    coeff n (monomial N D * F) = if N ≤ n then D * coeff (n - N) F else 0 := by
  rw [coeff_mul]
  by_cases hn : N ≤ n
  · rw [if_pos hn, Finset.sum_eq_single (N, n-N)]
    · simp
    · intro p hp hne
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hpn : p.1 ≠ N := by
        intro he
        apply hne
        apply Prod.ext he
        omega
      simp [coeff_monomial, hpn]
    · intro hp
      exact (hp (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hpn : p.1 ≠ N := by omega
    simp [coeff_monomial, hpn]

/-- The finite exponential coefficient at outer degree n and parameter degree m. -/
theorem coeff_parameter_exp_monomial (N : ℕ) (hN : 0 < N) (D : R) (n m : ℕ) :
    (coeff n (FormalSeries.exp (monomial N (Polynomial.monomial 1 D)))).coeff m =
      if m * N = n then (m.factorial : ℚ)⁻¹ • D ^ m else 0 := by
  simp only [FormalSeries.exp, coeff_sumPowers, noncomm_monomial_pow, coeff_monomial,
    Polynomial.monomial_pow, one_mul, one_div]
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · split_ifs <;> simp_all [Polynomial.coeff_smul, eq_comm]
  · intro j hj hjm
    split_ifs <;> simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hjm]
  · intro hm
    have hmn : n < m := by simpa using hm
    have hbad : m * N ≠ n := by
      have hl := Nat.le_mul_of_pos_right m hN
      omega
    simp [Ne.symm hbad]

/-- The exact factorial recurrence cancels the derivative factor without commuting operators. -/
theorem factorial_derivative (D : R) (m : ℕ) :
    (((m + 1).factorial : ℚ)⁻¹ • D ^ (m + 1)) * (m + 1 : R) =
      D * ((m.factorial : ℚ)⁻¹ • D ^ m) := by
  rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_smul_comm, ← pow_succ']
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hm : (m + 1 : ℚ) ≠ 0 := by positivity
  field_simp

/-- The polynomial-parameter exponential solves its actual constant-velocity equation. -/
theorem parameterDerivative_exp_monomial (N : ℕ) (hN : 0 < N) (D : R) :
    PathOrderedExp.parameterDerivative (FormalSeries.exp (monomial N (Polynomial.monomial 1 D))) =
      monomial N (Polynomial.C D) * FormalSeries.exp (monomial N (Polynomial.monomial 1 D)) := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.ext
  intro m
  rw [PathOrderedExp.coeff_parameterDerivative, Polynomial.coeff_derivative,
    coeff_parameter_exp_monomial N hN, coeff_monomial_left]
  by_cases he : (m + 1) * N = n
  · have hn : N ≤ n := by nlinarith
    have hm : m * N = n - N := by
      have he' : m * N + N = n := by simpa [Nat.add_mul] using he
      omega
    rw [if_pos he, if_pos hn, Polynomial.coeff_C_mul, coeff_parameter_exp_monomial N hN,
      if_pos hm]
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_derivative D m
  · rw [if_neg he, zero_mul]
    by_cases hn : N ≤ n
    · have hm : m * N ≠ n - N := by
        intro hh
        apply he
        rw [Nat.add_mul, one_mul, hh, Nat.sub_add_cancel hn]
      rw [if_pos hn, Polynomial.coeff_C_mul, coeff_parameter_exp_monomial N hN, if_neg hm, mul_zero]
    · rw [if_neg hn, Polynomial.coeff_zero]

end Ring

section Operators
variable {k V : Type*} [CommRing k] [Algebra ℚ k] [AddCommGroup V] [Module k V]
  [Module ℚ V] [IsScalarTower ℚ k V] [SMulCommClass k ℚ V]
local instance : Ring (Module.End k V) := @Module.End.instRing k V inferInstance inferInstance inferInstance
open PowerSeriesModule

omit [Algebra ℚ k] [Module ℚ V] [IsScalarTower ℚ k V] [SMulCommClass k ℚ V] in
/-- The polynomial-module bridge identifies the constant-in-parameter monomial velocity. -/
theorem pathEquiv_monomial_C (N : ℕ) (D : Module.End k V) :
    PolynomialModuleRingBridge.pathEquiv (k := k) (PowerSeries.monomial N (Polynomial.C D)) =
      constantPath (PowerSeriesModule.single N D) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [PolynomialModuleRingBridge.coeff_pathEquiv, PowerSeries.coeff_monomial,
    constantPath, PowerSeriesModule.coeffV_map, PowerSeriesModule.coeffV_single]
  by_cases h : n = N
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false, map_zero]

/-- The actual operator exponential satisfies the polynomial-path differential equation. -/
theorem operatorPath_derivative (N : ℕ) (hN : 0 < N) (D : Module.End k V) :
    PolynomialModuleCalculus.seriesDerivative (operatorPath N D) =
      pathBilinear (LinearMap.mul k (Module.End k V))
        (constantPath (PowerSeriesModule.single N D)) (operatorPath N D) := by
  rw [operatorPath, ← PolynomialModuleRingBridge.pathEquiv_derivative]
  change PolynomialModuleRingBridge.pathEquiv
    (PathOrderedExp.parameterDerivative (FormalSeries.exp (PowerSeries.monomial N (Polynomial.monomial 1 D)))) = _
  rw [parameterDerivative_exp_monomial N hN, PolynomialModuleRingBridge.pathEquiv_mul,
    pathEquiv_monomial_C]
  rfl

/-- Applying the exponential path to a fixed series retains the actual monomial action ODE. -/
theorem fullPath_derivative (N : ℕ) (hN : 0 < N) (D : Module.End k V)
    (B : PowerSeriesModule k V) :
    PolynomialModuleCalculus.seriesDerivative (fullPath N D B) =
      pathOperator (constantPath (PowerSeriesModule.single N D)) (fullPath N D B) := by
  change PolynomialModuleCalculus.seriesDerivative
    (pathBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
      (operatorPath N D) (constantPath B)) =
    pathBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
      (constantPath (PowerSeriesModule.single N D))
      (pathBilinear (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V) (operatorPath N D) (constantPath B))
  rw [pathBilinear_derivative, operatorPath_derivative N hN, constantPath_derivative,
    map_zero, add_zero]
  exact pathBilinear_assoc (LinearMap.mul k (Module.End k V))
    (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
    (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
    (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V) (fun _ _ _ ↦ rfl) _ _ _

end Operators

end EnvelopingIsomorphism.Deformation.Gauge.MonomialOperatorPath


namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
open EnvelopingIsomorphism.FormalSeries PowerSeriesModule
open scoped BigOperators Classical
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
local instance : CharZero (Scalars K) := scalarCharZero
local instance : Module ℚ (Bivector K d) := bivectorRationalModule
local instance : IsScalarTower ℚ (Scalars K) (Bivector K d) := bivectorRationalTower
local instance : SMulCommClass (Scalars K) ℚ (Bivector K d) := bivectorRationalComm
local instance : Ring (Module.End (Scalars K) (Bivector K d)) :=
  @Module.End.instRing (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance
local instance : AddCommGroup (PowerSeriesModule (Scalars K) (Bivector K d)) :=
  @HahnModule.instAddCommGroup ℕ (Scalars K) (Bivector K d) inferInstance inferInstance inferInstance

/-- The vector direction maps to its actual monomial source action. -/
theorem pathMap_action_constant_single (N : ℕ) (X : Vector K d) :
    pathMap action (constantPath (single N X)) = constantPath (single N (action X)) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathMap, constantPath, coeffV_map, coeffV_single]
  by_cases h : n = N
  · simp only [h, if_true]
    exact PolynomialModule.map_lsingle (Scalars K) (action (K := K) (d := d)) 0 X
  · simp only [h, if_false, map_zero]

/-- The actual translated source exponential solves the full polynomial action equation. -/
theorem elementaryFullPath_derivative (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) :
    PolynomialModuleCalculus.seriesDerivative (elementaryFullPath π N X b) =
      pathBilinear action (constantPath (single N X)) (elementaryFullPath π N X b) := by
  change PolynomialModuleCalculus.seriesDerivative
    (MonomialOperatorPath.fullPath N (action X) (single 0 π + b)) = _
  rw [MonomialOperatorPath.fullPath_derivative N hN,
    ← pathMap_action_constant_single, pathOperator_pathMap]
  rfl

/-- Adding back the fixed base recovers the constructed full source path. -/
theorem translated_elementaryPath (π : Bivector K d) (N : ℕ)
    (X : Vector K d) (b : Families K d) :
    constantPath (single 0 π) + elementaryPath π N X b = elementaryFullPath π N X b := by
  rw [elementaryPath]
  abel

/-- The actual affine source path solves the polynomial-parameter source action ODE. -/
theorem elementaryPath_derivative (π : Bivector K d) (N : ℕ) (hN : 0 < N)
    (X : Vector K d) (b : Families K d) :
    PolynomialModuleCalculus.seriesDerivative (elementaryPath π N X b) =
      pathBilinear action (constantPath (single N X))
        (constantPath (single 0 π) + elementaryPath π N X b) := by
  rw [translated_elementaryPath]
  calc
    PolynomialModuleCalculus.seriesDerivative (elementaryPath π N X b) =
        PolynomialModuleCalculus.seriesDerivative (elementaryFullPath π N X b) := by
      rw [elementaryPath, map_sub, constantPath_derivative, sub_zero]
    _ = _ := elementaryFullPath_derivative π N hN X b

end EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
