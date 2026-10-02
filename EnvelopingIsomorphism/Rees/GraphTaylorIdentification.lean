import EnvelopingIsomorphism.Rees.CompletedGraphProduct
import EnvelopingIsomorphism.Rees.GraphStarComparison
import EnvelopingIsomorphism.Rees.GraphHbarCoefficients
import EnvelopingIsomorphism.Rees.PoissonMCFamily
import EnvelopingIsomorphism.Deformation.Gauge.GraphTaylorCoefficients
import EnvelopingIsomorphism.Deformation.Gauge.TaylorLaurentEvaluation
import EnvelopingIsomorphism.Deformation.GraphPolynomialCoefficients

/-! Coefficient identification of the actual graph Taylor family and the actual
completed polynomial graph product on the native Rees Poisson family. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace EnvelopingIsomorphism.Rees.GraphTaylorIdentification

open FormalSeries CompletedOperator PolynomialCoefficientOperators
open Deformation.Gauge Deformation.KontsevichGraph
open scoped CompletedOperator CompletedPBWProduct LaurentPolynomialCoefficients BigOperators
open scoped Classical

variable {k L : Type*} [Field k] [CharZero k] {d : ℕ}
    [LieRing L] [LieAlgebra k L] {b : Module.Basis (Fin d) k L}
    (D : WeightData b)
    (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 1)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 1) → k)

local instance polynomialUnaryGroup : AddCommGroup (Module.End k (MvPolynomial (Fin d) k)) :=
  @LinearMap.addCommGroup k k (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) k)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (RingHom.id k)

local instance sourceSeriesGroup : AddCommGroup
    (PowerSeriesModule k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)) :=
  @HahnModule.instAddCommGroup ℕ k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
    inferInstance inferInstance inferInstance

local instance sourceLaurentGroup : AddCommGroup
    (LaurentModule k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)) :=
  @HahnModule.instAddCommGroup ℤ k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
    inferInstance inferInstance inferInstance

local instance nativeBinaryLaurentGroup : AddCommGroup
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k))) :=
  @HahnModule.instAddCommGroup ℤ k (Deformation.Binary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance

local instance nativeBinarySeriesGroup : AddCommGroup
    (PowerSeriesModule (LaurentSeries k) (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))) :=
  @HahnModule.instAddCommGroup ℕ (LaurentSeries k)
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))
    inferInstance inferInstance inferInstance

/-- Effective graph weights are constant in both parameters. No additional factorial is inserted. -/
def parameterWeights (j : ℕ) (Γ : Deformation.KontsevichGraph (j + 1)) :
    _root_.Polynomial (_root_.Polynomial k) :=
  _root_.Polynomial.C (_root_.Polynomial.C (w j Γ))

/-- The exact already constructed completed graph product for the native Rees table. -/
def graphFamily : CompletedBinary.Families k (Coordinates (Fin d) k) :=
  CompletedGraphProduct.completedProduct s (parameterWeights w) (GraphStarComparison.tensor D)

/-- The genuine multilinear Taylor family evaluated at the native Poisson series. -/
def fullTaylor : PowerSeriesModule (LaurentSeries k)
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k))) :=
  laurentScaledMCEvaluation
    (V := Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
    (W := Deformation.Binary k (MvPolynomial (Fin d) k))
    (GraphTaylorCoefficients.effectiveFamily s w)
    (PoissonMCFamily.poissonSeries D)

/-- The native polynomial space and its fixed monomial coordinates are linearly equivalent. -/
def coordinateEquiv : MvPolynomial (Fin d) k ≃ₗ[k] Coordinates (Fin d) k :=
  (MvPolynomial.basisMonomials (Fin d) k).repr

/-- Actual conjugation of a binary cochain by the monomial coordinate equivalence. -/
def binaryCoordinates : Deformation.Binary k (MvPolynomial (Fin d) k) ≃ₗ[k]
    Deformation.Binary k (Coordinates (Fin d) k) :=
  LinearEquiv.arrowCongr coordinateEquiv (LinearEquiv.arrowCongr coordinateEquiv coordinateEquiv)

omit [CharZero k] in
theorem binaryCoordinates_apply
    (B : Deformation.Binary k (MvPolynomial (Fin d) k)) (p q : MvPolynomial (Fin d) k)
    (m : Fin d →₀ ℕ) :
    binaryCoordinates B (coordinateEquiv p) (coordinateEquiv q) m =
      MvPolynomial.coeff m (B p q) := by
  simp only [binaryCoordinates, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The native Taylor output is transported by the genuine coefficient equivalence. -/
def coordinateFullTaylor : CompletedBinary.Families k (Coordinates (Fin d) k) :=
  PowerSeriesModule.map
    (LaurentModule.map (X := Deformation.Binary k (MvPolynomial (Fin d) k))
      (Y := Deformation.Binary k (Coordinates (Fin d) k)) binaryCoordinates.toLinearMap)
    (fullTaylor D s w)

omit [CharZero k] in
@[simp] theorem includePolynomial_polynomial (p : MvPolynomial (Fin d) k) :
    includePolynomial (S := _root_.Polynomial k) (coordinateEquiv p) =
      MvPolynomial.map _root_.Polynomial.C p := by
  change MvPolynomial.map _ ((coordinateEquiv (k := k) (d := d)).symm (coordinateEquiv p)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

omit [CharZero k] in
@[simp] theorem includePolynomial_double (p : MvPolynomial (Fin d) k) :
    includePolynomial (S := _root_.Polynomial (_root_.Polynomial k)) (coordinateEquiv p) =
      MvPolynomial.map _root_.Polynomial.C (MvPolynomial.map _root_.Polynomial.C p) := by
  change MvPolynomial.map _ ((coordinateEquiv (k := k) (d := d)).symm (coordinateEquiv p)) = _
  rw [LinearEquiv.symm_apply_apply, MvPolynomial.map_map]
  rfl

omit [CharZero k] in
/-- Inner degree zero of the actual graph family is ordinary multiplication. -/
theorem graphFamily_coeff_zero (r : ℕ) (p q : MvPolynomial (Fin d) k) (m : Fin d →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r (graphFamily D s w)) 0
        (coordinateEquiv p) (coordinateEquiv q) m =
      if r = 0 then MvPolynomial.coeff m (p * q) else 0 := by
  rw [graphFamily, CompletedGraphProduct.completedProduct_coeff,
    CompletedGraphProduct.coefficientBinary_source]
  simp only [lt_self_iff_false, ite_false, Int.natAbs_zero]
  unfold CompletedGraphProduct.sourceProduct parameterWeights GraphStarComparison.tensor
  simp only [polynomialProductBilinear_apply, includePolynomial_double]
  rw [GraphHbarCoefficients.polynomialProduct_coeff_zero]
  rw [← map_mul, MvPolynomial.coeff_map, _root_.Polynomial.coeff_C]

omit [CharZero k] in
/-- Each positive inner degree is the same effective weighted graph operation
over the native polynomial Rees coefficient table. -/
theorem graphFamily_coeff_succ (r n : ℕ) (p q : MvPolynomial (Fin d) k) (m : Fin d →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r (graphFamily D s w)) (n + 1 : ℕ)
        (coordinateEquiv p) (coordinateEquiv q) m =
      (MvPolynomial.coeff m
        (weightedOperator (s n) (fun Γ ↦ _root_.Polynomial.C (w n Γ)) (fun _ ↦ D.coeff)
          (MvPolynomial.map _root_.Polynomial.C p)
          (MvPolynomial.map _root_.Polynomial.C q))).coeff r := by
  rw [graphFamily, CompletedGraphProduct.completedProduct_coeff,
    CompletedGraphProduct.coefficientBinary_source]
  rw [if_neg (show ¬ (↑(n + 1) : ℤ) < 0 by omega)]
  simp only [Int.natAbs_natCast]
  unfold CompletedGraphProduct.sourceProduct parameterWeights GraphStarComparison.tensor
  simp only [polynomialProductBilinear_apply, includePolynomial_double]
  rw [GraphHbarCoefficients.polynomialProduct_coeff_succ]

omit [CharZero k] in
/-- The zero-arity effective Taylor coefficient is exactly ordinary multiplication. -/
theorem fullTaylor_coeff_zero (r : ℕ) (p q : MvPolynomial (Fin d) k) (m : Fin d →₀ ℕ) :
    MvPolynomial.coeff m (LaurentModule.coeff (X := Deformation.Binary k (MvPolynomial (Fin d) k))
      (PowerSeriesModule.coeffV r (fullTaylor D s w)) 0 p q) =
      if r = 0 then MvPolynomial.coeff m (p * q) else 0 := by
  letI : DecidableEq (Fin 0) := Classical.decEq _
  rw [fullTaylor]
  have hc := coeff_laurentScaledMCEvaluation_nat
    (GraphTaylorCoefficients.effectiveFamily s w) (PoissonMCFamily.poissonSeries D) r 0
  simp only [Nat.cast_zero] at hc
  rw [hc, PowerSeriesModule.coeffV_applyMultilinear]
  have hempty : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
  rw [hempty, Finset.piAntidiag_empty]
  by_cases hr : r = 0
  · simp [hr, GraphTaylorCoefficients.effectiveFamily_zero]
  · simp [hr]

omit [CharZero k] in
/-- Every Taylor input is the actual native coefficient bivector; independent
coefficient tensors are allowed and are not assumed individually Poisson. -/
theorem effectiveFamily_bivectorCoefficients (n : ℕ) (a : Fin (n + 1) → ℕ) :
    GraphTaylorCoefficients.effectiveFamily s w (n + 1)
        (fun v ↦ PoissonMCFamily.bivectorCoefficient D (a v)) =
      weightedOperator (s n) (w n) (fun v ↦ PoissonMCFamily.coeffTable D (a v)) :=
  GraphTaylorCoefficients.effectiveFamily_linearBivectors s w n _
    (fun v ↦ PoissonMCFamily.coeffTable_skew D (a v))
    (fun v ↦ PoissonMCFamily.coeffTable_self D (a v))

omit [CharZero k] in
/-- The actual Taylor evaluation has the finite outer-parameter convolution
of the same graph operators, at each fixed positive inner order. -/
theorem fullTaylor_coeff_succ (r n : ℕ) (p q : MvPolynomial (Fin d) k) (m : Fin d →₀ ℕ) :
    MvPolynomial.coeff m (LaurentModule.coeff (X := Deformation.Binary k (MvPolynomial (Fin d) k))
      (PowerSeriesModule.coeffV r (fullTaylor D s w)) (n + 1 : ℕ) p q) =
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) r,
        MvPolynomial.coeff m
          (weightedOperator (s n) (w n) (fun v ↦ PoissonMCFamily.coeffTable D (a v)) p q) := by
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  rw [fullTaylor, coeff_laurentScaledMCEvaluation_nat,
    PowerSeriesModule.coeffV_applyMultilinear]
  change MvPolynomial.coeff m
    ((∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) r,
      GraphTaylorCoefficients.effectiveFamily s w (n + 1)
        (fun v ↦ PowerSeriesModule.coeffV (a v) (PoissonMCFamily.poissonSeries D))) p q) = _
  simp only [LinearMap.sum_apply, MvPolynomial.coeff_sum,
    PoissonMCFamily.poissonSeries_coeff, effectiveFamily_bivectorCoefficients]
  congr 1
  ext a
  simp only [Finset.mem_piAntidiag]

omit [CharZero k] in
/-- The actual completed Taylor output equals the actual graph product in fixed
monomial coordinates. The equality is proved by both genuine parameter coefficients. -/
theorem coordinateFullTaylor_eq_graphFamily :
    coordinateFullTaylor D s w = graphFamily D s w := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  obtain ⟨p, rfl⟩ := (coordinateEquiv (k := k) (d := d)).surjective a
  obtain ⟨q, rfl⟩ := (coordinateEquiv (k := k) (d := d)).surjective b
  apply Finsupp.ext
  intro m
  rw [coordinateFullTaylor, PowerSeriesModule.coeffV_map, LaurentModule.coeff_map,
    LinearEquiv.coe_coe,
    binaryCoordinates_apply]
  cases j with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    cases n with
    | zero =>
      simp only [Nat.cast_zero]
      rw [fullTaylor_coeff_zero, graphFamily_coeff_zero]
    | succ n =>
      rw [fullTaylor_coeff_succ, graphFamily_coeff_succ,
        Deformation.GraphPolynomialCoefficients.coeff_weightedOperator]
      rfl
  | negSucc n =>
    rw [fullTaylor, coeff_laurentScaledMCEvaluation_neg _ _ _ _ (Int.negSucc_lt_zero n),
      graphFamily, CompletedGraphProduct.completedProduct_coeff,
      CompletedGraphProduct.coefficientBinary_eq_zero_of_neg _ _ _ _ _ (Int.negSucc_lt_zero n)]
    rfl

/-- Transport the actual completed coordinate product back to the native polynomial cochains. -/
def nativeGraphFamily : PowerSeriesModule (LaurentSeries k)
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k))) :=
  PowerSeriesModule.map
    (LaurentModule.map (X := Deformation.Binary k (Coordinates (Fin d) k))
      (Y := Deformation.Binary k (MvPolynomial (Fin d) k)) binaryCoordinates.symm.toLinearMap)
    (graphFamily D s w)

omit [CharZero k] in
/-- The exact native-cochain identification; no equivalence of products is assumed. -/
theorem fullTaylor_eq_nativeGraphFamily : fullTaylor D s w = nativeGraphFamily D s w := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply binaryCoordinates.injective
  have h := congrArg
    (fun B ↦ LaurentModule.coeff (PowerSeriesModule.coeffV r B) j)
    (coordinateFullTaylor_eq_graphFamily D s w)
  rw [coordinateFullTaylor, PowerSeriesModule.coeffV_map, LaurentModule.coeff_map] at h
  rw [nativeGraphFamily, PowerSeriesModule.coeffV_map, LaurentModule.coeff_map,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact h

/-- The actual positive outer perturbation before multiplying by the inner parameter. -/
def perturbation : PowerSeriesModule k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2) :=
  PoissonMCFamily.poissonSeries D -
    PowerSeriesModule.single (k := k)
      (V := Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
      0 (PoissonMCFamily.constantBivector D)

omit [CharZero k] in
theorem perturbation_zero : PowerSeriesModule.coeffV 0 (perturbation D) = 0 := by
  change PowerSeriesModule.coefficient (k := k)
    (V := Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2) 0 (_ - _) = 0
  rw [map_sub]
  simp [PowerSeriesModule.coefficient, PoissonMCFamily.poissonSeries,
    PoissonMCFamily.constantBivector]

omit [CharZero k] in
theorem constant_add_perturbation :
    PowerSeriesModule.single (k := k)
      (V := Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
      0 (PoissonMCFamily.constantBivector D) + perturbation D =
      PoissonMCFamily.poissonSeries D := by
  unfold perturbation
  abel

/-- The source used in the genuine Laurent Taylor evaluation is the actual
native twisted Rees Maurer--Cartan perturbation. -/
theorem laurentScaledInput_eq_perturbationSeries :
    laurentScaledInput (perturbation D) = PoissonMCFamily.perturbationSeries D := by
  apply PowerSeriesModule.ext (k := LaurentSeries k)
    (V := LaurentModule k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2))
  intro r
  rw [coeff_laurentScaledInput, PoissonMCFamily.perturbationSeries_coeff]
  simp only [perturbation, PowerSeriesModule.coeffV_sub, PoissonMCFamily.poissonSeries,
    PowerSeriesModule.coeffV_mk, PowerSeriesModule.coeffV_single]

/-- The exact twisted Taylor identity with the actual completed graph product.
Both the full product identification and the source perturbation identification
are proved, so neither is an assumed compatibility field. -/
theorem taylorApply_eq_graph_difference :
    taylorApply (k := LaurentSeries k)
        (V := LaurentModule k (Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2))
        (W := LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))
        (laurentPlacementTaylorFamily (GraphTaylorCoefficients.effectiveFamily s w)
          (PoissonMCFamily.constantBivector D))
        (PoissonMCFamily.perturbationSeries D) =
      nativeGraphFamily D s w -
        PowerSeriesModule.single (k := LaurentSeries k) 0
          (V := LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))
          (PowerSeriesModule.coeffV 0 (nativeGraphFamily D s w)) := by
  have h := laurent_taylorApply_eq_full_sub_constant
    (V := Deformation.Multiderivation k (MvPolynomial (Fin d) k) 2)
    (W := Deformation.Binary k (MvPolynomial (Fin d) k))
    (GraphTaylorCoefficients.effectiveFamily s w) (PoissonMCFamily.constantBivector D)
    (perturbation D) (perturbation_zero D)
  rw [laurentScaledInput_eq_perturbationSeries, constant_add_perturbation] at h
  change taylorApply _ _ = fullTaylor D s w - PowerSeriesModule.single (k := LaurentSeries k) 0
    (V := LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))
    (PowerSeriesModule.coeffV 0 (fullTaylor D s w)) at h
  rw [fullTaylor_eq_nativeGraphFamily] at h
  exact h

end EnvelopingIsomorphism.Rees.GraphTaylorIdentification
