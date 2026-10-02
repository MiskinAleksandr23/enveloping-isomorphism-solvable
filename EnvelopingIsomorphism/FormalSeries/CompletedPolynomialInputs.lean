import EnvelopingIsomorphism.FormalSeries.CompletedOperatorAction
import EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators
import EnvelopingIsomorphism.Rees.LaurentPolynomialCoefficients

/-! Finite polynomial inputs in the genuine Laurent-then-power-series completion.
The source has finite coordinate support; the target retains both completion support conditions.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.CompletedPolynomialInputs

open Rees.PolynomialCoefficientOperators
open scoped Rees.LaurentPolynomialCoefficients

variable {k ι : Type*} [Field k]

abbrev Scalars (k : Type*) [Field k] := Polynomial (LaurentSeries k)
abbrev Vectors (ι k : Type*) [Field k] := CompletedOperator.Vectors k (Coordinates ι k)

/-- Polynomial scalars act through the inclusion in outer power series. -/
scoped instance polynomialModule : Module (Scalars k) (Vectors ι k) :=
  Module.compHom _ Polynomial.coeToPowerSeries.ringHom

open scoped CompletedPolynomialInputs

@[simp] theorem polynomial_smul (s : Scalars k) (x : Vectors ι k) :
    s • x = (s : PowerSeries (LaurentSeries k)) • x := rfl

/-- Coordinates are constant in both formal parameters. -/
abbrev constant (a : Coordinates ι k) : Vectors ι k := CompletedOperator.constant a

/-- Include a finite polynomial by its finite linear combination of coordinate monomials. -/
def embed : MvPolynomial ι (Scalars k) →ₗ[Scalars k] Vectors ι k :=
  (Finsupp.linearCombination (Scalars k) (fun m ↦ constant (Finsupp.single m 1))).comp
    (MvPolynomial.basisMonomials ι (Scalars k)).repr.toLinearMap

@[simp] theorem embed_monomial (m : ι →₀ ℕ) (c : Scalars k) :
    embed (MvPolynomial.monomial m c) = c • constant (Finsupp.single m 1) := by
  change Finsupp.linearCombination (Scalars k) _ (Finsupp.single m c) = _
  exact Finsupp.linearCombination_single _ _ _

theorem embed_eq_sum (p : MvPolynomial ι (Scalars k)) :
    embed p = ∑ m ∈ p.support, MvPolynomial.coeff m p • constant (Finsupp.single m 1) := rfl

theorem coeff_series_smul_constant {A : Type*} [AddCommGroup A] [Module k A]
    (s : LaurentSeries k) (a : A) (j : ℤ) :
    LaurentModule.coeff (s • LaurentModule.single (k := k) 0 a) j = s.coeff j • a := by
  classical
  change ((HahnModule.of k).symm (s • HahnModule.of k (HahnSeries.single 0 a))).coeff j = _
  rw [HahnModule.coeff_smul_right (R := k) (x := s)
    (y := HahnModule.of k (HahnSeries.single 0 a)) (Set.isPWO_singleton (0 : ℤ))
    HahnSeries.support_single_subset]
  rw [Finset.sum_eq_single (j, 0)]
  · simp
  · intro ij hij hne
    have hh := Finset.mem_vaddAntidiagonal _ _ |>.mp hij
    have hz : ij.2 = 0 := hh.2.1
    have hj : ij.1 = j := by simpa [hz] using hh.2.2
    exact (hne (Prod.ext hj hz)).elim
  · intro h
    have hs : s.coeff j = 0 := by
      by_contra hs
      apply h
      simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, Set.mem_singleton_iff,
        vadd_eq_add, add_zero, and_self, and_true]
      exact hs
    simp [hs]

theorem coeffV_series_smul_constant {E A : Type*} [CommRing E]
    [AddCommGroup A] [Module E A] (s : PowerSeries E) (a : A) (r : ℕ) :
    PowerSeriesModule.coeffV r (s • PowerSeriesModule.single (k := E) 0 a) =
      PowerSeries.coeff r s • a := by
  rw [PowerSeriesModule.coeffV_series_smul, Finset.sum_eq_single (r, 0)]
  · simp
  · intro ij hij hne
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hz : ij.2 ≠ 0 := by
      intro hz
      exact hne (Prod.ext (by simpa [hz] using hs) hz)
    simp [hz]
  · simp

theorem coeff_laurent_sum {A I : Type*} [AddCommGroup A] [Module k A]
    (s : Finset I) (f : I → LaurentModule k A) (j : ℤ) :
    LaurentModule.coeff (∑ i ∈ s, f i) j = ∑ i ∈ s, LaurentModule.coeff (f i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- Every coefficient can be read directly from the finite polynomial input. -/
theorem coeff_embed (p : MvPolynomial ι (Scalars k)) (r : ℕ) (j : ℤ) (m : ι →₀ ℕ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r (embed p)) j m =
      ((MvPolynomial.coeff m p).coeff r).coeff j := by
  classical
  rw [embed_eq_sum]
  simp only [PowerSeriesModule.coeffV_sum, polynomial_smul, constant,
    CompletedOperator.constant, coeffV_series_smul_constant, Polynomial.coeff_coe]
  rw [coeff_laurent_sum]
  simp only [coeff_series_smul_constant, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single m]
  · simp
  · intro a ha hne
    simp [hne]
  · intro hm
    have hz : MvPolynomial.coeff m p = 0 := MvPolynomial.notMem_support_iff.mp hm
    simp [hz]

theorem embed_injective : Function.Injective (embed (k := k) (ι := ι)) := by
  intro p q h
  apply MvPolynomial.ext
  intro m
  apply Polynomial.ext
  intro r
  apply HahnSeries.ext
  funext j
  simpa only [coeff_embed] using congrArg
    (fun x : Vectors ι k ↦ LaurentModule.coeff (PowerSeriesModule.coeffV r x) j m) h

@[simp] theorem coeff_includePolynomial (a : Coordinates ι k) (m : ι →₀ ℕ) :
    MvPolynomial.coeff m (includePolynomial (S := Scalars k) a) =
      algebraMap k (Scalars k) (a m) := by
  change MvPolynomial.coeff m (MvPolynomial.map (algebraMap k (Scalars k))
    ((MvPolynomial.basisMonomials ι k).repr.symm a)) = _
  rw [MvPolynomial.coeff_map]
  rfl

@[simp] theorem embed_includePolynomial (a : Coordinates ι k) :
    embed (includePolynomial (S := Scalars k) a) = constant a := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply Finsupp.ext
  intro m
  rw [coeff_embed, coeff_includePolynomial]
  change ((Polynomial.C (algebraMap k (LaurentSeries k) (a m))).coeff r).coeff j = _
  have hc : algebraMap k (LaurentSeries k) (a m) = HahnSeries.C (a m) := by
    simp [HahnSeries.algebraMap_apply']
  rw [hc]
  by_cases hr : r = 0 <;> by_cases hj : j = 0 <;>
    simp [constant, CompletedOperator.constant, Polynomial.coeff_C, hr, hj,
      HahnSeries.C_apply]

/-- A linear map over complete scalars agrees on every finite polynomial input
once it agrees on the original coordinate space. -/
theorem linear_extension
    (F : Vectors ι k →ₗ[PowerSeries (LaurentSeries k)] Vectors ι k)
    (f : MvPolynomial ι (Scalars k) →ₗ[Scalars k] MvPolynomial ι (Scalars k))
    (h : ∀ a, F (constant a) = embed (f (includePolynomial (S := Scalars k) a)))
    (p : MvPolynomial ι (Scalars k)) : F (embed p) = embed (f p) := by
  classical
  rw [embed_eq_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomial_smul, map_smul, h, includePolynomial_single]
  have hm : MvPolynomial.monomial m (MvPolynomial.coeff m p) =
      MvPolynomial.coeff m p • MvPolynomial.monomial m (1 : Scalars k) := by
    simp [MvPolynomial.smul_monomial]
  rw [hm, map_smul, map_smul, polynomial_smul]

/-- The analogous finite-input extension statement for bilinear operations. -/
theorem bilinear_extension
    (B : Vectors ι k →ₗ[PowerSeries (LaurentSeries k)]
      Vectors ι k →ₗ[PowerSeries (LaurentSeries k)] Vectors ι k)
    (b : MvPolynomial ι (Scalars k) →ₗ[Scalars k]
      MvPolynomial ι (Scalars k) →ₗ[Scalars k] MvPolynomial ι (Scalars k))
    (h : ∀ a c, B (constant a) (constant c) =
      embed (b (includePolynomial (S := Scalars k) a) (includePolynomial (S := Scalars k) c)))
    (p q : MvPolynomial ι (Scalars k)) : B (embed p) (embed q) = embed (b p q) := by
  classical
  rw [embed_eq_sum p, map_sum, LinearMap.sum_apply]
  conv_rhs => rw [p.as_sum, map_sum, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomial_smul, map_smul, LinearMap.smul_apply]
  have hq := linear_extension (B (constant (Finsupp.single m 1)))
    (b (MvPolynomial.monomial m 1)) (fun c ↦ by simpa using h (Finsupp.single m 1) c) q
  rw [hq]
  have hm : MvPolynomial.monomial m (MvPolynomial.coeff m p) =
      MvPolynomial.coeff m p • MvPolynomial.monomial m (1 : Scalars k) := by
    simp [MvPolynomial.smul_monomial]
  rw [hm, map_smul, LinearMap.smul_apply, map_smul, polynomial_smul]

end EnvelopingIsomorphism.FormalSeries.CompletedPolynomialInputs
