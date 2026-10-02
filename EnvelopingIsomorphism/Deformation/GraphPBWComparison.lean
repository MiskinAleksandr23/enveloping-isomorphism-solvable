import EnvelopingIsomorphism.Deformation.PolynomialGraphProduct
import EnvelopingIsomorphism.Deformation.GraphLinearParameters
import EnvelopingIsomorphism.Enveloping.Injective
import Mathlib.Algebra.Algebra.Rat
import EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators
import EnvelopingIsomorphism.Rees.SymmetricPBWProduct
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LaurentSeries

/-!
# The canonical symmetrized graph comparison

The graph-averaging map is polynomial-valued and independent of any source
Lie presentation. With genuine graph product laws and matching Lie generators,
it is the composite of native PBW symmetrization and the canonical graph UEA
equivalence, so its inverse exists by proved triangularity.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph

open scoped BigOperators
open MvPolynomial
open EnvelopingIsomorphism.PBW

variable {R : Type*} [CommRing R] [Algebra ℚ R] {d : ℕ}
  (s : (j : ℕ) → Finset (KontsevichGraph (j + 1)))
  (w : (j : ℕ) → KontsevichGraph (j + 1) → R)
  (c : Fin d → Fin d → Fin d → R)

/-- The right-associated product of a list under the actual graph operation.
It is defined even before the analytical product laws are supplied. -/
def graphWord : List (Polynomial d R) → Polynomial d R
  | [] => 1
  | p :: ps => polynomialProduct s w c p (graphWord ps)

omit [Algebra ℚ R] in
@[simp] theorem graphWord_nil : graphWord s w c [] = 1 := rfl
omit [Algebra ℚ R] in
@[simp] theorem graphWord_cons (p : Polynomial d R) (ps : List (Polynomial d R)) :
    graphWord s w c (p :: ps) = polynomialProduct s w c p (graphWord s w c ps) := rfl

/-- The actual permutation average of graph products of coordinate generators. -/
def averagedCoordinateWord (v : List (Fin d)) : Polynomial d R :=
  inverseFactorial R v.length • ∑ σ : Equiv.Perm (Fin v.length),
    graphWord s w c (List.ofFn ((fun i ↦ X (v.get i)) ∘ σ))

/-- The intrinsic polynomial graph comparison map, given by actual averaging
on the ordinary monomial basis. -/
def comparisonMap : Polynomial d R →ₗ[R] Polynomial d R :=
  (MvPolynomial.basisMonomials (Fin d) R).constr R
    (fun m ↦ averagedCoordinateWord s w c (orderedWord m))

@[simp] theorem comparisonMap_monomial (m : Fin d →₀ ℕ) (r : R) :
    comparisonMap s w c (monomial m r) = r • averagedCoordinateWord s w c (orderedWord m) := by
  have hm : (monomial m r : Polynomial d R) = r • monomial m 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  congr 1
  exact (MvPolynomial.basisMonomials (Fin d) R).constr_basis R _ m

section ComparisonEquivalence

variable [Nontrivial R] (laws : ProductLaws s w c)

omit [Algebra ℚ R] in
theorem toPolynomial_list_prod (ps : List (ProductAlgebra s w c laws)) :
    toPolynomial s w c laws ps.prod =
      graphWord s w c (ps.map (toPolynomial s w c laws)) := by
  induction ps with
  | nil => exact toPolynomial_one s w c laws
  | cons p ps ih =>
      rw [List.prod_cons, toPolynomial_mul, ih]
      rfl

theorem toPolynomial_averagedProduct (n : ℕ) (v : Fin n → ProductAlgebra s w c laws) :
    toPolynomial s w c laws (averagedProduct R (ProductAlgebra s w c laws) n v) =
      inverseFactorial R n • ∑ σ : Equiv.Perm (Fin n),
        graphWord s w c (List.ofFn ((toPolynomial s w c laws ∘ v) ∘ σ)) := by
  rw [averagedProduct_apply, map_smul, map_sum]
  simp only [toPolynomial_list_prod, List.map_ofFn, Function.comp_assoc]

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra R L]
  (b : Module.Basis (Fin d) R L) (g : L →ₗ⁅R⁆ ProductAlgebra s w c laws)
  (hgen : ∀ i, toPolynomial s w c laws (g (b i)) = X i)

/-- Direction: ordinary PBW coordinates to graph-product coordinates.
The inverse is part of the proved native linear equivalence. -/
def comparisonEquiv : Polynomial d R ≃ₗ[R] Polynomial d R :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv |>.trans
    (symmetrizationEquiv b) |>.trans
    (envelopingEquiv s w c laws b g hgen).toLinearEquiv |>.trans
    (toPolynomial s w c laws)

theorem comparisonEquiv_monomial (m : Fin d →₀ ℕ) :
    comparisonEquiv s w c laws b g hgen (monomial m 1) =
      averagedCoordinateWord s w c (orderedWord m) := by
  have hm : (SymmetricAlgebra.equivMvPolynomial b).symm (monomial m 1) =
      b.symmetricAlgebra m := rfl
  change toPolynomial s w c laws
    (envelopingEquiv s w c laws b g hgen
      (symmetrizationEquiv b ((SymmetricAlgebra.equivMvPolynomial b).symm (monomial m 1)))) = _
  rw [hm, symmetrizationEquiv_apply, symmetrization_basis, averagedWord_map]
  change toPolynomial s w c laws
    ((envelopingEquiv s w c laws b g hgen).toAlgHom
      (averagedProduct R (UniversalEnvelopingAlgebra R L) (orderedWord m).length
        ((UniversalEnvelopingAlgebra.ι R ∘ b) ∘ (orderedWord m).get))) = _
  rw [EnvelopingIsomorphism.Enveloping.averagedProduct_map, toPolynomial_averagedProduct]
  unfold averagedCoordinateWord
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply congrArg List.ofFn
  funext i
  exact envelopingEquiv_ι_basis s w c laws b g hgen ((orderedWord m).get (σ i))

/-- The comparison depends only on the graph formula, not on the source Lie
presentation used to prove its invertibility. -/
theorem comparisonEquiv_toLinearMap :
    (comparisonEquiv s w c laws b g hgen).toLinearMap = comparisonMap s w c := by
  apply (MvPolynomial.basisMonomials (Fin d) R).ext
  intro m
  change comparisonEquiv s w c laws b g hgen (monomial m 1) =
    comparisonMap s w c (monomial m 1)
  rw [comparisonEquiv_monomial, comparisonMap_monomial, one_smul]

theorem comparisonEquiv_apply (p : Polynomial d R) :
    comparisonEquiv s w c laws b g hgen p = comparisonMap s w c p :=
  LinearMap.congr_fun (comparisonEquiv_toLinearMap s w c laws b g hgen) p

theorem comparisonEquiv_apply_symPolynomialEquiv (p : Polynomial d R) :
    comparisonEquiv s w c laws b g hgen p = toPolynomial s w c laws
      (envelopingEquiv s w c laws b g hgen (EnvelopingIsomorphism.Rees.Homogenization.symPolynomialEquiv b p)) := rfl

/-- The genuine finite PBW multiplication is intertwined with the genuine
polynomial graph multiplication by the canonical comparison. -/
theorem comparisonEquiv_symProduct (p q : Polynomial d R) :
    comparisonEquiv s w c laws b g hgen (EnvelopingIsomorphism.Rees.SymmetricPBWProduct.symProduct b p q) =
      polynomialProduct s w c (comparisonEquiv s w c laws b g hgen p)
        (comparisonEquiv s w c laws b g hgen q) := by
  simp only [comparisonEquiv_apply_symPolynomialEquiv,
    EnvelopingIsomorphism.Rees.SymmetricPBWProduct.symPolynomialEquiv_product,
    map_mul, toPolynomial_mul]

include laws g hgen in
theorem comparisonMap_symProduct (p q : Polynomial d R) :
    comparisonMap s w c (EnvelopingIsomorphism.Rees.SymmetricPBWProduct.symProduct b p q) =
      polynomialProduct s w c (comparisonMap s w c p) (comparisonMap s w c q) := by
  simpa only [comparisonEquiv_apply] using comparisonEquiv_symProduct s w c laws b g hgen p q

/-- On a product of arbitrary linear vectors, the comparison is the actual
permutation average of their graph products. -/
theorem comparisonEquiv_product (n : ℕ) (v : Fin n → L) :
    comparisonEquiv s w c laws b g hgen
      ((SymmetricAlgebra.equivMvPolynomial b)
        ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (v i))).prod)) =
      inverseFactorial R n • ∑ σ : Equiv.Perm (Fin n),
        graphWord s w c
          (List.ofFn (fun i ↦ toPolynomial s w c laws (g (v (σ i))))) := by
  change toPolynomial s w c laws
    (envelopingEquiv s w c laws b g hgen
      (symmetrizationEquiv b ((SymmetricAlgebra.equivMvPolynomial b).symm
        ((SymmetricAlgebra.equivMvPolynomial b)
          ((List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (v i))).prod))))) = _
  rw [AlgEquiv.symm_apply_apply, symmetrizationEquiv_apply, symmetrization_prod]
  change toPolynomial s w c laws
    ((envelopingEquiv s w c laws b g hgen).toAlgHom
      (averagedProduct R (UniversalEnvelopingAlgebra R L) n
        (fun i ↦ UniversalEnvelopingAlgebra.ι R (v i)))) = _
  rw [EnvelopingIsomorphism.Enveloping.averagedProduct_map, toPolynomial_averagedProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply congrArg List.ofFn
  funext i
  exact congrArg (toPolynomial s w c laws) (envelopingEquiv_ι s w c laws b g hgen (v (σ i)))

@[simp] theorem comparisonEquiv_X (i : Fin d) :
    comparisonEquiv s w c laws b g hgen (X i) = X i := by
  have hi : (SymmetricAlgebra.equivMvPolynomial b).symm (X i) = SymmetricAlgebra.ι R L (b i) := by
    apply (SymmetricAlgebra.equivMvPolynomial b).injective
    simp
  change toPolynomial s w c laws
    (envelopingEquiv s w c laws b g hgen
      (symmetrizationEquiv b ((SymmetricAlgebra.equivMvPolynomial b).symm (X i)))) = X i
  rw [hi, symmetrizationEquiv_ι, envelopingEquiv_ι_basis]

@[simp] theorem comparisonEquiv_symm_X (i : Fin d) :
    (comparisonEquiv s w c laws b g hgen).symm (X i) = X i := by
  apply (comparisonEquiv s w c laws b g hgen).injective
  rw [LinearEquiv.apply_symm_apply, comparisonEquiv_X]

end ComparisonEquivalence

section ScalarNaturality

variable {S : Type*} [CommRing S] [Algebra ℚ S] [Nontrivial S] (φ : R →+* S)

omit [Algebra ℚ R] [Algebra ℚ S] in
theorem map_graphWord (ps : List (Polynomial d R)) :
    MvPolynomial.map φ (graphWord s w c ps) =
      graphWord s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r))
        (ps.map (MvPolynomial.map φ)) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [graphWord_cons, map_polynomialProduct, ih]
      rfl

omit [Nontrivial S] in
theorem map_inverseFactorial (n : ℕ) : φ (inverseFactorial R n) = inverseFactorial S n :=
  φ.map_rat_algebraMap _

theorem map_averagedCoordinateWord (v : List (Fin d)) :
    MvPolynomial.map φ (averagedCoordinateWord s w c v) =
      averagedCoordinateWord s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r)) v := by
  simp only [averagedCoordinateWord, MvPolynomial.smul_eq_C_mul, map_mul,
    map_inverseFactorial, map_sum, map_graphWord, List.map_ofFn, Function.comp_def,
    MvPolynomial.map_X]

/-- The intrinsic comparison specializes by the same graph formula even if
specialization decreases the degrees of its coefficients or inputs. -/
theorem map_comparisonMap (p : Polynomial d R) :
    MvPolynomial.map φ (comparisonMap s w c p) =
      comparisonMap s (fun j Γ ↦ φ (w j Γ)) (fun i j r ↦ φ (c i j r)) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
      rw [comparisonMap_monomial, MvPolynomial.map_monomial, comparisonMap_monomial]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_averagedCoordinateWord]
  | add p q hp hq => simp only [map_add, hp, hq]

end ScalarNaturality

omit [Algebra ℚ R] in
theorem polynomialProduct_zero_coefficients (f g : Polynomial d R) :
    polynomialProduct s w (fun _ _ _ ↦ 0) f g = f * g := by
  apply sub_eq_zero.mp
  rw [polynomialProduct, finiteStarOperator_sub_mul]
  apply Finset.sum_eq_zero
  intro j _
  exact weightedOperator_zero_coefficients (s j) (w j) (Nat.succ_pos j) f g

omit [Algebra ℚ R] in
theorem graphWord_zero_coefficients (ps : List (Polynomial d R)) :
    graphWord s w (fun _ _ _ ↦ 0) ps = ps.prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [graphWord_cons, polynomialProduct_zero_coefficients, ih, List.prod_cons]

omit [Algebra ℚ R] in
theorem prod_X_wordIndex (v : List (Fin d)) :
    (v.map (X : Fin d → Polynomial d R)).prod = monomial (wordIndex v) 1 := by
  induction v with
  | nil => simp
  | cons i v ih =>
      simp only [List.map_cons, List.prod_cons, ih, wordIndex_cons, MvPolynomial.X,
        monomial_mul, one_mul]

theorem averagedCoordinateWord_zero_coefficients (v : List (Fin d)) :
    averagedCoordinateWord s w (fun _ _ _ ↦ 0) v = (v.map X).prod := by
  unfold averagedCoordinateWord
  simp only [graphWord_zero_coefficients]
  have hp (σ : Equiv.Perm (Fin v.length)) :
      (List.ofFn ((fun i ↦ (X (v.get i) : Polynomial d R)) ∘ σ)).prod = (v.map X).prod := by
    have h := (σ.ofFn_comp_perm (fun i ↦ (X (v.get i) : Polynomial d R))).prod_eq
    have heq : List.ofFn ((X : Fin d → Polynomial d R) ∘ v.get) = v.map X := by
      rw [← List.map_ofFn, List.ofFn_get]
    exact h.trans (congrArg List.prod heq)
  simp_rw [hp]
  exact inverseFactorial_smul_sum_const R v.length _

/-- At the zero Poisson tensor the actual graph comparison is exactly the identity. -/
theorem comparisonMap_zero_coefficients :
    comparisonMap (d := d) s w (fun _ _ _ ↦ 0) = LinearMap.id := by
  apply (MvPolynomial.basisMonomials (Fin d) R).ext
  intro m
  change comparisonMap s w (fun _ _ _ ↦ 0) (monomial m 1) = monomial m 1
  rw [comparisonMap_monomial, one_smul, averagedCoordinateWord_zero_coefficients,
    prod_X_wordIndex, wordIndex_orderedWord]

section Specialization

variable {S : Type*} [CommRing S] [Algebra ℚ S] [Nontrivial S] (φ : R →+* S)

/-- Vanishing of the specialized bivector gives identity specialization of `J`. -/
theorem map_comparisonMap_of_coefficients_zero
    (hc : ∀ i j r, φ (c i j r) = 0) (p : Polynomial d R) :
    MvPolynomial.map φ (comparisonMap s w c p) = MvPolynomial.map φ p := by
  rw [map_comparisonMap]
  have hzero : (fun i j r ↦ φ (c i j r)) = fun _ _ _ ↦ 0 := by
    funext i j r
    exact hc i j r
  rw [hzero, comparisonMap_zero_coefficients, LinearMap.id_apply]

/-- The same specialized graph tensor produces the same specialized comparison.
This is the exact `J_L(0) = J_M(0)` statement after identifying their coordinates. -/
theorem map_comparisonMap_eq_of_coefficients_eq
    (c' : Fin d → Fin d → Fin d → R) (hc : ∀ i j r, φ (c i j r) = φ (c' i j r))
    (p : Polynomial d R) :
    MvPolynomial.map φ (comparisonMap s w c p) = MvPolynomial.map φ (comparisonMap s w c' p) := by
  have hc' : (fun i j r ↦ φ (c i j r)) = fun i j r ↦ φ (c' i j r) := by
    funext i j r
    exact hc i j r
  rw [map_comparisonMap, map_comparisonMap, hc']

end Specialization

section EquivalenceSpecialization

attribute [local instance 100] LieRing.ofAssociativeRing

variable [Nontrivial R] (laws : ProductLaws s w c)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  (b : Module.Basis (Fin d) R L) (g : L →ₗ⁅R⁆ ProductAlgebra s w c laws)
  (hgen : ∀ i, toPolynomial s w c laws (g (b i)) = X i)
  {S : Type*} [CommRing S] [Algebra ℚ S] [Nontrivial S]
  (φ : R →+* S) (hc : ∀ i j r, φ (c i j r) = 0)

include hc

theorem map_comparisonEquiv_of_coefficients_zero (p : Polynomial d R) :
    MvPolynomial.map φ (comparisonEquiv s w c laws b g hgen p) = MvPolynomial.map φ p := by
  rw [comparisonEquiv_apply]
  exact map_comparisonMap_of_coefficients_zero s w c φ hc p

/-- The actual polynomial inverse has the same identity specialization. -/
theorem map_comparisonEquiv_symm_of_coefficients_zero (p : Polynomial d R) :
    MvPolynomial.map φ ((comparisonEquiv s w c laws b g hgen).symm p) = MvPolynomial.map φ p := by
  have h := map_comparisonEquiv_of_coefficients_zero s w c laws b g hgen φ hc
    ((comparisonEquiv s w c laws b g hgen).symm p)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end EquivalenceSpecialization

section PolynomialParameter

variable {k : Type*} [CommRing k] [Algebra ℚ k] [Nontrivial k]
  (wH : (j : ℕ) → KontsevichGraph (j + 1) → _root_.Polynomial k)
  (cH : Fin d → Fin d → Fin d → _root_.Polynomial k)

/-- For a tensor multiplied by the actual polynomial parameter, specialization
at zero makes the canonical comparison exactly the identity. -/
theorem eval_zero_comparisonMap (p : Polynomial d (_root_.Polynomial k)) :
    MvPolynomial.map (_root_.Polynomial.evalRingHom (0 : k))
        (comparisonMap s wH (fun i j r ↦ _root_.Polynomial.X * cH i j r) p) =
      MvPolynomial.map (_root_.Polynomial.evalRingHom (0 : k)) p := by
  apply map_comparisonMap_of_coefficients_zero
  intro i j r
  simp

/-- Coefficient extraction of the actual polynomial comparison gives an
endomorphism-valued power series. Its exponents are nonnegative by construction;
no Laurent completion of the polynomial function space is substituted here. -/
def comparisonSeries : PowerSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k)) :=
  PowerSeries.mk fun n ↦
    EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator
      (_root_.Polynomial.lcoeff k n)
      (comparisonMap s wH (fun i j r ↦ _root_.Polynomial.X * cH i j r))

omit [Nontrivial k] in
theorem comparisonSeries_coefficient (n : ℕ)
    (p : EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k)
    (m : Fin d →₀ ℕ) :
    PowerSeries.coeff n (comparisonSeries s wH cH) p m =
      (MvPolynomial.coeff m
        (comparisonMap s wH (fun i j r ↦ _root_.Polynomial.X * cH i j r)
          (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.includePolynomial
            (S := _root_.Polynomial k) p))).coeff n := by
  rw [comparisonSeries, PowerSeries.coeff_mk]
  rfl

/-- The genuine operator series is congruent to the identity modulo the
parameter, before any analytical associativity hypothesis is used. -/
theorem comparisonSeries_constantCoeff : PowerSeries.constantCoeff (comparisonSeries s wH cH) = 1 := by
  rw [comparisonSeries, PowerSeries.constantCoeff_mk]
  apply EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coordinate_end_ext
  intro a m
  rw [EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator_single]
  change (MvPolynomial.coeff m
    (comparisonMap s wH (fun i j r ↦ _root_.Polynomial.X * cH i j r) (monomial a 1))).coeff 0 =
      Finsupp.single a (1 : k) m
  have h := congrArg (MvPolynomial.coeff m) (eval_zero_comparisonMap s wH cH (monomial a 1))
  simpa only [MvPolynomial.coeff_map, _root_.Polynomial.coe_evalRingHom,
    ← _root_.Polynomial.coeff_zero_eq_eval_zero, MvPolynomial.coeff_monomial,
    apply_ite, map_one, map_zero, Finsupp.single_apply] using h

theorem comparisonSeries_isUnit : IsUnit (comparisonSeries s wH cH) := by
  apply (PowerSeries.isUnit_iff_constantCoeff (φ := comparisonSeries s wH cH)).mpr
  rw [comparisonSeries_constantCoeff]
  exact isUnit_one

/-- The actual polynomial comparison, bundled as a unit in nonnegative
parameter-series of endomorphisms. -/
def comparisonSeriesUnit : (PowerSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k)))ˣ :=
  (comparisonSeries_isUnit s wH cH).unit

@[simp] theorem comparisonSeriesUnit_val : (comparisonSeriesUnit s wH cH).val =
    comparisonSeries s wH cH := IsUnit.unit_spec _

end PolynomialParameter

section TwoParameters

variable {k : Type*} [CommRing k] [Algebra ℚ k] [Nontrivial k]
  (wTH : (j : ℕ) → KontsevichGraph (j + 1) → _root_.Polynomial (_root_.Polynomial k))
  (cTH : Fin d → Fin d → Fin d → _root_.Polynomial (_root_.Polynomial k))

/-- Extract outer `t` degree `r` from inner `h` degree `j` in the actual
coefficient ring `k[t][h]`. -/
def comparisonDoubleCoeff (r j : ℕ) :
    _root_.Polynomial (_root_.Polynomial k) →ₗ[k] k :=
  (_root_.Polynomial.lcoeff k r).comp
    ((_root_.Polynomial.lcoeff (_root_.Polynomial k) j).restrictScalars k)

omit [Algebra ℚ k] [Nontrivial k] in
theorem comparisonDoubleCoeff_apply (r j : ℕ) (p : _root_.Polynomial (_root_.Polynomial k)) :
    comparisonDoubleCoeff (k := k) r j p = (p.coeff j).coeff r := rfl

/-- Actual coefficient operators of the polynomial comparison, arranged with
outer parameter `t` and inner parameter `h`. -/
def comparisonRows : PowerSeries (PowerSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))) :=
  PowerSeries.mk fun r ↦ PowerSeries.mk fun j ↦
    EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator
      (comparisonDoubleCoeff r j)
      (comparisonMap s wTH (fun i j r ↦ _root_.Polynomial.X * cTH i j r))

omit [Nontrivial k] in
theorem comparisonRows_coefficient (r j : ℕ)
    (p : EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k)
    (m : Fin d →₀ ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff r (comparisonRows s wTH cTH)) p m =
      ((MvPolynomial.coeff m
        (comparisonMap s wTH (fun i j r ↦ _root_.Polynomial.X * cTH i j r)
          (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.includePolynomial
            (S := _root_.Polynomial (_root_.Polynomial k)) p))).coeff j).coeff r := by
  rw [comparisonRows, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rfl

/-- The whole `h = 0` operator series is the identity, in every outer `t` degree. -/
theorem comparisonRows_coefficient_h_zero (r : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.coeff r (comparisonRows s wTH cTH)) =
      if r = 0 then 1 else 0 := by
  rw [comparisonRows, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  apply EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coordinate_end_ext
  intro a m
  rw [EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator_single]
  change ((MvPolynomial.coeff m
    (comparisonMap s wTH (fun i j r ↦ _root_.Polynomial.X * cTH i j r) (monomial a 1))).coeff 0).coeff r = _
  have h := congrArg (fun F : Module.End (_root_.Polynomial k)
      (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) (_root_.Polynomial k)) ↦
        F (Finsupp.single a 1) m) (comparisonSeries_constantCoeff s wTH cTH)
  rw [comparisonSeries, PowerSeries.constantCoeff_mk,
    EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator_single] at h
  have h' := congrArg (fun p : _root_.Polynomial k ↦ p.coeff r) h
  by_cases hr : r = 0 <;> by_cases ham : a = m <;>
    simpa [_root_.Polynomial.lcoeff_apply, _root_.Polynomial.coeff_one,
      Finsupp.single_apply, ham, hr] using h'

/-- At `(t,h)=(0,0)` the extracted operator is the identity. -/
theorem comparisonRows_constant_constant :
    PowerSeries.constantCoeff (PowerSeries.constantCoeff (comparisonRows s wTH cTH)) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using
    comparisonRows_coefficient_h_zero s wTH cTH 0

theorem comparisonRows_isUnit : IsUnit (comparisonRows s wTH cTH) := by
  apply (PowerSeries.isUnit_iff_constantCoeff (φ := comparisonRows s wTH cTH)).mpr
  apply (PowerSeries.isUnit_iff_constantCoeff
    (φ := PowerSeries.constantCoeff (comparisonRows s wTH cTH))).mpr
  rw [comparisonRows_constant_constant]
  exact isUnit_one

def comparisonRowsUnit : (PowerSeries (PowerSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))))ˣ :=
  (comparisonRows_isUnit s wTH cTH).unit

@[simp] theorem comparisonRowsUnit_val : (comparisonRowsUnit s wTH cTH).val =
    comparisonRows s wTH cTH := IsUnit.unit_spec _

local instance : Ring (LaurentSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))) :=
  HahnSeries.instRing (Γ := ℤ) (R := Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))

/-- The comparison lives in the genuine completed operator algebra
`End_k(A)((h))[[t]]`, with the original polynomial function space `A`. -/
def comparisonCompleted : PowerSeries (LaurentSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))) :=
  PowerSeries.map (HahnSeries.ofPowerSeries ℤ _) (comparisonRows s wTH cTH)

omit [Nontrivial k] in
/-- Every outer coefficient has nonnegative `h` exponents. -/
theorem comparisonCompleted_coefficient_neg (r : ℕ) (j : ℤ) (hj : j < 0) :
    (PowerSeries.coeff r (comparisonCompleted s wTH cTH)).coeff j = 0 := by
  rw [comparisonCompleted, PowerSeries.coeff_map]
  simpa only [if_pos hj] using
    (PowerSeries.coeff_coe (PowerSeries.coeff r (comparisonRows s wTH cTH)) j)

omit [Nontrivial k] in
theorem comparisonCompleted_coefficient_nat (r j : ℕ) :
    (PowerSeries.coeff r (comparisonCompleted s wTH cTH)).coeff (j : ℤ) =
      PowerSeries.coeff j (PowerSeries.coeff r (comparisonRows s wTH cTH)) := by
  rw [comparisonCompleted, PowerSeries.coeff_map]
  exact LaurentSeries.coeff_coe_powerSeries _ _

theorem comparisonCompleted_coefficient_h_zero (r : ℕ) :
    (PowerSeries.coeff r (comparisonCompleted s wTH cTH)).coeff 0 = if r = 0 then 1 else 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, comparisonCompleted_coefficient_nat,
    comparisonRows_coefficient_h_zero]

theorem comparisonCompleted_isUnit : IsUnit (comparisonCompleted s wTH cTH) := by
  exact (comparisonRows_isUnit s wTH cTH).map (PowerSeries.map (HahnSeries.ofPowerSeries ℤ _))

/-- A genuine unit in `End_k(A)((h))[[t]]`, extracted from the actual polynomial `J`. -/
def comparisonCompletedUnit : (PowerSeries (LaurentSeries (Module.End k
    (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k))))ˣ :=
  Units.map (PowerSeries.map (HahnSeries.ofPowerSeries ℤ _)).toMonoidHom (comparisonRowsUnit s wTH cTH)

@[simp] theorem comparisonCompletedUnit_val : (comparisonCompletedUnit s wTH cTH).val =
    comparisonCompleted s wTH cTH := by
  change PowerSeries.map _ (comparisonRowsUnit s wTH cTH).val = _
  rw [comparisonRowsUnit_val]
  rfl

/-- The inverse unit also has no negative `h` coefficients in any outer row. -/
theorem comparisonCompletedUnit_inv_coefficient_neg (r : ℕ) (j : ℤ) (hj : j < 0) :
    (PowerSeries.coeff r ((comparisonCompletedUnit s wTH cTH)⁻¹).val).coeff j = 0 := by
  change (PowerSeries.coeff r
    (PowerSeries.map (HahnSeries.ofPowerSeries ℤ _) ((comparisonRowsUnit s wTH cTH)⁻¹).val)).coeff j = 0
  rw [PowerSeries.coeff_map]
  simpa only [if_pos hj] using
    (PowerSeries.coeff_coe (PowerSeries.coeff r ((comparisonRowsUnit s wTH cTH)⁻¹).val) j)

/-- Specialize the `t` coefficients while retaining the polynomial variable `h`. -/
def comparisonSpecializeT : _root_.Polynomial (_root_.Polynomial k) →+* _root_.Polynomial k :=
  _root_.Polynomial.mapRingHom (_root_.Polynomial.evalRingHom 0)

omit [Algebra ℚ k] [Nontrivial k] in
theorem coeff_comparisonSpecializeT (p : _root_.Polynomial (_root_.Polynomial k)) (j : ℕ) :
    (comparisonSpecializeT p).coeff j = (p.coeff j).coeff 0 := by
  simp only [comparisonSpecializeT, _root_.Polynomial.coe_mapRingHom,
    _root_.Polynomial.coeff_map, _root_.Polynomial.coe_evalRingHom,
    _root_.Polynomial.coeff_zero_eq_eval_zero]

/-- Equal specialized tensors give identical outer constant rows of the
actual two-parameter operator series. The common row need not be the identity. -/
theorem comparisonRows_constant_eq
    (cTH' : Fin d → Fin d → Fin d → _root_.Polynomial (_root_.Polynomial k))
    (hc : ∀ i j r, comparisonSpecializeT (cTH i j r) = comparisonSpecializeT (cTH' i j r)) :
    PowerSeries.constantCoeff (comparisonRows s wTH cTH) =
      PowerSeries.constantCoeff (comparisonRows s wTH cTH') := by
  simp only [comparisonRows, PowerSeries.constantCoeff_mk]
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_mk]
  apply EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coordinate_end_ext
  intro a m
  rw [EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator_single,
    EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.coefficientOperator_single,
    comparisonDoubleCoeff_apply, comparisonDoubleCoeff_apply]
  have hc' : ∀ i j r, comparisonSpecializeT (_root_.Polynomial.X * cTH i j r) =
      comparisonSpecializeT (_root_.Polynomial.X * cTH' i j r) := by
    intro i j r
    rw [map_mul, map_mul, hc]
  have h := map_comparisonMap_eq_of_coefficients_eq s wTH
    (fun i j r ↦ _root_.Polynomial.X * cTH i j r) (comparisonSpecializeT (k := k))
    (fun i j r ↦ _root_.Polynomial.X * cTH' i j r) hc' (monomial a 1)
  have h' := congrArg (fun p : Polynomial d (_root_.Polynomial k) ↦ (coeff m p).coeff j) h
  simpa only [MvPolynomial.coeff_map, coeff_comparisonSpecializeT] using h'

/-- This is the genuine completed-operator identity `J_L(0,h)=J_M(0,h)`
obtained from the same specialized graph tensor. -/
theorem comparisonCompleted_constant_eq
    (cTH' : Fin d → Fin d → Fin d → _root_.Polynomial (_root_.Polynomial k))
    (hc : ∀ i j r, comparisonSpecializeT (cTH i j r) = comparisonSpecializeT (cTH' i j r)) :
    PowerSeries.constantCoeff (comparisonCompleted s wTH cTH) =
      PowerSeries.constantCoeff (comparisonCompleted s wTH cTH') := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ
    (Module.End k (EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators.Coordinates (Fin d) k)))
      (comparisonRows_constant_eq s wTH cTH cTH' hc)
  simpa only [comparisonCompleted, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map] using h

end TwoParameters

end EnvelopingIsomorphism.Deformation.KontsevichGraph
