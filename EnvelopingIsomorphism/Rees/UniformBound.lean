import EnvelopingIsomorphism.Rees.MarkedIsomorphism
import EnvelopingIsomorphism.Rees.Homogenization
import EnvelopingIsomorphism.Rees.DegreeBound
import EnvelopingIsomorphism.Rees.PolynomialDiagonalBound
import EnvelopingIsomorphism.PBW.SymmetrizationFiltration
import EnvelopingIsomorphism.Rees.LaurentReweight
import EnvelopingIsomorphism.Rees.PolynomialCoefficientOperators

/-!
# The uniform degree bound for the actual Rees comparison

Generator corrections are separated by an auxiliary finite polynomial variable. Evaluating
that variable at the actual central parameter retains the native target enveloping algebra.
This avoids changing its multiplication to a parameter-independent one.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.UniformBound

open Module
open scoped BigOperators

variable {k ι L M : Type*} [Field k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Basis ι k L} {bM : Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- The ordinary PBW filtration in the actual target family over `k[t]`. -/
def ordinary (n : ℕ) : Submodule (Polynomial k) (EnvelopingFamily.U dM) :=
  PBW.weightedUpper (Family.basis dM) (fun _ ↦ 1) n

theorem ordinary_mono : Monotone (ordinary dM) :=
  fun _ _ h ↦ PBW.weightedUpper_mono _ _ h

instance ordinaryGraded : SetLike.GradedMonoid (ordinary dM) where
  one_mem := by
    simpa only [ordinary, PBW.pbwBasis_zero] using
      PBW.pbwBasis_mem_weightedUpper (Family.basis dM) (fun _ ↦ 1)
        (m := 0) (d := 0) (by simp)
  mul_mem {i j} {x y} hx hy :=
    PBW.weightedUpper_mul_le (Family.basis dM) (fun _ ↦ 1) (fun _ _ _ _ ↦ by decide) i j
      (Submodule.mul_mem_mul hx hy)

/-- A concrete finite degree bound on all original generator images. -/
def generatorDegreeBound : ℕ :=
  max 1 (Finset.univ.sup (fun i : ι ↦
    ((PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι k (bL i)))).support.sup
      (fun m ↦ m.degree)))

theorem one_le_generatorDegreeBound : 1 ≤ generatorDegreeBound (bL := bL) (bM := bM) Φ :=
  Nat.le_max_left _ _

theorem generator_mem_degree_bound (i : ι) :
    Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈
      PBW.weightedUpper bM (fun _ ↦ 1) (generatorDegreeBound (bL := bL) (bM := bM) Φ) := by
  apply (PBW.mem_weightedUpper_iff bM (fun _ ↦ 1) _ _).mpr
  intro m hm
  rw [← Finsupp.degree_eq_weight_one]
  unfold generatorDegreeBound
  exact (Finset.le_sup hm).trans
    ((Finset.le_sup (f := fun i : ι ↦
      ((PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι k (bL i)))).support.sup
        (fun m ↦ m.degree)) (Finset.mem_univ i)).trans (Nat.le_max_right _ _))

/-- Reweighting coefficient polynomials does not change the ordinary PBW degree support. -/
theorem homogenize_preserves_degree (n D : ℕ) (a : UniversalEnvelopingAlgebra k M)
    (ha : a ∈ PBW.weightedUpper bM (fun _ ↦ 1) D) :
    EnvelopingFamily.homogenize dM n a ∈ ordinary dM D := by
  simp only [EnvelopingFamily.homogenize, Finsupp.sum]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  exact PBW.pbwBasis_mem_weightedUpper (Family.basis dM) (fun _ ↦ 1)
    ((PBW.mem_weightedUpper_iff bM (fun _ ↦ 1) D a).mp ha m hm)

/-- An additional unit of filtration weight gives an actual factor of the polynomial parameter. -/
theorem homogenize_succ (n : ℕ) (a : UniversalEnvelopingAlgebra k M)
    (ha : a ∈ PBW.weightedLower bM dM.weight (n + 1)) :
    EnvelopingFamily.homogenize dM n a =
      (Polynomial.X : Polynomial k) • EnvelopingFamily.homogenize dM (n + 1) a := by
  simp only [EnvelopingFamily.homogenize, Finsupp.sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro m hm
  have hd := (PBW.mem_weightedLower_iff bM dM.weight (n + 1) a).mp ha m hm
  have he : Finsupp.weight dM.weight m - n = Finsupp.weight dM.weight m - (n + 1) + 1 := by omega
  rw [he, pow_succ]
  congr 1
  ac_rfl

/-- The true polynomial correction after separating the target linear generator. -/
def correction (i : ι) : EnvelopingFamily.U dM :=
  EnvelopingFamily.homogenize dM (dL.weight i + 1)
    (Φ (UniversalEnvelopingAlgebra.ι k (bL i)) - UniversalEnvelopingAlgebra.ι k (bM i))

theorem linear_generator_mem (i : ι) :
    UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i) ∈ ordinary dM 1 := by
  simpa only [ordinary, PBW.pbwBasis_single] using
    PBW.pbwBasis_mem_weightedUpper (Family.basis dM) (fun _ ↦ 1)
      (m := Finsupp.single i 1) (d := 1) (by simp [Finsupp.weight_single])

theorem correction_mem (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (i : ι) : correction dL dM Φ i ∈ ordinary dM D := by
  apply homogenize_preserves_degree
  apply Submodule.sub_mem _ (hdeg i)
  simpa only [PBW.pbwBasis_single] using
    PBW.pbwBasis_mem_weightedUpper bM (fun _ ↦ 1)
      (m := Finsupp.single i 1) (d := D) (by simpa [Finsupp.weight_single] using hD)

/-- The actual Rees algebra map has the form `generator + t * bounded correction`. -/
theorem rees_generator_decomposition (i : ι) :
    EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ'
      (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i)) =
        UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i) +
          (Polynomial.X : Polynomial k) • correction dL dM Φ i := by
  rw [EnvelopingFamily.ofLeading_ι_basis]
  have hc : Φ (UniversalEnvelopingAlgebra.ι k (bL i)) - UniversalEnvelopingAlgebra.ι k (bM i) ∈
      PBW.weightedLower bM dM.weight (dL.weight i + 1) := by
    simpa only [AlgEquiv.coe_toAlgHom] using hΦ i
  have he : Φ (UniversalEnvelopingAlgebra.ι k (bL i)) =
      (Φ (UniversalEnvelopingAlgebra.ι k (bL i)) - UniversalEnvelopingAlgebra.ι k (bM i)) +
        UniversalEnvelopingAlgebra.ι k (bM i) := (sub_add_cancel _ _).symm
  rw [he, EnvelopingFamily.homogenize_add, homogenize_succ dM _ _ hc]
  have hg : EnvelopingFamily.homogenize dM (dL.weight i) (UniversalEnvelopingAlgebra.ι k (bM i)) =
      UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i) := by
    rw [congrFun hw i, ← PBW.pbwBasis_single bM i, EnvelopingFamily.homogenize_pbwBasis]
    simp [Finsupp.weight_single]
  rw [hg]
  exact add_comm _ _

local instance trackingPolynomialAlgebra :
    Algebra (Polynomial k) (Polynomial (EnvelopingFamily.U dM)) := Polynomial.algebraOfAlgebra
local instance trackingPowerSeriesAlgebra :
    Algebra (Polynomial k) (PowerSeries (EnvelopingFamily.U dM)) := MvPowerSeries.instAlgebra

/-- A finite auxiliary variable records how many positive-parameter corrections were used. -/
def trackingGenerator (i : ι) : Polynomial (EnvelopingFamily.U dM) :=
  Polynomial.C (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i)) +
    Polynomial.X * Polynomial.C (correction dL dM Φ i)

@[simp] theorem trackingGenerator_coeff_zero (i : ι) :
    (trackingGenerator dL dM Φ i).coeff 0 =
      UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dM i) := by
  simp [trackingGenerator]

theorem trackingGenerator_coeff_pos_mem (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (i : ι) (r : ℕ) (hr : r ≠ 0) :
    (trackingGenerator dL dM Φ i).coeff r ∈ ordinary dM D := by
  cases r with
  | zero => exact (hr rfl).elim
  | succ r =>
      simp only [trackingGenerator, Polynomial.coeff_add, Polynomial.coeff_C,
        Nat.succ_ne_zero, if_false, zero_add, Polynomial.coeff_X_mul]
      by_cases h : r = 0
      · subst r
        simpa using correction_mem dL dM Φ D hD hdeg i
      · simp [h]

theorem trackingGenerator_eval (i : ι) :
    PolynomialDiagonalBound.trackingEval (k := k) (trackingGenerator dL dM Φ i) =
      EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ'
        (UniversalEnvelopingAlgebra.ι (Polynomial k) (Family.basis dL i)) := by
  rw [trackingGenerator, PolynomialDiagonalBound.trackingEval_linear]
  exact (rees_generator_decomposition dL dM Φ hw hΦ hΦ' i).symm

/-- The generic multiplicative estimate applied to products in the actual target envelope. -/
theorem trackingProduct_coeff_mem (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (w : List ι) (r : ℕ) :
    PowerSeries.coeff r ((w.map (fun i ↦
      ((trackingGenerator dL dM Φ i) : PowerSeries (EnvelopingFamily.U dM)))).prod) ∈
        ordinary dM (w.length + r * (D - 1)) := by
  have h0 : ∀ f ∈ w.map (fun i ↦
      ((trackingGenerator dL dM Φ i) : PowerSeries (EnvelopingFamily.U dM))),
      PowerSeries.coeff 0 f ∈ ordinary dM 1 := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    simpa only [Polynomial.coeff_coe, trackingGenerator_coeff_zero] using linear_generator_mem dM i
  have hp : ∀ f ∈ w.map (fun i ↦
      ((trackingGenerator dL dM Φ i) : PowerSeries (EnvelopingFamily.U dM))),
      ∀ j, j ≠ 0 → PowerSeries.coeff j f ∈ ordinary dM D := by
    intro f hf j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    simpa only [Polynomial.coeff_coe] using trackingGenerator_coeff_pos_mem dL dM Φ D hD hdeg i j hj
  simpa only [List.length_map] using
    DegreeBound.product_generator_bound (ordinary_mono dM) hD
      (w.map (fun i ↦ ((trackingGenerator dL dM Φ i) : PowerSeries (EnvelopingFamily.U dM)))) h0 hp r

/-- The finite tracking polynomials embed coefficientwise, including their noncommutative coefficients. -/
def trackingToSeries : Polynomial (EnvelopingFamily.U dM) →ₐ[Polynomial k]
    PowerSeries (EnvelopingFamily.U dM) where
  toRingHom := Polynomial.coeToPowerSeries.ringHom
  commutes' p := by
    rw [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply]
    exact Polynomial.coe_C _

variable [CharZero k]

/-- The auxiliary polynomial represents the true symmetrized image of an input monomial. -/
def trackingAverage (m : ι →₀ ℕ) : Polynomial (EnvelopingFamily.U dM) :=
  PBW.averagedProduct (Polynomial k) (Polynomial (EnvelopingFamily.U dM))
    (PBW.orderedWord m).length (fun i ↦ trackingGenerator dL dM Φ ((PBW.orderedWord m).get i))

theorem trackingAverage_coe (m : ι →₀ ℕ) :
    (trackingAverage dL dM Φ m : PowerSeries (EnvelopingFamily.U dM)) =
      PBW.averagedProduct (Polynomial k) (PowerSeries (EnvelopingFamily.U dM))
        (PBW.orderedWord m).length (fun i ↦
          ((trackingGenerator dL dM Φ ((PBW.orderedWord m).get i)) :
            PowerSeries (EnvelopingFamily.U dM))) :=
  EnvelopingIsomorphism.Enveloping.averagedProduct_map
    (trackingToSeries dM) _ _

/-- Every auxiliary coefficient has the sharp excess bound in the native PBW filtration. -/
theorem trackingAverage_coeff_mem (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (m : ι →₀ ℕ) (r : ℕ) :
    (trackingAverage dL dM Φ m).coeff r ∈ ordinary dM (m.degree + r * (D - 1)) := by
  rw [← Polynomial.coeff_coe, trackingAverage_coe, PBW.averagedProduct_apply,
    PowerSeries.coeff_smul, map_sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ hσ
  simpa only [List.map_ofFn, List.length_ofFn, Function.comp_def,
    Homogenization.length_orderedWord_eq_degree] using
    trackingProduct_coeff_mem dL dM Φ D hD hdeg
      (List.ofFn ((PBW.orderedWord m).get ∘ σ)) r

/-- The actual inverse PBW symmetrization into polynomial coordinates over `k[t]`. -/
def inverseSym : EnvelopingFamily.U dM →ₗ[Polynomial k] MvPolynomial ι (Polynomial k) :=
  (Homogenization.symPolynomialEquiv (Family.basis dM)).symm.toLinearMap

/-- Ordinary degree cannot increase under this actual inverse map. -/
theorem inverseSym_degree {x : EnvelopingFamily.U dM} {n : ℕ}
    (hx : x ∈ ordinary dM n) {m : ι →₀ ℕ}
    (hm : MvPolynomial.coeff m (inverseSym dM x) ≠ 0) : m.degree ≤ n :=
  PBW.symmetrizationEquiv_symm_polynomial_support_degree_le (Family.basis dM) hx
    (MvPolynomial.mem_support_iff.mpr hm)

/-- The actual polynomial Rees map in the common symmetric coordinates. -/
def comparisonMap : MvPolynomial ι (Polynomial k) →ₗ[Polynomial k] MvPolynomial ι (Polynomial k) :=
  Homogenization.symPolynomialMap (Family.basis dL) (Family.basis dM)
    (EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ')

/-- No generic substitution is used here: finite tracking evaluation agrees with the constructed
Rees equivalence on each actual symmetrized input monomial. -/
theorem comparison_monomial_eq_tracking (m : ι →₀ ℕ) :
    comparisonMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial m 1) =
      inverseSym dM (PolynomialDiagonalBound.trackingEval (k := k) (trackingAverage dL dM Φ m)) := by
  let ψ := EnvelopingFamily.ofLeading dL dM Φ hw hΦ hΦ'
  change inverseSym dM (ψ (Homogenization.symPolynomialEquiv (Family.basis dL)
    (MvPolynomial.monomial m 1))) = _
  rw [Homogenization.symPolynomialEquiv_monomial, Homogenization.symBasis_apply,
    PBW.symmetrizationEquiv_apply, PBW.symmetrization_basis, PBW.averagedWord_map]
  apply congrArg (inverseSym dM)
  change ψ.toAlgHom (PBW.averagedProduct _ _ _ _) = _
  rw [EnvelopingIsomorphism.Enveloping.averagedProduct_map, trackingAverage,
    EnvelopingIsomorphism.Enveloping.averagedProduct_map]
  congr 1
  funext i
  exact (trackingGenerator_eval dL dM Φ hw hΦ hΦ' ((PBW.orderedWord m).get i)).symm

/-- The auxiliary constant coefficient is an algebra map even for the noncommutative target. -/
def trackingConstant : Polynomial (EnvelopingFamily.U dM) →ₐ[Polynomial k] EnvelopingFamily.U dM where
  toRingHom := Polynomial.constantCoeff
  commutes' p := by
    change (Polynomial.C (algebraMap (Polynomial k) (EnvelopingFamily.U dM) p)).coeff 0 = _
    simp

/-- At auxiliary degree zero, the true target symmetrization is recovered exactly over `k[t]`. -/
theorem trackingAverage_coeff_zero (m : ι →₀ ℕ) :
    (trackingAverage dL dM Φ m).coeff 0 = Homogenization.symBasis (Family.basis dM) m := by
  change trackingConstant dM (trackingAverage dL dM Φ m) = _
  rw [trackingAverage, EnvelopingIsomorphism.Enveloping.averagedProduct_map,
    Homogenization.symBasis_apply, PBW.symmetrizationEquiv_apply,
    PBW.symmetrization_basis, PBW.averagedWord_map]
  congr 1
  funext i
  exact trackingGenerator_coeff_zero dL dM Φ ((PBW.orderedWord m).get i)

theorem inverseSym_symBasis (m : ι →₀ ℕ) :
    inverseSym dM (Homogenization.symBasis (Family.basis dM) m) = MvPolynomial.monomial m 1 := by
  change (Homogenization.symPolynomialEquiv (Family.basis dM)).symm
    (Homogenization.symBasis (Family.basis dM) m) = _
  rw [← Homogenization.symPolynomialEquiv_monomial, LinearEquiv.symm_apply_apply]

/-- The actual symmetric comparison has no coefficient beyond the uniform excess bound. -/
theorem comparison_coeff_eq_zero_of_degree (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (a m : ι →₀ ℕ) (r : ℕ) (hm : a.degree + r * (D - 1) < m.degree) :
    (MvPolynomial.coeff m (comparisonMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial a 1))).coeff r = 0 := by
  rw [comparison_monomial_eq_tracking]
  apply PolynomialDiagonalBound.coeff_trackingEval_eq_zero_of_degree
    (inverseSym dM) (trackingAverage dL dM Φ a) a.degree (D - 1) _ r m hm
  intro j q hq
  exact inverseSym_degree dM (trackingAverage_coeff_mem dL dM Φ D hD hdeg a j) hq

/-- The actual coefficient at `t=0` is the identity in the common symmetric polynomial coordinates. -/
theorem comparison_constant_coeff (a m : ι →₀ ℕ) :
    (MvPolynomial.coeff m (comparisonMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial a 1))).coeff 0 =
      if a = m then 1 else 0 := by
  rw [comparison_monomial_eq_tracking, PolynomialDiagonalBound.coeff_zero_trackingEval,
    trackingAverage_coeff_zero, inverseSym_symBasis]
  by_cases h : a = m <;> simp [MvPolynomial.coeff_monomial, h]

/-- Actual coefficient vectors, extracted from the polynomial comparison over `k[t]`. -/
def coefficientColumn (r : ℕ) (a : ι →₀ ℕ) : (ι →₀ ℕ) →₀ k :=
  (((MvPolynomial.basisMonomials ι (Polynomial k)).repr
    (comparisonMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial a 1))).mapRange
      (fun p ↦ Polynomial.coeff p r) (by simp))

/-- The actual coefficient of order `r` as an endomorphism of the fixed polynomial coordinate space. -/
def coefficientOperator (r : ℕ) : Module.End k ((ι →₀ ℕ) →₀ k) :=
  Finsupp.linearCombination k (coefficientColumn dL dM Φ hw hΦ hΦ' r)

@[simp] theorem coefficientOperator_single (r : ℕ) (a m : ι →₀ ℕ) :
    coefficientOperator dL dM Φ hw hΦ hΦ' r (Finsupp.single a 1) m =
      (MvPolynomial.coeff m (comparisonMap dL dM Φ hw hΦ hΦ' (MvPolynomial.monomial a 1))).coeff r := by
  simp only [coefficientOperator, Finsupp.linearCombination_single, one_smul,
    coefficientColumn, Finsupp.mapRange_apply]
  rfl

/-- E2 for the actual coefficient operators, with the required bound linear in the outer order. -/
theorem coefficientOperator_hasDegreeShift (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ i, Φ (UniversalEnvelopingAlgebra.ι k (bL i)) ∈ PBW.weightedUpper bM (fun _ ↦ 1) D)
    (r : ℕ) :
    Rees.HasDegreeShift (fun m : ι →₀ ℕ ↦ m.degree)
      (coefficientOperator dL dM Φ hw hΦ hΦ' r) (r * (D - 1)) := by
  intro a m hm
  by_contra h
  apply hm
  rw [coefficientOperator_single]
  exact comparison_coeff_eq_zero_of_degree dL dM Φ hw hΦ hΦ' D hD hdeg a m r
    (Nat.lt_of_not_ge h)

theorem coefficientOperator_zero : coefficientOperator dL dM Φ hw hΦ hΦ' 0 = 1 := by
  have hcol (a : ι →₀ ℕ) : coefficientColumn dL dM Φ hw hΦ hΦ' 0 a = Finsupp.single a 1 := by
    ext m
    change (MvPolynomial.coeff m (comparisonMap dL dM Φ hw hΦ hΦ'
      (MvPolynomial.monomial a 1))).coeff 0 = (Finsupp.single a (1 : k)) m
    rw [comparison_constant_coeff]
    simp only [Finsupp.single_apply]
  apply Finsupp.lhom_ext
  intro a c
  change (Finsupp.linearCombination k (coefficientColumn dL dM Φ hw hΦ hΦ' 0))
    (Finsupp.single a c) = Finsupp.single a c
  rw [Finsupp.linearCombination_single, hcol, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The finite bound is derived from the given algebra equivalence itself. -/
theorem actual_degreeShift (r : ℕ) :
    Rees.HasDegreeShift (fun m : ι →₀ ℕ ↦ m.degree)
      (coefficientOperator dL dM Φ hw hΦ hΦ' r)
        (r * (generatorDegreeBound (bL := bL) (bM := bM) Φ - 1)) :=
  coefficientOperator_hasDegreeShift dL dM Φ hw hΦ hΦ' _
    (one_le_generatorDegreeBound Φ) (generator_mem_degree_bound Φ) r

/-- E3's actual uniformly bounded Laurent endomorphism series, completed only after E2. -/
def completedOperator :
    PowerSeries (LaurentSeries (Module.End k ((ι →₀ ℕ) →₀ k))) :=
  reweightPowerSeries (fun m : ι →₀ ℕ ↦ m.degree)
    (coefficientOperator dL dM Φ hw hΦ hΦ') (generatorDegreeBound (bL := bL) (bM := bM) Φ)
    (actual_degreeShift dL dM Φ hw hΦ hΦ')

theorem completedOperator_constantCoeff :
    PowerSeries.constantCoeff (completedOperator dL dM Φ hw hΦ hΦ') = 1 :=
  constantCoeff_reweightPowerSeries _ _ _ (actual_degreeShift dL dM Φ hw hΦ hΦ')
    (coefficientOperator_zero dL dM Φ hw hΦ hΦ')

theorem completedOperator_lower_bound (r : ℕ) :
    EnvelopingIsomorphism.FormalSeries.LaurentModule.BoundedBelow
      (k := k) (X := Module.End k ((ι →₀ ℕ) →₀ k))
      (-((r * (generatorDegreeBound (bL := bL) (bM := bM) Φ - 1) : ℕ) : ℤ))
      (reweightFamily (fun m : ι →₀ ℕ ↦ m.degree)
        (coefficientOperator dL dM Φ hw hΦ hΦ') _ (actual_degreeShift dL dM Φ hw hΦ hΦ') r) :=
  boundedBelow_reweightFamily _ _ _ (actual_degreeShift dL dM Φ hw hΦ hΦ') r

/-- The column construction is exactly coefficient extraction from the actual comparison on
every input polynomial, after its natural coefficient inclusion into `k[t]`. -/
theorem coefficientOperator_eq_actual (r : ℕ) :
    coefficientOperator dL dM Φ hw hΦ hΦ' r =
      PolynomialCoefficientOperators.coefficientOperator (Polynomial.lcoeff k r)
        (comparisonMap dL dM Φ hw hΦ hΦ') := by
  apply PolynomialCoefficientOperators.coordinate_end_ext
  intro a m
  rw [coefficientOperator_single, PolynomialCoefficientOperators.coefficientOperator_single]
  rfl

theorem coefficientOperator_apply (r : ℕ) (p : (ι →₀ ℕ) →₀ k) (m : ι →₀ ℕ) :
    coefficientOperator dL dM Φ hw hΦ hΦ' r p m =
      (MvPolynomial.coeff m (comparisonMap dL dM Φ hw hΦ hΦ'
        (PolynomialCoefficientOperators.includePolynomial (S := Polynomial k) p))).coeff r := by
  rw [coefficientOperator_eq_actual, PolynomialCoefficientOperators.coefficientOperator_apply]
  rfl

/-- The Laurent lower bound is a statement about the whole coefficient endomorphism, uniformly
over its input polynomial. -/
theorem completedOperator_coeff_eq_zero (r : ℕ) (j : ℤ)
    (hj : j < -((r * (generatorDegreeBound (bL := bL) (bM := bM) Φ - 1) : ℕ) : ℤ)) :
    (PowerSeries.coeff r (completedOperator dL dM Φ hw hΦ hΦ')).coeff j = 0 := by
  rw [completedOperator, coeff_reweightPowerSeries]
  exact degreeDiagonal_eq_zero_of_lt _ _ (actual_degreeShift dL dM Φ hw hΦ hΦ' r) hj

/-- Explicitly instantiate the native Hahn ring on endomorphism coefficients, avoiding its
competing inherited zero instances during typeclass inference. -/
scoped instance endLaurentRing : Ring (LaurentSeries (Module.End k ((ι →₀ ℕ) →₀ k))) :=
  HahnSeries.instRing (Γ := ℤ) (R := Module.End k ((ι →₀ ℕ) →₀ k))

/-- The actual completed endomorphism series is a unit because its outer constant is identity. -/
theorem completedOperator_isUnit : IsUnit (completedOperator dL dM Φ hw hΦ hΦ') := by
  exact (PowerSeries.isUnit_iff_constantCoeff
    (R := LaurentSeries (Module.End k ((ι →₀ ℕ) →₀ k)))
    (φ := completedOperator dL dM Φ hw hΦ hΦ')).mpr
      (by rw [completedOperator_constantCoeff]; exact isUnit_one)

def completedUnit : (PowerSeries (LaurentSeries (Module.End k ((ι →₀ ℕ) →₀ k))))ˣ :=
  (completedOperator_isUnit dL dM Φ hw hΦ hΦ').unit

@[simp] theorem completedUnit_val :
    (completedUnit dL dM Φ hw hΦ hΦ' : PowerSeries (LaurentSeries (Module.End k ((ι →₀ ℕ) →₀ k)))) =
      completedOperator dL dM Φ hw hΦ hΦ' :=
  (completedOperator_isUnit dL dM Φ hw hΦ hΦ').unit_spec

end EnvelopingIsomorphism.Rees.UniformBound
