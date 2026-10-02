import EnvelopingIsomorphism.Identification.PBWPolynomial
import EnvelopingIsomorphism.Identification.PolynomialLeading
import EnvelopingIsomorphism.Identification.PolynomialDifference
import EnvelopingIsomorphism.Enveloping.Augmentation
import EnvelopingIsomorphism.Enveloping.UniversalProperties
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Character translation and the PBW symbol of the action on a common eigenvector. -/

noncomputable section

namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra
open EnvelopingIsomorphism.Enveloping EnvelopingIsomorphism.PBW

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A common adjoint eigenvector intertwines right multiplication with character translation. -/
theorem mul_ι_eigenvector_eq_translation (χ : LieAlgebra.LieCharacter R L) (w : L)
    (hw : ∀ x : L, ⁅x, w⁆ = χ x • w) (a : UniversalEnvelopingAlgebra R L) :
    a * ι R w = ι R w * translation χ a := by
  induction a using EnvelopingIsomorphism.Enveloping.induction with
  | scalar r =>
    simp [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm]
  | generator x =>
    have h : ι R x * ι R w - ι R w * ι R x = χ x • ι R w := by
      have h' := congrArg (ι R) (hw x)
      simpa only [LieHom.map_lie, map_smul, Ring.lie_def] using h'
    calc
      _ = ι R w * ι R x + χ x • ι R w := by rw [← h]; abel
      _ = _ := by rw [translation_ι, mul_add, Algebra.algebraMap_eq_smul_one,
        Algebra.mul_smul_comm, mul_one]
  | mul a b ha hb =>
    rw [mul_assoc, hb, ← mul_assoc, ha, map_mul, mul_assoc]
  | add a b ha hb => simp only [add_mul, map_add, mul_add, ha, hb]

/-- The exact inner action is a translated finite difference followed by multiplication by `w`. -/
theorem lie_ι_eigenvector_eq_translation_sub (χ : LieAlgebra.LieCharacter R L) (w : L)
    (hw : ∀ x : L, ⁅x, w⁆ = χ x • w) (a : UniversalEnvelopingAlgebra R L) :
    ⁅a, ι R w⁆ = ι R w * (translation χ a - a) := by
  rw [Ring.lie_def, mul_ι_eigenvector_eq_translation χ w hw, mul_sub]

variable {α : Type*}

/-- Expand a scalar translation of a word while retaining the original order of its subwords. -/
def shiftWord (c : α → R) : List α → (List α →₀ R)
  | [] => Finsupp.single [] 1
  | i :: w => (shiftWord c w).mapDomain (List.cons i) + c i • shiftWord c w

/-- The ordinary commutative polynomial associated with a word. -/
def commutativeWord (w : List α) : MvPolynomial α R := (w.map MvPolynomial.X).prod

def wordPolynomial : (List α →₀ R) →ₗ[R] MvPolynomial α R :=
  Finsupp.linearCombination R commutativeWord

@[simp] theorem wordPolynomial_single (w : List α) (r : R) :
    wordPolynomial (Finsupp.single w r) = r • (commutativeWord w : MvPolynomial α R) := by
  classical
  simp [wordPolynomial]

theorem wordPolynomial_cons_mapDomain (i : α) (p : List α →₀ R) :
    wordPolynomial (p.mapDomain (List.cons i)) = MvPolynomial.X i * wordPolynomial p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, hp, hq, mul_add]
  | single w r => simp [commutativeWord, Algebra.mul_smul_comm]

theorem shiftWord_support_sublist (c : α → R) (w : List α) {v : List α}
    (hv : v ∈ (shiftWord c w).support) : v.Sublist w := by
  classical
  induction w generalizing v with
  | nil =>
    have h : v = [] := Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
    simp [h]
  | cons i w ih =>
    rcases Finset.mem_union.mp (Finsupp.support_add hv) with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h)
      exact (ih hu).cons_cons i
    · exact (ih (Finsupp.support_smul h)).cons i

theorem wordPolynomial_shiftWord (c : α → R) (w : List α) :
    wordPolynomial (shiftWord c w) =
      (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (c i)))
        (commutativeWord w : MvPolynomial α R) := by
  induction w with
  | nil => simp [shiftWord, commutativeWord]
  | cons i w ih =>
    simp only [shiftWord, map_add, map_smul, wordPolynomial_cons_mapDomain, ih,
      commutativeWord, List.map_cons, List.prod_cons, map_mul, MvPolynomial.aeval_X,
      add_mul, MvPolynomial.C_mul']

variable [LinearOrder α] (b : Module.Basis α R L)

theorem wordEval_single (w : List α) (r : R) :
    wordEval b (Finsupp.single w r) = r • (w.map (ι R ∘ b)).prod := by
  have h := (wordEval b).map_smul r (Finsupp.single w 1)
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, wordEval_single_one] using h

theorem wordEval_cons_mapDomain (i : α) (p : List α →₀ R) :
    wordEval b (p.mapDomain (List.cons i)) = ι R (b i) * wordEval b p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, hp, hq, mul_add]
  | single w r => simp [wordEval_single, Algebra.mul_smul_comm]

theorem wordEval_shiftWord (χ : LieAlgebra.LieCharacter R L) (w : List α) :
    wordEval b (shiftWord (fun i ↦ χ (b i)) w) =
      translation χ (wordEval b (Finsupp.single w 1)) := by
  induction w with
  | nil => simp only [shiftWord, wordEval_single_one, List.map_nil, List.prod_nil, map_one]
  | cons i w ih =>
    rw [shiftWord, map_add, map_smul, wordEval_cons_mapDomain, ih]
    simp only [wordEval_single_one, List.map_cons, List.prod_cons, Function.comp_apply,
      map_mul, translation_ι, add_mul, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]

theorem commutativeWord_eq_monomial (w : List α) :
    (commutativeWord w : MvPolynomial α R) = MvPolynomial.monomial (wordIndex w) 1 := by
  induction w with
  | nil => simp [commutativeWord]
  | cons i w ih =>
    change MvPolynomial.X i * commutativeWord w = _
    rw [ih, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, wordIndex_cons]

theorem pbwPolynomialEquiv_wordEval_ordered (w : List α) (hw : w.Pairwise (· ≤ ·)) :
    pbwPolynomialEquiv b (wordEval b (Finsupp.single w 1)) = commutativeWord w := by
  rw [commutativeWord_eq_monomial, ← pbwPolynomialEquiv_basis b (wordIndex w)]
  congr 1
  rw [wordEval_single_one, pbwBasis_apply, orderedWord_wordIndex hw]

theorem pbwPolynomialEquiv_wordEval_of_ordered_support (p : List α →₀ R)
    (hp : ∀ w ∈ p.support, w.Pairwise (· ≤ ·)) :
    pbwPolynomialEquiv b (wordEval b p) = wordPolynomial p := by
  classical
  conv_lhs => rw [← Finsupp.sum_single p]
  simp only [Finsupp.sum, map_sum, wordEval_single, map_smul, wordPolynomial,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [← wordEval_single_one, pbwPolynomialEquiv_wordEval_ordered b w (hp w hw)]

/-- Ordered PBW coordinates intertwine character translation with ordinary polynomial translation. -/
theorem pbwPolynomialEquiv_translation (χ : LieAlgebra.LieCharacter R L)
    (a : UniversalEnvelopingAlgebra R L) :
    pbwPolynomialEquiv b (translation χ a) =
      (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
        (pbwPolynomialEquiv b a) := by
  have h : (pbwPolynomialEquiv b).toLinearMap.comp (translation χ).toLinearMap =
      (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i)))).toLinearMap.comp
        (pbwPolynomialEquiv b).toLinearMap := by
    apply (pbwBasis b).ext
    intro m
    change pbwPolynomialEquiv b (translation χ (pbwBasis b m)) = _
    calc
      _ = pbwPolynomialEquiv b
          (wordEval b (shiftWord (fun i ↦ χ (b i)) (orderedWord m))) := by
        rw [wordEval_shiftWord, wordEval_single_one, pbwBasis_apply]
      _ = wordPolynomial (shiftWord (fun i ↦ χ (b i)) (orderedWord m)) := by
        apply pbwPolynomialEquiv_wordEval_of_ordered_support
        intro w hw
        exact (pairwise_orderedWord m).sublist (shiftWord_support_sublist _ _ hw)
      _ = (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
          (commutativeWord (orderedWord m) : MvPolynomial α R) :=
        wordPolynomial_shiftWord _ _
      _ = _ := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
          pbwPolynomialEquiv_basis, commutativeWord_eq_monomial, wordIndex_orderedWord]
  exact LinearMap.congr_fun h a

/-- The exact common-eigenvector action in actual PBW polynomial coordinates. -/
theorem pbwPolynomialEquiv_lie_eigenvector (χ : LieAlgebra.LieCharacter R L) (w : L)
    (hw : ∀ x : L, ⁅x, w⁆ = χ x • w) (a : UniversalEnvelopingAlgebra R L) :
    pbwPolynomialEquiv b ⁅a, ι R w⁆ =
      pbwStar b (pbwPolynomialEquiv b (ι R w))
        ((MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
          (pbwPolynomialEquiv b a) - pbwPolynomialEquiv b a) := by
  rw [← pbwPolynomialEquiv_translation b χ a, ← map_sub, pbwStar_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    lie_ι_eigenvector_eq_translation_sub χ w hw a]

theorem polynomial_mem_basisUpper_iff (ω : α → ℕ) (n : ℕ) (p : MvPolynomial α R) :
    p ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) n ↔
      ∀ m ∈ p.support, Finsupp.weight ω m ≤ n :=
  mem_basisSupport _ _ _

theorem polynomial_isWeightedHomogeneous_of_upper_zero (ω : α → ℕ) (p : MvPolynomial α R)
    (hp : p ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) 0) :
    p.IsWeightedHomogeneous ω 0 := by
  intro m hm
  exact Nat.eq_zero_of_le_zero
    ((polynomial_mem_basisUpper_iff ω 0 p).mp hp m (MvPolynomial.mem_support_iff.mpr hm))

theorem weightedComponent_eq_zero_of_basisStrict (ω : α → ℕ) (n : ℕ) (p : MvPolynomial α R)
    (hp : p ∈ basisStrict (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) n) :
    MvPolynomial.weightedHomogeneousComponent ω n p = 0 := by
  apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
  intro m hm
  exact Nat.ne_of_lt ((mem_basisSupport (MvPolynomial.basisMonomials α R) _ p).mp hp m hm)

theorem weightedComponent_zeroWeight_mul (ω : α → ℕ) (n : ℕ) (p q : MvPolynomial α R)
    (hp : p.IsWeightedHomogeneous ω 0) :
    MvPolynomial.weightedHomogeneousComponent ω n (p * q) =
      p * MvPolynomial.weightedHomogeneousComponent ω n q := by
  classical
  ext m
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  have hv {u v : α →₀ ℕ} (huv : u + v = m) (hu : MvPolynomial.coeff u p ≠ 0) :
      Finsupp.weight ω v = Finsupp.weight ω m := by
    rw [← huv, map_add, hp hu, zero_add]
  by_cases hm : Finsupp.weight ω m = n
  · rw [if_pos hm]
    apply Finset.sum_congr rfl
    rintro ⟨u, v⟩ huv
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hu : MvPolynomial.coeff u p = 0
    · simp [hu]
    · rw [if_pos ((hv (Finset.mem_antidiagonal.mp huv) hu).trans hm)]
  · rw [if_neg hm]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨u, v⟩ huv
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hu : MvPolynomial.coeff u p = 0
    · simp [hu]
    · rw [if_neg (by rw [hv (Finset.mem_antidiagonal.mp huv) hu]; exact hm), mul_zero]

/-- Multiplication by a weight-zero input has the usual product as its homogeneous leading term. -/
theorem weightedComponent_pbwStar_of_upper_zero (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (n : ℕ) (p q : MvPolynomial α R)
    (hp : p ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) 0)
    (hq : q ∈ basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) n) :
    MvPolynomial.weightedHomogeneousComponent ω n (pbwStar b p q) =
      p * MvPolynomial.weightedHomogeneousComponent ω n q := by
  have he := pbwStar_sub_mul_mem_strict b ω hc 0 n p hp q hq
  simp only [zero_add] at he
  have hz := weightedComponent_eq_zero_of_basisStrict ω n (pbwStar b p q - p * q) he
  rw [map_sub, sub_eq_zero] at hz
  rw [hz]
  exact weightedComponent_zeroWeight_mul ω n p q
    (polynomial_isWeightedHomogeneous_of_upper_zero ω p hp)

/-- The actual homogeneous leading derivation on a common eigenvector is the leading
component of the translated finite difference, multiplied by that eigenvector. -/
theorem pbwLeadingDerivation_eigenvector_eq_component_difference (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (χ : LieAlgebra.LieCharacter R L) (w : L) (hw : ∀ x : L, ⁅x, w⁆ = χ x • w)
    (hw0 : ι R w ∈ weightedUpper b ω 0)
    (a : UniversalEnvelopingAlgebra R L) (r : ℕ)
    (hshift : ∀ m, ⁅a, pbwBasis b m⁆ ∈ weightedUpper b ω (Finsupp.weight ω m + r))
    (hdiff : (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
        (pbwPolynomialEquiv b a) - pbwPolynomialEquiv b a ∈
      basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) r) :
    pbwLeadingDerivation b ω hc a r hshift (pbwPolynomialEquiv b (ι R w)) =
      pbwPolynomialEquiv b (ι R w) * MvPolynomial.weightedHomogeneousComponent ω r
        ((MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
          (pbwPolynomialEquiv b a) - pbwPolynomialEquiv b a) := by
  have hp0 := (pbwPolynomialEquiv_mem_upper_iff b ω 0 (ι R w)).mpr hw0
  have hph := polynomial_isWeightedHomogeneous_of_upper_zero ω _ hp0
  change leadingOperator (MvPolynomial.basisMonomials α R) (Finsupp.weight ω)
    (pbwInner b a) r (pbwPolynomialEquiv b (ι R w)) = _
  rw [leadingOperator_polynomial_homogeneous ω (pbwInner b a) r hph, zero_add,
    pbwInner_apply, LinearEquiv.symm_apply_apply, pbwPolynomialEquiv_lie_eigenvector b χ w hw a]
  exact weightedComponent_pbwStar_of_upper_zero b ω hc r _ _ hp0 hdiff

section FiniteBasis

variable [Fintype α]

/-- The actual leading inner derivation on a common weight-zero eigenvector is
the eigenvector times the directional derivative of the top PBW polynomial.
All filtration and translation bounds are derived from the stated concrete data. -/
theorem pbwLeadingDerivationOfUpper_eigenvector (ω : α → ℕ)
    (hω : ∀ i, ω i = 0 ∨ ω i = 1)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (χ : LieAlgebra.LieCharacter R L) (hχ : ∀ i, ω i = 0 → χ (b i) = 0)
    (w : L) (hw : ∀ x : L, ⁅x, w⁆ = χ x • w)
    (hw0 : ι R w ∈ weightedUpper b ω 0)
    (a : UniversalEnvelopingAlgebra R L) (m : ℕ) (hm : 0 < m)
    (ha : a ∈ weightedUpper b ω m) :
    pbwLeadingDerivationOfUpper b ω hc a m hm ha (pbwPolynomialEquiv b (ι R w)) =
      pbwPolynomialEquiv b (ι R w) *
        ∑ i, χ (b i) • MvPolynomial.pderiv i
          (MvPolynomial.weightedHomogeneousComponent ω m (pbwPolynomialEquiv b a)) := by
  have hp := (pbwPolynomialEquiv_mem_upper_iff b ω m a).mpr ha
  have hpsupport := (polynomial_mem_basisUpper_iff ω m _).mp hp
  have hdiff : (MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + MvPolynomial.C (χ (b i))))
        (pbwPolynomialEquiv b a) - pbwPolynomialEquiv b a ∈
      basisUpper (MvPolynomial.basisMonomials α R) (Finsupp.weight ω) (m - 1) := by
    apply (polynomial_mem_basisUpper_iff ω (m - 1) _).mpr
    intro n hn
    have h := PolynomialDifference.difference_support_lt ω (fun i ↦ χ (b i)) hω hχ hpsupport hn
    omega
  change pbwLeadingDerivation b ω hc a (m - 1)
    (inner_pbwBasis_mem_upper_pred b ω hc hm ha) (pbwPolynomialEquiv b (ι R w)) = _
  rw [pbwLeadingDerivation_eigenvector_eq_component_difference b ω hc χ w hw hw0 a
    (m - 1) (inner_pbwBasis_mem_upper_pred b ω hc hm ha) hdiff,
    PolynomialDifference.component_translation_sub ω (fun i ↦ χ (b i)) hω hχ hm hpsupport]

end FiniteBasis

end EnvelopingIsomorphism.Identification
