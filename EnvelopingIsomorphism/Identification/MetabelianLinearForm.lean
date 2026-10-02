import EnvelopingIsomorphism.Enveloping.AbelianIdeal
import EnvelopingIsomorphism.Identification.PBWPolynomial
import Mathlib.Algebra.MvPolynomial.Rename

/-! Actual polynomial-coefficient linear forms for PBW complementary degree at most one. -/

noncomputable section

namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra EnvelopingIsomorphism.PBW
open EnvelopingIsomorphism.Enveloping (complementWeight)

variable {R α β : Type*} [CommRing R]

def idealExponent (m : (α ⊕ β) →₀ ℕ) : α →₀ ℕ :=
  m.comapDomain Sum.inl Sum.inl_injective.injOn

def complementExponent (m : (α ⊕ β) →₀ ℕ) : β →₀ ℕ :=
  m.comapDomain Sum.inr Sum.inr_injective.injOn

theorem exponent_split (m : (α ⊕ β) →₀ ℕ) :
    m = (idealExponent m).mapDomain Sum.inl + (complementExponent m).mapDomain Sum.inr := by
  rw [← Finsupp.sumElim_eq_add]
  exact (Finsupp.comapDomain_sumElim_comapDomain m).symm

@[simp] theorem complementWeight_mapDomain_inl (m : α →₀ ℕ) :
    Finsupp.weight (complementWeight (β := β)) (m.mapDomain Sum.inl) = 0 := by
  induction m using Finsupp.induction with
  | zero => simp
  | single_add i n m hi hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, ih, Finsupp.weight_single]
    simp [complementWeight]

@[simp] theorem complementWeight_mapDomain_inr (m : β →₀ ℕ) :
    Finsupp.weight (complementWeight (α := α)) (m.mapDomain Sum.inr) = m.degree := by
  induction m using Finsupp.induction with
  | zero => simp
  | single_add i n m hi hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, ih, Finsupp.weight_single]
    simp [complementWeight]

theorem complementWeight_eq_degree (m : (α ⊕ β) →₀ ℕ) :
    Finsupp.weight complementWeight m = (complementExponent m).degree := by
  conv_lhs => rw [exponent_split m]
  rw [map_add, complementWeight_mapDomain_inl, complementWeight_mapDomain_inr, zero_add]

theorem exponent_of_complementWeight_le_one (m : (α ⊕ β) →₀ ℕ)
    (hm : Finsupp.weight complementWeight m ≤ 1) :
    m = (idealExponent m).mapDomain Sum.inl ∨
      ∃ q : β, m = (idealExponent m).mapDomain Sum.inl + Finsupp.single (Sum.inr q) 1 := by
  rw [complementWeight_eq_degree] at hm
  have hcases : (complementExponent m).degree = 0 ∨ (complementExponent m).degree = 1 := by omega
  rcases hcases with hzero | hone
  · have hz := (Finsupp.degree_eq_zero_iff _).mp hzero
    exact Or.inl ((exponent_split m).trans (by rw [hz]; simp))
  · obtain ⟨q, hq⟩ := (Finsupp.sum_eq_one_iff (complementExponent m)).mp hone
    exact Or.inr ⟨q, (exponent_split m).trans (by rw [hq, Finsupp.mapDomain_single])⟩

section Polynomial

variable [Fintype β]

/-- A polynomial in the ideal variables plus a linear form in the complementary variables. -/
def polynomialLinearForm :
    (MvPolynomial α R × (β → MvPolynomial α R)) →ₗ[R] MvPolynomial (α ⊕ β) R where
  toFun f := MvPolynomial.rename Sum.inl f.1 +
    ∑ q, MvPolynomial.rename Sum.inl (f.2 q) * MvPolynomial.X (Sum.inr q)
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]; abel
  map_smul' r f := by simp [Finset.smul_sum, smul_add, Algebra.smul_mul_assoc]

/-- Complementary degree at most one is an actual polynomial linear form. -/
theorem exists_polynomialLinearForm (p : MvPolynomial (α ⊕ β) R)
    (hp : ∀ m ∈ p.support, Finsupp.weight complementWeight m ≤ 1) :
    ∃ p0 : MvPolynomial α R, ∃ pq : β → MvPolynomial α R,
      p = MvPolynomial.rename Sum.inl p0 +
        ∑ q, MvPolynomial.rename Sum.inl (pq q) * MvPolynomial.X (Sum.inr q) := by
  classical
  have hmem : p ∈ LinearMap.range (polynomialLinearForm (R := R) (α := α) (β := β)) := by
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro m hm
    rcases exponent_of_complementWeight_le_one m (hp m hm) with hz | ⟨q, hq⟩
    · refine ⟨(MvPolynomial.monomial (idealExponent m) (MvPolynomial.coeff m p), 0), ?_⟩
      simp [polynomialLinearForm, MvPolynomial.rename_monomial, ← hz]
    · refine ⟨(0, Pi.single q (MvPolynomial.monomial (idealExponent m) (MvPolynomial.coeff m p))), ?_⟩
      simp [polynomialLinearForm, Pi.single_apply, apply_ite, MvPolynomial.rename_monomial,
        MvPolynomial.monomial_mul, MvPolynomial.X, ← hq]
  obtain ⟨⟨p0, pq⟩, h⟩ := hmem
  exact ⟨p0, pq, h.symm⟩

end Polynomial

section Native

variable {L : Type*} [LieRing L] [LieAlgebra R L] [LinearOrder (α ⊕ β)]
  (b : Module.Basis (α ⊕ β) R L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Evaluate ideal-variable polynomials in their actual ordered PBW coordinates. -/
def idealPolynomialLinear : MvPolynomial α R →ₗ[R] UniversalEnvelopingAlgebra R L :=
  (pbwPolynomialEquiv b).symm.toLinearMap.comp (MvPolynomial.rename Sum.inl).toLinearMap

@[simp] theorem pbwPolynomialEquiv_idealPolynomialLinear (p : MvPolynomial α R) :
    pbwPolynomialEquiv b (idealPolynomialLinear b p) = MvPolynomial.rename Sum.inl p := by
  simp [idealPolynomialLinear]

theorem idealPolynomialLinear_monomial (m : α →₀ ℕ) (r : R) :
    idealPolynomialLinear b (MvPolynomial.monomial m r) =
      r • pbwBasis b (m.mapDomain Sum.inl) := by
  change (pbwPolynomialEquiv b).symm (MvPolynomial.rename Sum.inl (MvPolynomial.monomial m r)) = _
  rw [MvPolynomial.rename_monomial]
  have h : (MvPolynomial.monomial (m.mapDomain Sum.inl) r : MvPolynomial (α ⊕ β) R) =
      r • MvPolynomial.monomial (m.mapDomain Sum.inl) (1 : R) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, map_smul, pbwPolynomialEquiv_symm_monomial]

@[simp] theorem idealPolynomialLinear_C (r : R) :
    idealPolynomialLinear b (MvPolynomial.C r) = algebraMap R _ r := by
  change idealPolynomialLinear b (MvPolynomial.monomial 0 r) = _
  rw [idealPolynomialLinear_monomial]
  simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem idealPolynomialLinear_X (i : α) :
    idealPolynomialLinear b (MvPolynomial.X i) = ι R (b (.inl i)) := by
  rw [MvPolynomial.X, idealPolynomialLinear_monomial, Finsupp.mapDomain_single, one_smul,
    pbwBasis_single]

theorem rename_inl_mem_upper_zero (p : MvPolynomial α R) :
    MvPolynomial.rename Sum.inl p ∈
      basisUpper (MvPolynomial.basisMonomials (α ⊕ β) R) (Finsupp.weight complementWeight) 0 := by
  classical
  apply (mem_basisSupport _ _ _).mpr
  intro m hm
  change m ∈ (MvPolynomial.rename Sum.inl p).support at hm
  rw [MvPolynomial.support_rename_of_injective Sum.inl_injective] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  exact (complementWeight_mapDomain_inl u).le

theorem pbwStar_rename_inl
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → complementWeight a < complementWeight i + complementWeight j)
    (p q : MvPolynomial α R) :
    pbwStar b (MvPolynomial.rename Sum.inl p) (MvPolynomial.rename Sum.inl q) =
      MvPolynomial.rename Sum.inl p * MvPolynomial.rename Sum.inl q := by
  have h := pbwStar_sub_mul_mem_strict b complementWeight hc 0 0 _
    (rename_inl_mem_upper_zero p) _ (rename_inl_mem_upper_zero q)
  have hz : basisStrict (MvPolynomial.basisMonomials (α ⊕ β) R)
      (Finsupp.weight complementWeight) 0 = ⊥ := by simp [basisStrict, basisSupport]
  rw [Nat.add_zero, hz, Submodule.mem_bot, sub_eq_zero] at h
  exact h

/-- The ideal polynomial map is an actual algebra homomorphism into the native UEA. -/
def idealPolynomialEval
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → complementWeight a < complementWeight i + complementWeight j) :
    MvPolynomial α R →ₐ[R] UniversalEnvelopingAlgebra R L :=
  AlgHom.ofLinearMap (idealPolynomialLinear b)
    (by simpa using idealPolynomialLinear_C b (1 : R)) (by
      intro p q
      apply (pbwPolynomialEquiv b).injective
      rw [pbwPolynomialEquiv_idealPolynomialLinear]
      change _ = pbwStar b (MvPolynomial.rename Sum.inl p) (MvPolynomial.rename Sum.inl q)
      rw [pbwStar_rename_inl b hc, map_mul])

variable (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → complementWeight a < complementWeight i + complementWeight j)

@[simp] theorem idealPolynomialEval_apply (p : MvPolynomial α R) :
    idealPolynomialEval b hc p = idealPolynomialLinear b p := rfl

@[simp] theorem pbwPolynomialEquiv_idealPolynomialEval (p : MvPolynomial α R) :
    pbwPolynomialEquiv b (idealPolynomialEval b hc p) = MvPolynomial.rename Sum.inl p :=
  pbwPolynomialEquiv_idealPolynomialLinear b p

@[simp] theorem idealPolynomialEval_X (i : α) :
    idealPolynomialEval b hc (MvPolynomial.X i) = ι R (b (.inl i)) :=
  idealPolynomialLinear_X b i

theorem idealPolynomialEval_injective : Function.Injective (idealPolynomialEval b hc) := by
  intro p q h
  apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
  simpa only [pbwPolynomialEquiv_idealPolynomialEval] using congrArg (pbwPolynomialEquiv b) h

theorem idealPolynomialEval_mem (H : LieIdeal R L) [IsLieAbelian H]
    (hH : (H : Submodule R L) = Submodule.span R (Set.range (fun i : α ↦ b (.inl i))))
    (p : MvPolynomial α R) : idealPolynomialEval b hc p ∈ idealPolynomialPart H := by
  have h : idealPolynomialEval b hc p ∈ weightedUpper b complementWeight 0 := by
    apply (pbwPolynomialEquiv_mem_upper_iff b complementWeight 0 _).mp
    rw [pbwPolynomialEquiv_idealPolynomialEval]
    exact rename_inl_mem_upper_zero p
  rw [← Enveloping.idealPolynomialPart_eq_complementDegree_zero b H hH] at h
  exact h

theorem range_idealPolynomialEval (H : LieIdeal R L) [IsLieAbelian H]
    (hH : (H : Submodule R L) = Submodule.span R (Set.range (fun i : α ↦ b (.inl i)))) :
    (idealPolynomialEval b hc).range = idealPolynomialPart H := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact idealPolynomialEval_mem b hc H hH p
  · apply Algebra.adjoin_le
    rintro _ ⟨x, rfl⟩
    have hspan : Submodule.span R (Set.range (fun i : α ↦ b (.inl i))) ≤
        (idealPolynomialEval b hc).range.toSubmodule.comap (ι R).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨MvPolynomial.X i, idealPolynomialEval_X b hc i⟩
    exact hspan (hH ▸ x.property)

theorem orderedWord_inl_add_single_inr
    (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
    (m : α →₀ ℕ) (q : β) :
    orderedWord (m.mapDomain Sum.inl + Finsupp.single (Sum.inr q) 1) =
      orderedWord (m.mapDomain Sum.inl) ++ [Sum.inr q] := by
  have h0 : wordWeight complementWeight
      (orderedWord (m.mapDomain (Sum.inl : α → α ⊕ β))) = 0 := by
    simp only [wordWeight, wordIndex_orderedWord, complementWeight_mapDomain_inl]
  have hletters := (Enveloping.wordWeight_eq_zero_iff complementWeight _).mp h0
  have hsorted : (orderedWord (m.mapDomain Sum.inl) ++ [Sum.inr q]).Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨pairwise_orderedWord _, by simp, ?_⟩
    intro i hi j hj
    have hj' : j = Sum.inr q := by simpa using hj
    subst j
    cases i with
    | inl i => exact hfirst i q
    | inr i => have h := hletters (.inr i) hi; simp [complementWeight] at h
  have hidx : wordIndex (orderedWord (m.mapDomain Sum.inl) ++ [Sum.inr q]) =
      m.mapDomain Sum.inl + Finsupp.single (Sum.inr q) 1 := by simp
  rw [← hidx]
  exact orderedWord_wordIndex hsorted

/-- Ideal-first order makes this an actual native product with no PBW correction. -/
theorem pbwBasis_inl_mul_ι_inr
    (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
    (m : α →₀ ℕ) (q : β) :
    pbwBasis b (m.mapDomain Sum.inl) * ι R (b (.inr q)) =
      pbwBasis b (m.mapDomain Sum.inl + Finsupp.single (Sum.inr q) 1) := by
  rw [pbwBasis_apply b (m.mapDomain Sum.inl + Finsupp.single (Sum.inr q) 1),
    orderedWord_inl_add_single_inr hfirst]
  simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    Function.comp_apply, pbwBasis_apply]

/-- The polynomial-coordinate linear form represents a genuine product in the original UEA. -/
theorem pbwPolynomialEquiv_idealPolynomialEval_mul_ι_inr
    (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
    (p : MvPolynomial α R) (q : β) :
    pbwPolynomialEquiv b (idealPolynomialEval b hc p * ι R (b (.inr q))) =
      MvPolynomial.rename Sum.inl p * MvPolynomial.X (Sum.inr q) := by
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [map_add, add_mul, hp, hr]
  | monomial m r =>
    rw [idealPolynomialEval_apply, idealPolynomialLinear_monomial, smul_mul_assoc,
      pbwBasis_inl_mul_ι_inr b hfirst, map_smul, pbwPolynomialEquiv_basis]
    simp [MvPolynomial.rename_monomial, MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.smul_monomial]

section FiniteComplement

variable [Fintype β]

/-- Every actual complementary-degree-one enveloping element is a genuine linear form
in complementary generators with polynomial coefficients in the ideal variables. -/
theorem exists_metabelianLinearForm
    (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
    (a : UniversalEnvelopingAlgebra R L) (ha : a ∈ weightedUpper b complementWeight 1) :
    ∃ p0 : MvPolynomial α R, ∃ pq : β → MvPolynomial α R,
      pbwPolynomialEquiv b a = MvPolynomial.rename Sum.inl p0 +
        ∑ q, MvPolynomial.rename Sum.inl (pq q) * MvPolynomial.X (Sum.inr q) ∧
      a = idealPolynomialEval b hc p0 +
        ∑ q, idealPolynomialEval b hc (pq q) * ι R (b (.inr q)) := by
  have hp := (pbwPolynomialEquiv_mem_upper_iff b complementWeight 1 a).mpr ha
  have hpsupport : ∀ m ∈ (pbwPolynomialEquiv b a).support, Finsupp.weight complementWeight m ≤ 1 :=
    (mem_basisSupport (MvPolynomial.basisMonomials (α ⊕ β) R) _ (pbwPolynomialEquiv b a)).mp hp
  obtain ⟨p0, pq, hcoord⟩ := exists_polynomialLinearForm (pbwPolynomialEquiv b a) hpsupport
  refine ⟨p0, pq, hcoord, ?_⟩
  apply (pbwPolynomialEquiv b).injective
  simpa only [map_add, map_sum, pbwPolynomialEquiv_idealPolynomialEval,
    pbwPolynomialEquiv_idealPolynomialEval_mul_ι_inr b hc hfirst] using hcoord

end FiniteComplement

end Native

end EnvelopingIsomorphism.Identification
