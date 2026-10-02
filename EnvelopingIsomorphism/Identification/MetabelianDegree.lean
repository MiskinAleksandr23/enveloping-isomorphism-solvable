import EnvelopingIsomorphism.Identification.MetabelianAffine
import EnvelopingIsomorphism.Identification.EigenvectorSymbol

/-! The first hard HQ2 step: LF elements have complementary degree at most one. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra EnvelopingIsomorphism.PBW
open EnvelopingIsomorphism.Enveloping (complementWeight)

variable {k L Q α β J : Type*} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [AddCommGroup Q] [Module k Q]
  [Fintype α] [Fintype β] [LinearOrder (α ⊕ β)]
  (b : Module.Basis (α ⊕ β) k L) (bQ : Module.Basis β k Q)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The first hard HQ2 degree bound. Its inputs are actual common eigenvectors,
separating quotient weights, and the concrete bracket support of an abelian
extension; the leading-symbol identity is supplied by the proved native PBW theorem. -/
theorem locallyFinite_complementDegree_le_one
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 →
      complementWeight a < complementWeight i + complementWeight j)
    (χ : J → LieAlgebra.LieCharacter k L) (ψ : J → Q →ₗ[k] k)
    (hψ : ∀ q, (∀ j, ψ j q = 0) → q = 0)
    (hχ0 : ∀ (j : J) (i : α), χ j (b (.inl i)) = 0)
    (hχ1 : ∀ (j : J) (i : β), χ j (b (.inr i)) = ψ j (bQ i))
    (w : J → L) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, w j⁆ = χ j x • w j)
    (hw0 : ∀ j, ι k (w j) ∈ weightedUpper b complementWeight 0)
    {a : UniversalEnvelopingAlgebra k L} (hLF : a ∈ LF k (UniversalEnvelopingAlgebra k L)) :
    a ∈ weightedUpper b complementWeight 1 := by
  classical
  let ω : α ⊕ β → ℕ := complementWeight
  have hω : ∀ i, ω i = 0 ∨ ω i = 1 := by
    intro i
    cases i <;> simp [ω, complementWeight]
  have hχ (j : J) : ∀ i, ω i = 0 → χ j (b i) = 0 := by
    intro i hi
    cases i with
    | inl i => exact hχ0 j i
    | inr i => simp [ω, complementWeight] at hi
  let wp := fun j => pbwPolynomialEquiv b (ι k (w j))
  have hwp (j : J) : wp j ≠ 0 := by
    intro h
    apply hw j
    apply ι_injective_of_basis b
    apply (pbwPolynomialEquiv b).injective
    simpa only [map_zero] using h
  have hτ : ∀ i : α ⊕ β, ω i ≠ 0 → ∃ j : β, Sum.inr j = i := by
    intro i hi
    cases i with
    | inl i => simp [ω, complementWeight] at hi
    | inr i => exact ⟨i, rfl⟩
  obtain ⟨m, hm⟩ := exists_mem_weightedUpper b ω a
  suffices h : ∀ m, a ∈ weightedUpper b ω m → a ∈ weightedUpper b ω 1 from h m hm
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro ha
    by_cases hm : m ≤ 1
    · exact weightedUpper_mono b ω hm ha
    have hm1 : 1 < m := Nat.lt_of_not_ge hm
    let D := pbwLeadingDerivationOfUpper b ω hc a m (Nat.zero_lt_of_lt hm1) ha
    have hD : IsLocallyNilpotent D.toLinearMap :=
      pbwLeadingDerivationOfUpper_isLocallyNilpotent b ω hc a m hm1 ha hLF
    let p := MvPolynomial.weightedHomogeneousComponent ω m (pbwPolynomialEquiv b a)
    have htop : p = 0 := by
      apply homogeneous_eq_zero_of_locallyNilpotent_weight_formula bQ ψ hψ ω Sum.inr hτ
        D hD wp hwp (Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hm1))
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous m _)
      intro j
      change pbwLeadingDerivationOfUpper b ω hc a m (Nat.zero_lt_of_lt hm1) ha
        (pbwPolynomialEquiv b (ι k (w j))) = _
      rw [pbwLeadingDerivationOfUpper_eigenvector b ω hω hc (χ j) (hχ j) (w j)
        (heigen j) (hw0 j) a m (Nat.zero_lt_of_lt hm1) ha]
      congr 1
      rw [Fintype.sum_sum_type]
      simp only [hχ0, hχ1, zero_smul, Finset.sum_const_zero, zero_add]
    have hstrict := weightedComponent_remainder_strict ω m
      ((pbwPolynomialEquiv_mem_upper_iff b ω m a).mpr ha)
    change pbwPolynomialEquiv b a - p ∈ _ at hstrict
    rw [htop, sub_zero] at hstrict
    apply ih (m - 1) (by omega)
    apply (pbwPolynomialEquiv_mem_upper_iff b ω (m - 1) a).mp
    apply basisSupport_mono (MvPolynomial.basisMonomials (α ⊕ β) k) _ hstrict
    intro n hn
    change Finsupp.weight ω n ≤ m - 1
    change Finsupp.weight ω n < m at hn
    omega

end EnvelopingIsomorphism.Identification
