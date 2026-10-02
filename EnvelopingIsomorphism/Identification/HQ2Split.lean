import EnvelopingIsomorphism.Identification.MetabelianDegree
import EnvelopingIsomorphism.Identification.IdealVectorFields
import EnvelopingIsomorphism.Identification.MetabelianLinearForm

/-! Full HQ2 over a field with actual separating common eigenweights. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra EnvelopingIsomorphism.PBW
open EnvelopingIsomorphism.Enveloping (complementWeight)
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k L Q α β J : Type*} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [AddCommGroup Q] [Module k Q]
  [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder (α ⊕ β)]
  (b : Module.Basis (α ⊕ β) k L) (bQ : Module.Basis β k Q)
  (H : LieIdeal k L) [IsLieAbelian H]
  (hH : (H : Submodule k L) = Submodule.span k (Set.range (fun i : α => b (.inl i))))
  (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
  (χ : J → LieAlgebra.LieCharacter k L) (ψ : J → Q →ₗ[k] k)
  (hψ : ∀ q, (∀ j, ψ j q = 0) → q = 0)
  (hχ0 : ∀ (j : J) (i : α), χ j (b (.inl i)) = 0)
  (hχ1 : ∀ (j : J) (i : β), χ j (b (.inr i)) = ψ j (bQ i))
  (w : J → L) (hwH : ∀ j, w j ∈ H) (hw : ∀ j, w j ≠ 0)
  (heigen : ∀ j x, ⁅x, w j⁆ = χ j x • w j)

include bQ hH hψ hχ0 hχ1 in
omit [CharZero k] [LinearOrder α] [LinearOrder (α ⊕ β)] [IsLieAbelian H] in
theorem mem_ideal_of_all_weights_zero {x : L} (hx : ∀ j, χ j x = 0) : x ∈ H := by
  classical
  have hq : (∑ i : β, b.repr x (.inr i) • bQ i) = 0 := by
    apply hψ
    intro j
    have h := congrArg (χ j) (b.sum_repr x)
    rw [map_sum, Fintype.sum_sum_type] at h
    simpa only [map_sum, map_smul, hχ0, hχ1, smul_zero, Finset.sum_const_zero, zero_add,
      hx j] using h
  have hcoeff (i : β) : b.repr x (.inr i) = 0 := by
    have h := congrArg (fun q => bQ.repr q i) hq
    simpa [Finsupp.single_apply] using h
  change x ∈ (H : Submodule k L)
  rw [basisSupport_ideal b H hH]
  apply (mem_basisSupport b _ x).mpr
  intro i hi
  cases i with
  | inl i => exact ⟨i, rfl⟩
  | inr i => exact (Finsupp.mem_support_iff.mp hi (hcoeff i)).elim

include bQ hH hfirst hψ hχ0 hχ1 hwH hw heigen in
/-- Complete hard and easy LF directions, with the real polynomial subalgebra. -/
theorem mem_LF_iff_linear_add_polynomial_of_split_weights
    (a : UniversalEnvelopingAlgebra k L) :
    a ∈ LF k (UniversalEnvelopingAlgebra k L) ↔
      ∃ x : L, ∃ p : UniversalEnvelopingAlgebra k L,
        p ∈ idealPolynomialPart H ∧ a = ι k x + p := by
  classical
  constructor
  · intro hLF
    let hc := complementWeight_bracket_strict b H hH
    have hw0 (j : J) : ι k (w j) ∈ weightedUpper b complementWeight 0 := by
      rw [← EnvelopingIsomorphism.Enveloping.idealPolynomialPart_eq_complementDegree_zero b H hH]
      exact ι_mem_idealPolynomialPart H (hwH j)
    have hdeg := locallyFinite_complementDegree_le_one b bQ hc χ ψ hψ hχ0 hχ1
      w hw heigen hw0 hLF
    obtain ⟨p₀, p, _, ha⟩ := exists_metabelianLinearForm b hc hfirst a hdeg
    let φ := idealPolynomialEval b hc
    have hφX : ∀ i, φ (MvPolynomial.X i) = ι k (b (.inl i)) := idealPolynomialEval_X b hc
    have he (i : β) (j : J) : ⁅b (.inr i), w j⁆ = ψ j (bQ i) • w j := by
      rw [heigen, hχ1]
    have hcoeff := affine_coefficients_constant_of_locallyFinite b H hH φ hφX
      (idealPolynomialEval_injective b hc) bQ ψ hψ w hwH hw he p p₀ (by rw [← ha]; exact hLF)
    refine ⟨∑ i, MvPolynomial.coeff 0 (p i) • b (.inr i), φ p₀,
      idealPolynomialEval_mem b hc H hH p₀, ?_⟩
    rw [ha, map_sum]
    simp only [map_smul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [hcoeff i]
    change idealPolynomialEval b hc (algebraMap k (MvPolynomial α k) (MvPolynomial.coeff 0 (p i))) *
      ι k (b (.inr i)) = MvPolynomial.coeff 0 (p i) • ι k (b (.inr i))
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  · rintro ⟨x, p, hp, rfl⟩
    exact affine_idealPolynomialPart_mem_LF b H hH x hp

include bQ hH hfirst hψ hχ0 hχ1 hwH hw heigen in
/-- Complete LN equality, without augmentation or any preservation assumption. -/
theorem mem_LN_iff_polynomial_of_split_weights
    (a : UniversalEnvelopingAlgebra k L) :
    a ∈ LN k (UniversalEnvelopingAlgebra k L) ↔ a ∈ idealPolynomialPart H := by
  constructor
  · intro hLN
    obtain ⟨x, p, hp, ha⟩ :=
      (mem_LF_iff_linear_add_polynomial_of_split_weights b bQ H hH hfirst χ ψ hψ
        hχ0 hχ1 w hwH hw heigen a).mp (LN_subset_LF hLN)
    have hweights (j : J) : χ j x = 0 := by
      by_contra hj
      have hιw : ι k (w j) ≠ 0 := by
        intro h
        exact hw j (ι_injective_of_basis b (h.trans (map_zero (ι k)).symm))
      apply not_locallyNilpotent_of_eigenvector (LieAlgebra.ad k _ a) hιw hj _ hLN
      change ⁅a, ι k (w j)⁆ = χ j x • ι k (w j)
      rw [ha, add_lie, lie_eq_zero_of_mem_idealPolynomialPart H hp
        (ι_mem_idealPolynomialPart H (hwH j)), add_zero, ← LieHom.map_lie, heigen, map_smul]
    have hx := mem_ideal_of_all_weights_zero b bQ H hH χ ψ hψ hχ0 hχ1 hweights
    rw [ha]
    exact add_mem (ι_mem_idealPolynomialPart H hx) hp
  · intro ha
    exact idealPolynomialPart_subset_LN H ha

end EnvelopingIsomorphism.Identification
