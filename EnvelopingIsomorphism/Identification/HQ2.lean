import EnvelopingIsomorphism.Identification.HQ2Split
import EnvelopingIsomorphism.Identification.Solvability.AbelianExtension
import EnvelopingIsomorphism.LinearAlgebra.ComplementaryQuotientBasis

/-! HQ2 with native quotient eigenweights and arbitrary linear sections. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- A linear functional on the abelian quotient pulls back to a genuine Lie character. -/
def quotientLinearCharacter (H : LieIdeal k L) [IsLieAbelian (L ⧸ H)]
    (ψ : Module.Dual k (L ⧸ H)) : LieAlgebra.LieCharacter k L where
  toLinearMap := ψ.comp (quotientLieHom H).toLinearMap
  map_lie' {x y} := by
    change ψ (quotientLieHom H ⁅x, y⁆) = ⁅ψ (quotientLieHom H x), ψ (quotientLieHom H y)⁆
    rw [LieHom.map_lie, trivial_lie_zero, map_zero]
    simp [Ring.lie_def, mul_comm]

@[simp] theorem quotientLinearCharacter_apply (H : LieIdeal k L) [IsLieAbelian (L ⧸ H)]
    (ψ : Module.Dual k (L ⧸ H)) (x : L) :
    quotientLinearCharacter H ψ x = ψ (quotientLieHom H x) := rfl

theorem linear_add_polynomial_iff_section_add_polynomial
    (H : LieIdeal k L) (s : (L ⧸ H) →ₗ[k] L)
    (hs : ∀ q, quotientLieHom H (s q) = q) (a : UniversalEnvelopingAlgebra k L) :
    (∃ x : L, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k x + p) ↔
      ∃ q : L ⧸ H, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k (s q) + p := by
  constructor
  · rintro ⟨x, p, hp, ha⟩
    let q := quotientLieHom H x
    have hdiff : x - s q ∈ H := by
      have hz : quotientLieHom H (x - s q) = 0 := by rw [map_sub, hs, sub_self]
      have hk := LieHom.mem_ker.mpr hz
      simpa only [quotientLieHom_ker] using hk
    refine ⟨q, ι k (x - s q) + p, add_mem (ι_mem_idealPolynomialPart H hdiff) hp, ?_⟩
    rw [ha, map_sub]
    abel
  · rintro ⟨q, p, hp, ha⟩
    exact ⟨s q, p, hp, ha⟩

section AdaptedBasis

variable [CharZero k] {α β J : Type*} [Fintype α] [Fintype β]
  [LinearOrder α] [LinearOrder (α ⊕ β)]
  (b : Module.Basis (α ⊕ β) k L) (H : LieIdeal k L)
  [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
  (hH : (H : Submodule k L) = Submodule.span k (Set.range (fun i : α => b (.inl i))))
  (hfirst : ∀ i : α, ∀ q : β, Sum.inl i ≤ Sum.inr q)
  (bQ : Module.Basis β k (L ⧸ H))
  (hbQ : ∀ i, bQ i = quotientLieHom H (b (.inr i)))
  (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
  (w : J → H) (hw : ∀ j, w j ≠ 0)
  (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L))

include hH hfirst bQ hbQ hψ hw heigen in
/-- HQ2 with true eigenweights of the native abelian quotient and an adapted basis. -/
theorem hq2_with_adapted_basis (a : UniversalEnvelopingAlgebra k L) :
    (a ∈ LN k (UniversalEnvelopingAlgebra k L) ↔ a ∈ idealPolynomialPart H) ∧
      (a ∈ LF k (UniversalEnvelopingAlgebra k L) ↔
        ∃ x : L, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k x + p) := by
  let χ := fun j => quotientLinearCharacter H (ψ j)
  have hψker : ∀ q, (∀ j, ψ j q = 0) → q = 0 := by
    intro q hq
    apply hψ
    funext j
    simp [hq j]
  have hχ0 (j : J) (i : α) : χ j (b (.inl i)) = 0 := by
    have hz : quotientLieHom H (b (.inl i)) = 0 := by
      apply LieHom.mem_ker.mp
      simpa only [quotientLieHom_ker] using ideal_basis_mem b H hH i
    change ψ j (quotientLieHom H (b (.inl i))) = 0
    rw [hz, map_zero]
  have hχ1 (j : J) (i : β) : χ j (b (.inr i)) = ψ j (bQ i) := by
    change ψ j (quotientLieHom H (b (.inr i))) = ψ j (bQ i)
    rw [hbQ]
  have hwL (j : J) : (w j : L) ≠ 0 := by
    intro h
    exact hw j (Subtype.ext h)
  exact ⟨mem_LN_iff_polynomial_of_split_weights b bQ H hH hfirst χ ψ hψker hχ0 hχ1
      (fun j => (w j : L)) (fun j => (w j).property) hwL heigen a,
    mem_LF_iff_linear_add_polynomial_of_split_weights b bQ H hH hfirst χ ψ hψker hχ0 hχ1
      (fun j => (w j : L)) (fun j => (w j).property) hwL heigen a⟩

end AdaptedBasis

section WithoutBasis

variable [CharZero k] [Module.Finite k L] {J : Type*}

/-- HQ2 without a chosen basis: the actual LN and LF conditions are recovered
from a finite-dimensional abelian ideal extension with separating true quotient
eigenweights. No splitting as Lie algebras, augmentation, or PBW condition is assumed. -/
theorem hq2_of_quotientEigenweights
    (H : LieIdeal k L) [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
    (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
    (w : J → H) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L))
    (a : UniversalEnvelopingAlgebra k L) :
    (a ∈ LN k (UniversalEnvelopingAlgebra k L) ↔ a ∈ idealPolynomialPart H) ∧
      (a ∈ LF k (UniversalEnvelopingAlgebra k L) ↔
        ∃ x : L, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k x + p) := by
  classical
  obtain ⟨n, m, b, hb⟩ := EnvelopingIsomorphism.Enveloping.exists_idealAdaptedBasis H
  letI := EnvelopingIsomorphism.Enveloping.idealFirstOrder (Fin n) (Fin m)
  let bQ : Module.Basis (Fin m) k (L ⧸ H) :=
    EnvelopingIsomorphism.LinearAlgebra.complementaryQuotientBasis b H.toSubmodule hb.symm
  have hbQ (i : Fin m) : bQ i = quotientLieHom H (b (.inr i)) :=
    EnvelopingIsomorphism.LinearAlgebra.complementaryQuotientBasis_apply b H.toSubmodule hb.symm i
  exact hq2_with_adapted_basis b H hb (fun i j => Sum.Lex.inl_le_inr i j)
    bQ hbQ ψ hψ w hw heigen a

theorem LN_eq_polynomialPart_of_quotientEigenweights
    (H : LieIdeal k L) [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
    (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
    (w : J → H) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L)) :
    LN k (UniversalEnvelopingAlgebra k L) = (idealPolynomialPart H : Set _) := by
  ext a
  exact (hq2_of_quotientEigenweights H ψ hψ w hw heigen a).1

theorem LF_eq_linear_add_polynomialPart_of_quotientEigenweights
    (H : LieIdeal k L) [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
    (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
    (w : J → H) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L)) :
    LF k (UniversalEnvelopingAlgebra k L) =
      {a | ∃ x : L, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k x + p} := by
  ext a
  exact (hq2_of_quotientEigenweights H ψ hψ w hw heigen a).2

theorem LF_eq_linearPolynomialPart_of_quotientEigenweights
    (H : LieIdeal k L) [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
    (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
    (w : J → H) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L)) :
    LF k (UniversalEnvelopingAlgebra k L) = (linearPolynomialPart H : Set _) := by
  ext a
  exact (hq2_of_quotientEigenweights H ψ hψ w hw heigen a).2.trans
    (mem_linearPolynomialPart_iff H a).symm

/-- The LF description for any chosen linear section, including sections
whose Lie extension cocycle is nonzero. -/
theorem LF_eq_section_add_polynomialPart_of_quotientEigenweights
    (H : LieIdeal k L) [IsLieAbelian H] [IsLieAbelian (L ⧸ H)]
    (ψ : J → Module.Dual k (L ⧸ H)) (hψ : Function.Injective (fun q j => ψ j q))
    (w : J → H) (hw : ∀ j, w j ≠ 0)
    (heigen : ∀ j x, ⁅x, (w j : L)⁆ = ψ j (quotientLieHom H x) • (w j : L))
    (s : (L ⧸ H) →ₗ[k] L) (hs : ∀ q, quotientLieHom H (s q) = q) :
    LF k (UniversalEnvelopingAlgebra k L) =
      {a | ∃ q : L ⧸ H, ∃ p, p ∈ idealPolynomialPart H ∧ a = ι k (s q) + p} := by
  ext a
  exact (hq2_of_quotientEigenweights H ψ hψ w hw heigen a).2.trans
    (linear_add_polynomial_iff_section_add_polynomial H s hs a)

end WithoutBasis
end EnvelopingIsomorphism.Identification
