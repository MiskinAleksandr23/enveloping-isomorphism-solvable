import EnvelopingIsomorphism.Rees.Homogenization

/-!
# Scalar extension of actual symmetric enveloping coordinates

The compatibility is proved from permutation averaging and rational
factorial normalization. It is not assumed as a naturality hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Rees.SymmetricScalarCoordinates

open Module Homogenization
open scoped TensorProduct BigOperators

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [IsScalarTower ℚ R S]

theorem map_inverseFactorial (n : ℕ) :
    algebraMap R S (PBW.inverseFactorial R n) = PBW.inverseFactorial S n := by
  simp only [PBW.inverseFactorial, ← IsScalarTower.algebraMap_apply]

/-- Actual permutation averaging commutes with a coefficient-compatible algebra map. -/
theorem map_averagedProduct {A B : Type*} [Ring A] [Algebra R A]
    [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) (n : ℕ) (v : Fin n → A) :
    f (PBW.averagedProduct R A n v) = PBW.averagedProduct S B n (f ∘ v) := by
  rw [PBW.averagedProduct_apply, PBW.averagedProduct_apply, map_smul, map_sum,
    ← IsScalarTower.algebraMap_smul S, map_inverseFactorial]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [map_list_prod, List.map_ofFn]
  rfl

variable {L M α β : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

section SymmetricBasis

variable [LinearOrder α] (b : Basis α R L)

theorem symBasis_eq_averagedProduct (m : α →₀ ℕ) :
    symBasis b m = PBW.averagedProduct R (UniversalEnvelopingAlgebra R L)
      (PBW.orderedWord m).length
      (fun i ↦ UniversalEnvelopingAlgebra.ι R (b ((PBW.orderedWord m).get i))) := by
  rw [symBasis_apply, PBW.symmetrizationEquiv_apply, PBW.symmetrization_basis,
    PBW.averagedWord_map]
  rfl

/-- The native base-change equivalence sends each averaged basis vector to
the scalar extension of its original averaged basis vector. -/
theorem baseChangeEquiv_symBasis (m : α →₀ ℕ) :
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L (symBasis (b.baseChange S) m) =
      (1 : S) ⊗ₜ[R] symBasis b m := by
  rw [symBasis_eq_averagedProduct, symBasis_eq_averagedProduct]
  have hmap : EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L
      (PBW.averagedProduct S _ (PBW.orderedWord m).length
        (fun i ↦ UniversalEnvelopingAlgebra.ι S (b.baseChange S ((PBW.orderedWord m).get i)))) =
      PBW.averagedProduct S _ (PBW.orderedWord m).length
        (fun i ↦ EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L
          (UniversalEnvelopingAlgebra.ι S (b.baseChange S ((PBW.orderedWord m).get i)))) :=
    map_averagedProduct S S (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).toAlgHom _ _
  rw [hmap]
  let j : UniversalEnvelopingAlgebra R L →ₐ[R] S ⊗[R] UniversalEnvelopingAlgebra R L :=
    Algebra.TensorProduct.includeRight
  change PBW.averagedProduct S _ (PBW.orderedWord m).length _ =
    j (PBW.averagedProduct R _ (PBW.orderedWord m).length _)
  rw [map_averagedProduct R S j]
  congr 1
  funext i
  simp only [Function.comp_apply, Basis.baseChange_apply,
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv_ι_tmul]
  rfl

/-- Equality of the two actual scalar-extended symmetric bases. -/
theorem symBasis_map_baseChangeEquiv :
    (symBasis (b.baseChange S)).map
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).toLinearEquiv =
        (symBasis b).baseChange S := by
  apply DFunLike.ext
  intro m
  rw [Basis.map_apply, Basis.baseChange_apply]
  exact baseChangeEquiv_symBasis R S b m

theorem symCoeff_baseChange_symm_tmul (s : S) (a : UniversalEnvelopingAlgebra R L)
    (m : α →₀ ℕ) :
    (symBasis (b.baseChange S)).repr
      ((EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).symm (s ⊗ₜ[R] a)) m =
        s * algebraMap R S ((symBasis b).repr a m) := by
  calc
    _ = ((symBasis (b.baseChange S)).map
        (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).toLinearEquiv).repr
          (s ⊗ₜ[R] a) m := rfl
    _ = ((symBasis b).baseChange S).repr (s ⊗ₜ[R] a) m := by
      rw [symBasis_map_baseChangeEquiv]
    _ = _ := by rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

@[simp] theorem symCoeff_baseChange_symm_one_tmul (a : UniversalEnvelopingAlgebra R L)
    (m : α →₀ ℕ) :
    (symBasis (b.baseChange S)).repr
      ((EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).symm (1 ⊗ₜ[R] a)) m =
        algebraMap R S ((symBasis b).repr a m) := by
  rw [symCoeff_baseChange_symm_tmul, one_mul]

end SymmetricBasis

section EquivalenceCoefficients

variable [LinearOrder α] [LinearOrder β] (bL : Basis α R L) (bM : Basis β R M)

theorem baseChangeAlgEquiv_symBasis
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) (m : α →₀ ℕ) :
    EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ (symBasis (bL.baseChange S) m) =
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S M).symm
        (1 ⊗ₜ[R] Φ (symBasis bL m)) := by
  simp only [EnvelopingScalarCoordinates.baseChangeAlgEquiv, AlgEquiv.trans_apply,
    baseChangeEquiv_symBasis]
  rfl

theorem symCoeff_baseChangeAlgEquiv
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (p : α →₀ ℕ) (q : β →₀ ℕ) :
    (symBasis (bM.baseChange S)).repr
      (EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ (symBasis (bL.baseChange S) p)) q =
        algebraMap R S ((symBasis bM).repr (Φ (symBasis bL p)) q) := by
  rw [baseChangeAlgEquiv_symBasis, symCoeff_baseChange_symm_one_tmul]

/-- The actual symmetric polynomial-coordinate matrix extends coefficientwise. -/
theorem coeff_symPolynomialMap_monomial_baseChange
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (p : α →₀ ℕ) (q : β →₀ ℕ) :
    MvPolynomial.coeff q
      (symPolynomialMap (bL.baseChange S) (bM.baseChange S)
        (EnvelopingScalarCoordinates.baseChangeAlgEquiv R S Φ) (MvPolynomial.monomial p 1)) =
      algebraMap R S (MvPolynomial.coeff q (symPolynomialMap bL bM Φ (MvPolynomial.monomial p 1))) := by
  rw [coeff_symPolynomialMap_monomial, coeff_symPolynomialMap_monomial,
    symCoeff_baseChangeAlgEquiv]

end EquivalenceCoefficients

end EnvelopingIsomorphism.Rees.SymmetricScalarCoordinates
