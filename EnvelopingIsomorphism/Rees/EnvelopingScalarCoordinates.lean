import EnvelopingIsomorphism.Enveloping.BaseChange
import EnvelopingIsomorphism.PBW.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension and native PBW coordinates

The base-change equivalence for enveloping algebras carries the actual
scalar-extended PBW basis to the scalar extension of the original PBW basis.
All coefficient formulas below concern ordinary algebraic tensor products.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.EnvelopingScalarCoordinates

open Module
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {L M α β : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Scalar extension of an actual enveloping-algebra equivalence. -/
def baseChangeAlgEquiv
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) :
    UniversalEnvelopingAlgebra S (S ⊗[R] L) ≃ₐ[S]
      UniversalEnvelopingAlgebra S (S ⊗[R] M) :=
  (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) Φ).trans
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S M).symm)

theorem baseChangeAlgEquiv_ι_tmul
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (s : S) (x : L) :
    baseChangeAlgEquiv R S Φ (UniversalEnvelopingAlgebra.ι S (s ⊗ₜ[R] x)) =
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S M).symm
        (s ⊗ₜ[R] Φ (UniversalEnvelopingAlgebra.ι R x)) := by
  simp only [baseChangeAlgEquiv, AlgEquiv.trans_apply,
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv_ι_tmul]
  rfl

section PBWBasis

variable [LinearOrder α] (b : Basis α R L)

omit [LinearOrder α] in
theorem baseChangeEquiv_word (w : List α) :
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L
      ((w.map (UniversalEnvelopingAlgebra.ι S ∘ b.baseChange S)).prod) =
        (1 : S) ⊗ₜ[R] ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod) := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one]
    rfl
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Function.comp_apply,
      Basis.baseChange_apply, EnvelopingIsomorphism.Enveloping.baseChangeEquiv_ι_tmul, ih,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

@[simp] theorem baseChangeEquiv_pbwBasis (m : α →₀ ℕ) :
    EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L (PBW.pbwBasis (b.baseChange S) m) =
      (1 : S) ⊗ₜ[R] PBW.pbwBasis b m := by
  simpa only [PBW.pbwBasis_apply] using baseChangeEquiv_word R S b (PBW.orderedWord m)

/-- The two native constructions of the scalar-extended PBW basis agree. -/
theorem pbwBasis_map_baseChangeEquiv :
    (PBW.pbwBasis (b.baseChange S)).map
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).toLinearEquiv =
        (PBW.pbwBasis b).baseChange S := by
  apply DFunLike.ext
  intro m
  rw [Basis.map_apply, Basis.baseChange_apply]
  exact baseChangeEquiv_pbwBasis R S b m

/-- Every PBW coefficient is extended by the scalar algebra map. -/
theorem pbwCoeff_baseChange_symm_tmul (s : S) (a : UniversalEnvelopingAlgebra R L)
    (m : α →₀ ℕ) :
    (PBW.pbwBasis (b.baseChange S)).repr
      ((EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).symm (s ⊗ₜ[R] a)) m =
        s * algebraMap R S ((PBW.pbwBasis b).repr a m) := by
  calc
    _ = ((PBW.pbwBasis (b.baseChange S)).map
        (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).toLinearEquiv).repr
          (s ⊗ₜ[R] a) m := rfl
    _ = ((PBW.pbwBasis b).baseChange S).repr (s ⊗ₜ[R] a) m := by
      rw [pbwBasis_map_baseChangeEquiv]
    _ = _ := by rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

@[simp] theorem pbwCoeff_baseChange_symm_one_tmul (a : UniversalEnvelopingAlgebra R L)
    (m : α →₀ ℕ) :
    (PBW.pbwBasis (b.baseChange S)).repr
      ((EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S L).symm (1 ⊗ₜ[R] a)) m =
        algebraMap R S ((PBW.pbwBasis b).repr a m) := by
  rw [pbwCoeff_baseChange_symm_tmul, one_mul]

end PBWBasis

section EquivalenceCoefficients

variable [LinearOrder α] [LinearOrder β] (bL : Basis α R L) (bM : Basis β R M)

theorem baseChangeAlgEquiv_pbwBasis
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M) (m : α →₀ ℕ) :
    baseChangeAlgEquiv R S Φ (PBW.pbwBasis (bL.baseChange S) m) =
      (EnvelopingIsomorphism.Enveloping.baseChangeEquiv R S M).symm
        (1 ⊗ₜ[R] Φ (PBW.pbwBasis bL m)) := by
  simp only [baseChangeAlgEquiv, AlgEquiv.trans_apply, baseChangeEquiv_pbwBasis]
  rfl

/-- Scalar extension of an algebra equivalence preserves its actual PBW matrix. -/
theorem pbwCoeff_baseChangeAlgEquiv
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (p : α →₀ ℕ) (q : β →₀ ℕ) :
    (PBW.pbwBasis (bM.baseChange S)).repr
      (baseChangeAlgEquiv R S Φ (PBW.pbwBasis (bL.baseChange S) p)) q =
        algebraMap R S ((PBW.pbwBasis bM).repr (Φ (PBW.pbwBasis bL p)) q) := by
  rw [baseChangeAlgEquiv_pbwBasis, pbwCoeff_baseChange_symm_one_tmul]

/-- In particular, this is the coefficient formula for each original Lie generator. -/
theorem pbwCoeff_baseChangeAlgEquiv_generator
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (i : α) (q : β →₀ ℕ) :
    (PBW.pbwBasis (bM.baseChange S)).repr
      (baseChangeAlgEquiv R S Φ (UniversalEnvelopingAlgebra.ι S (1 ⊗ₜ[R] bL i))) q =
        algebraMap R S ((PBW.pbwBasis bM).repr (Φ (UniversalEnvelopingAlgebra.ι R (bL i))) q) := by
  simpa only [PBW.pbwBasis_single, Basis.baseChange_apply] using
    pbwCoeff_baseChangeAlgEquiv R S bL bM Φ (Finsupp.single i 1) q

end EquivalenceCoefficients

end EnvelopingIsomorphism.Rees.EnvelopingScalarCoordinates
