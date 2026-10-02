import EnvelopingIsomorphism.FieldTheory.EnvelopingModel
import EnvelopingIsomorphism.FieldTheory.LieModel

/-!
# A field of definition for an actual pair of enveloping algebras

Only the two Lie structure tables and the PBW coefficients of the images of
the finitely many generators under the equivalence and its inverse are needed.
This construction can precede the identification of nilradicals and filtrations.
-/

noncomputable section

namespace EnvelopingIsomorphism.FieldTheory

open UniversalEnvelopingAlgebra
open EnvelopingModel
open scoped TensorProduct

variable {k L M : Type*} [Field k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  {n m : ℕ}

/-- All coefficients of a finite Lie structure table. -/
def lieStructureCoefficientSet (b : Module.Basis (Fin n) k L) : Finset k := by
  classical
  exact Finset.univ.image (fun p : Fin n × Fin n × Fin n => b.repr ⁅b p.1, b p.2.1⁆ p.2.2)

theorem mem_lieStructureCoefficientSet (b : Module.Basis (Fin n) k L) (i j a : Fin n) :
    b.repr ⁅b i, b j⁆ a ∈ lieStructureCoefficientSet b := by
  classical
  exact Finset.mem_image.mpr ⟨(i, j, a), Finset.mem_univ _, rfl⟩

/-- The finite data needed to descend both Lie algebras and the actual equivalence. -/
def pairCoefficientSet (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) : Finset k := by
  classical
  exact (lieStructureCoefficientSet b ∪ lieStructureCoefficientSet c) ∪
    ((Finset.univ.biUnion fun i => pbwCoefficientSet c (φ (ι k (b i)))) ∪
      (Finset.univ.biUnion fun j => pbwCoefficientSet b (φ.symm (ι k (c j)))))

variable [CharZero k]

/-- A single finitely generated coefficient field for the full input pair. -/
def pairCoefficientField (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    IntermediateField ℚ k :=
  coefficientField (pairCoefficientSet b c φ)

theorem mem_pairCoefficientField (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    {a : k} (ha : a ∈ pairCoefficientSet b c φ) : a ∈ pairCoefficientField b c φ :=
  mem_coefficientField ha

theorem source_structure_mem_pairCoefficientField (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) (i j a : Fin n) :
    b.repr ⁅b i, b j⁆ a ∈ pairCoefficientField b c φ := by
  classical
  apply mem_pairCoefficientField
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_union.mpr (Or.inl (mem_lieStructureCoefficientSet b i j a)))

theorem target_structure_mem_pairCoefficientField (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) (i j a : Fin m) :
    c.repr ⁅c i, c j⁆ a ∈ pairCoefficientField b c φ := by
  classical
  apply mem_pairCoefficientField
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_union.mpr (Or.inr (mem_lieStructureCoefficientSet c i j a)))

theorem forward_coefficients_mem_pairCoefficientField (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (i : Fin n) {a : k} (ha : a ∈ pbwCoefficientSet c (φ (ι k (b i)))) :
    a ∈ pairCoefficientField b c φ := by
  classical
  apply mem_pairCoefficientField
  apply Finset.mem_union.mpr
  exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)))

theorem inverse_coefficients_mem_pairCoefficientField (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (j : Fin m) {a : k} (ha : a ∈ pbwCoefficientSet b (φ.symm (ι k (c j)))) :
    a ∈ pairCoefficientField b c φ := by
  classical
  apply mem_pairCoefficientField
  apply Finset.mem_union.mpr
  exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))

instance pairCoefficientField_countable (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Countable (pairCoefficientField b c φ) :=
  coefficientField_countable (pairCoefficientSet b c φ)

theorem pairCoefficientField_fg (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    (pairCoefficientField b c φ).FG :=
  coefficientField_fg (pairCoefficientSet b c φ)

/-- The field of definition of the entire input pair has an actual complex embedding. -/
def pairCoefficientFieldEmbedding (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    pairCoefficientField b c φ →+* ℂ :=
  complexEmbeddingOfCountable (pairCoefficientField b c φ)

theorem pairCoefficientFieldEmbedding_injective (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Function.Injective (pairCoefficientFieldEmbedding b c φ) :=
  (pairCoefficientFieldEmbedding b c φ).injective

/-- The source Lie algebra over the coefficient field of the entire input pair. -/
abbrev PairSourceModel (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :=
  LieModel.Model b (pairCoefficientField b c φ) (source_structure_mem_pairCoefficientField b c φ)

/-- The target Lie algebra over the same coefficient field. -/
abbrev PairTargetModel (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :=
  LieModel.Model c (pairCoefficientField b c φ) (target_structure_mem_pairCoefficientField b c φ)

def pairSourceBasis (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Module.Basis (Fin n) (pairCoefficientField b c φ) (PairSourceModel b c φ) :=
  LieModel.basis b (pairCoefficientField b c φ) (source_structure_mem_pairCoefficientField b c φ)

def pairTargetBasis (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Module.Basis (Fin m) (pairCoefficientField b c φ) (PairTargetModel b c φ) :=
  LieModel.basis c (pairCoefficientField b c φ) (target_structure_mem_pairCoefficientField b c φ)

/-- Scalar extension of the source model recovers the original source Lie algebra. -/
def pairSourceBaseChangeEquiv (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    k ⊗[pairCoefficientField b c φ] PairSourceModel b c φ ≃ₗ⁅k⁆ L :=
  LieModel.baseChangeEquiv b (pairCoefficientField b c φ)
    (source_structure_mem_pairCoefficientField b c φ)

/-- Scalar extension of the target model recovers the original target Lie algebra. -/
def pairTargetBaseChangeEquiv (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    k ⊗[pairCoefficientField b c φ] PairTargetModel b c φ ≃ₗ⁅k⁆ M :=
  LieModel.baseChangeEquiv c (pairCoefficientField b c φ)
    (target_structure_mem_pairCoefficientField b c φ)

/-- The actual input equivalence descends to the coefficient models, with exact scalar extension. -/
theorem exists_pairModelEquiv (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    ∃ ψ : UniversalEnvelopingAlgebra (pairCoefficientField b c φ) (PairSourceModel b c φ) ≃ₐ[
        pairCoefficientField b c φ]
        UniversalEnvelopingAlgebra (pairCoefficientField b c φ) (PairTargetModel b c φ),
      extendEquiv (pairSourceBaseChangeEquiv b c φ) (pairTargetBaseChangeEquiv b c φ) ψ = φ := by
  have hL (i : Fin n) : pairSourceBaseChangeEquiv b c φ
      (1 ⊗ₜ[pairCoefficientField b c φ] pairSourceBasis b c φ i) = b i :=
    LieModel.baseChangeEquiv_one_tmul_basis _ _ _ i
  have hM (j : Fin m) : pairTargetBaseChangeEquiv b c φ
      (1 ⊗ₜ[pairCoefficientField b c φ] pairTargetBasis b c φ j) = c j :=
    LieModel.baseChangeEquiv_one_tmul_basis _ _ _ j
  have hφ (i : Fin n) (a : k) (ha : a ∈ pbwCoefficientSet c (φ (ι k (b i)))) :
      a ∈ Set.range (algebraMap (pairCoefficientField b c φ) k) :=
    ⟨⟨a, forward_coefficients_mem_pairCoefficientField b c φ i ha⟩, rfl⟩
  have hφinv (j : Fin m) (a : k) (ha : a ∈ pbwCoefficientSet b (φ.symm (ι k (c j)))) :
      a ∈ Set.range (algebraMap (pairCoefficientField b c φ) k) :=
    ⟨⟨a, inverse_coefficients_mem_pairCoefficientField b c φ j ha⟩, rfl⟩
  obtain ⟨ψ, hψ, _⟩ := exists_descendedEquiv_of_coefficients
    (pairSourceBasis b c φ) b (pairTargetBasis b c φ) c
    (pairSourceBaseChangeEquiv b c φ) (pairTargetBaseChangeEquiv b c φ) hL hM φ hφ hφinv
  exact ⟨ψ, extendEquiv_eq_of_evaluate (pairSourceBasis b c φ) b
    (pairSourceBaseChangeEquiv b c φ) (pairTargetBaseChangeEquiv b c φ) hL φ ψ hψ⟩

/-- A chosen, genuinely constructed equivalence over the small coefficient field. -/
def descendedPairEquiv (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    UniversalEnvelopingAlgebra (pairCoefficientField b c φ) (PairSourceModel b c φ) ≃ₐ[
      pairCoefficientField b c φ]
      UniversalEnvelopingAlgebra (pairCoefficientField b c φ) (PairTargetModel b c φ) :=
  Classical.choose (exists_pairModelEquiv b c φ)

@[simp]
theorem extend_descendedPairEquiv (b : Module.Basis (Fin n) k L)
    (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    extendEquiv (pairSourceBaseChangeEquiv b c φ) (pairTargetBaseChangeEquiv b c φ)
      (descendedPairEquiv b c φ) = φ :=
  Classical.choose_spec (exists_pairModelEquiv b c φ)

/-- Source solvability is retained by the model over the smaller field. -/
theorem pairSourceModel_isSolvable [LieAlgebra.IsSolvable L]
    (b : Module.Basis (Fin n) k L) (c : Module.Basis (Fin m) k M)
    (φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    LieAlgebra.IsSolvable (PairSourceModel b c φ) := inferInstance

end EnvelopingIsomorphism.FieldTheory
