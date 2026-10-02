import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality

/-!
# Small coefficient fields

A finite set of coefficients in an arbitrary characteristic-zero field lies
in a countable subfield finitely generated over the rationals. Embeddings
into the complex numbers will be constructed only for this small subfield.
-/

noncomputable section

namespace EnvelopingIsomorphism.FieldTheory

/-- Send a transcendence basis to an algebraically independent family, then
extend across the remaining algebraic extension into an algebraically closed field. -/
def embeddingOfTranscendenceBasis
    {F E K ι : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [IsAlgClosed K] {x : ι → E} {y : ι → K}
    (hx : IsTranscendenceBasis F x) (hy : AlgebraicIndependent F y) : E →+* K := by
  let F₀ := IntermediateField.adjoin F (Set.range x)
  let g : F₀ →+* K :=
    ((IntermediateField.val _).comp
      (hx.1.aevalEquivField.symm.trans hy.aevalEquivField).toAlgHom).toRingHom
  letI : Algebra F₀ K := g.toAlgebra
  letI : Algebra.IsAlgebraic F₀ E := hx.isAlgebraic_field
  exact (IsAlgClosed.lift : E →ₐ[F₀] K).toRingHom

variable {k : Type*} [Field k] [CharZero k]

/-- Adjoining countably many elements to the rationals gives a countable field. -/
theorem countable_rat_adjoin {S : Set k} (hS : S.Countable) :
    Countable (IntermediateField.adjoin ℚ S) := by
  haveI : Countable S := hS.to_subtype
  apply Cardinal.mk_le_aleph0_iff.mp
  have h := IntermediateField.lift_cardinalMk_adjoin_le ℚ S
  apply Cardinal.lift_le_aleph0.mp
  exact h.trans (by simp)

/-- Every countable characteristic-zero field embeds into every uncountable
algebraically closed characteristic-zero field. -/
def embeddingOfCountable (k K : Type*) [Field k] [CharZero k] [Countable k]
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K] : k →+* K := by
  apply Classical.choice
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ k
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ K
  haveI : Infinite t := by
    rcases finite_or_infinite t with hfin | hinf
    · haveI := hfin
      let K₀ := IntermediateField.adjoin ℚ (Set.range (Subtype.val : t → K))
      haveI : Countable K₀ := countable_rat_adjoin (Set.countable_range _)
      haveI : Algebra.IsAlgebraic K₀ K := ht.isAlgebraic_field
      have hK : Countable K := by
        apply Cardinal.mk_le_aleph0_iff.mp
        apply Cardinal.lift_le_aleph0.mp
        exact (Algebra.IsAlgebraic.lift_cardinalMk_le_max K₀ K).trans (by simp)
      exact (not_countable hK).elim
    · exact hinf
  letI := Encodable.ofCountable s
  let e : s ↪ t :=
    ⟨fun x ↦ Infinite.natEmbedding t (Encodable.encode x),
      (Infinite.natEmbedding t).injective.comp Encodable.encode_injective⟩
  exact ⟨embeddingOfTranscendenceBasis hs (ht.1.comp e e.injective)⟩

/-- A countable characteristic-zero field embeds in the complex numbers. -/
def complexEmbeddingOfCountable (k : Type*) [Field k] [CharZero k] [Countable k] :
    k →+* ℂ := by
  haveI : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum)
  exact embeddingOfCountable k ℂ

/-- The subfield generated over the rationals by the requested coefficients. -/
def coefficientField (S : Finset k) : IntermediateField ℚ k :=
  IntermediateField.adjoin ℚ (S : Set k)

theorem mem_coefficientField {S : Finset k} {x : k} (hx : x ∈ S) :
    x ∈ coefficientField S :=
  IntermediateField.subset_adjoin ℚ _ hx

/-- Finite generation is as a field extension, allowing transcendental coefficients. -/
theorem coefficientField_fg (S : Finset k) : (coefficientField S).FG :=
  IntermediateField.fg_adjoin_finset S

instance coefficientField_countable (S : Finset k) : Countable (coefficientField S) := by
  exact countable_rat_adjoin S.countable_toSet

/-- Only the finitely generated coefficient field is embedded in `ℂ`. -/
def coefficientFieldEmbedding (S : Finset k) : coefficientField S →+* ℂ :=
  complexEmbeddingOfCountable (coefficientField S)

theorem coefficientFieldEmbedding_injective (S : Finset k) :
    Function.Injective (coefficientFieldEmbedding S) :=
  (coefficientFieldEmbedding S).injective

/-- A finite coefficient set admits a countable, finitely generated field of
definition with an actual embedding in the complex numbers. -/
theorem exists_coefficientField_embedding (S : Finset k) :
    ∃ K : IntermediateField ℚ k,
      (∀ x ∈ S, x ∈ K) ∧ K.FG ∧ Countable K ∧
        ∃ σ : K →+* ℂ, Function.Injective σ := by
  exact ⟨coefficientField S, fun _ hx ↦ mem_coefficientField hx,
    coefficientField_fg S, inferInstance, coefficientFieldEmbedding S,
    coefficientFieldEmbedding_injective S⟩

end EnvelopingIsomorphism.FieldTheory
