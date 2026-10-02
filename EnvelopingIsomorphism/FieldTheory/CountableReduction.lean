import EnvelopingIsomorphism.Statement
import EnvelopingIsomorphism.FieldTheory.DescentToCoefficientField

/-!
# Reduction of the identification problem to countable coefficient fields

This file proves a reduction, not the identification theorem itself. The hypothesis
`CountableStatement` remains a mathematical theorem to be proved elsewhere.
The original field and the two Lie carriers may live in independent universes.
-/

noncomputable section

open scoped TensorProduct

section LieBaseChange

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- Scalar extension of a Lie algebra equivalence. -/
def LieEquiv.baseChange (S : Type*) [CommRing S] [Algebra R S] (e : L ≃ₗ⁅R⁆ M) :
    S ⊗[R] L ≃ₗ⁅S⁆ S ⊗[R] M :=
  { e.toLinearEquiv.baseChange R S L M with
    map_lie' := by
      intro x y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id R S) e.toLieHom).map_lie x y }

@[simp]
theorem LieEquiv.baseChange_tmul (S : Type*) [CommRing S] [Algebra R S]
    (e : L ≃ₗ⁅R⁆ M) (s : S) (x : L) :
    e.baseChange S (s ⊗ₜ[R] x) = s ⊗ₜ[R] e x := rfl

end LieBaseChange

namespace EnvelopingIsomorphism

universe u v w

/-- The identification theorem restricted to countable fields and coordinate-sized carriers.

Both carriers may be taken in the universe of the coefficient field because
the descended models have underlying types `Fin n → K`.
-/
def CountableStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [Countable k]
    (L : Type u) [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    (M : Type u) [LieRing M] [LieAlgebra k M] [Module.Finite k M],
    LieAlgebra.IsSolvable L →
    (UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) →
    Nonempty (L ≃ₗ⁅k⁆ M)

/-- Identification over countable fields implies the full statement over arbitrary characteristic-zero fields.

The actual smaller UEA equivalence and both scalar-extension identifications
are constructed by `DescentToCoefficientField`; no descent hypothesis is added.
-/
theorem of_countable (h : CountableStatement.{u}) : Statement.{u, v, w} := by
  intro k _ _ L _ _ _ M _ _ _ hL φ
  haveI : LieAlgebra.IsSolvable L := hL
  let b := Module.finBasis k L
  let c := Module.finBasis k M
  obtain ⟨f⟩ := h (FieldTheory.pairCoefficientField b c φ)
    (FieldTheory.PairSourceModel b c φ) (FieldTheory.PairTargetModel b c φ)
    (FieldTheory.pairSourceModel_isSolvable b c φ) (FieldTheory.descendedPairEquiv b c φ)
  exact ⟨(FieldTheory.pairSourceBaseChangeEquiv b c φ).symm.trans
    ((f.baseChange k).trans (FieldTheory.pairTargetBaseChangeEquiv b c φ))⟩

end EnvelopingIsomorphism
