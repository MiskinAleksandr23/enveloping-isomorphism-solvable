import EnvelopingIsomorphism.Enveloping.Quotient
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! Native Lie quotients commute with arbitrary scalar extension.
The underlying linear equivalence uses right exactness, not flatness. -/

noncomputable section

namespace EnvelopingIsomorphism.Enveloping

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (S : Type*) [CommRing S] [Algebra R S] (I : LieIdeal R L)

/-- The standard tensor/quotient equivalence over the extended scalar ring. -/
def lieQuotientBaseChangeLinearEquiv :
    S ⊗[R] (L ⧸ I) ≃ₗ[S] (S ⊗[R] L) ⧸ I.baseChange S :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S I.toSubmodule

@[simp] theorem lieQuotientBaseChangeLinearEquiv_tmul (s : S) (x : L) :
    lieQuotientBaseChangeLinearEquiv S I (s ⊗ₜ[R] lieQuotientMap I x) =
      lieQuotientMap (I.baseChange S) (s ⊗ₜ[R] x) := rfl

private theorem zero_lie_self {V : Type*} [LieRing V] (x : V) : ⁅(0 : V), x⁆ = 0 := by
  apply add_left_cancel (a := ⁅(0 : V), x⁆)
  simpa only [zero_add, add_zero] using (LieRing.add_lie (0 : V) 0 x).symm

private theorem lie_zero_self {V : Type*} [LieRing V] (x : V) : ⁅x, (0 : V)⁆ = 0 := by
  apply add_left_cancel (a := ⁅x, (0 : V)⁆)
  simpa only [zero_add, add_zero] using (LieRing.lie_add x (0 : V) 0).symm

/-- Scalar extension commutes with the quotient as a Lie algebra, for any commutative
ring extension. No flatness, finite dimensionality, or PBW is needed. -/
def lieQuotientBaseChangeEquiv :
    S ⊗[R] (L ⧸ I) ≃ₗ⁅S⁆ (S ⊗[R] L) ⧸ I.baseChange S :=
  { lieQuotientBaseChangeLinearEquiv S I with
    map_lie' := by
      intro u v
      change lieQuotientBaseChangeLinearEquiv S I ⁅u, v⁆ =
        ⁅lieQuotientBaseChangeLinearEquiv S I u, lieQuotientBaseChangeLinearEquiv S I v⁆
      induction u using TensorProduct.induction_on with
      | zero => simp only [zero_lie_self, map_zero]
      | tmul s x =>
        obtain ⟨x, rfl⟩ := lieQuotientMap_surjective I x
        induction v using TensorProduct.induction_on with
        | zero => simp only [lie_zero_self, map_zero]
        | tmul t y =>
          obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I y
          rw [LieAlgebra.ExtendScalars.bracket_tmul, ← LieHom.map_lie,
            lieQuotientBaseChangeLinearEquiv_tmul, lieQuotientBaseChangeLinearEquiv_tmul,
            lieQuotientBaseChangeLinearEquiv_tmul, ← LieHom.map_lie,
            LieAlgebra.ExtendScalars.bracket_tmul]
        | add v w hv hw => simp only [LieRing.lie_add, map_add, hv, hw]
      | add u w hu hw => simp only [LieRing.add_lie, map_add, hu, hw] }

@[simp] theorem lieQuotientBaseChangeEquiv_tmul (s : S) (x : L) :
    lieQuotientBaseChangeEquiv S I (s ⊗ₜ[R] lieQuotientMap I x) =
      lieQuotientMap (I.baseChange S) (s ⊗ₜ[R] x) := rfl

@[simp] theorem lieQuotientBaseChangeEquiv_symm_mk_tmul (s : S) (x : L) :
    (lieQuotientBaseChangeEquiv S I).symm (lieQuotientMap (I.baseChange S) (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] lieQuotientMap I x := by
  rw [← lieQuotientBaseChangeEquiv_tmul, LieEquiv.symm_apply_apply]

end EnvelopingIsomorphism.Enveloping
