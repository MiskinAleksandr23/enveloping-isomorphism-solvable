import EnvelopingIsomorphism.Identification.Solvability.AlgebraicallyClosed
import EnvelopingIsomorphism.Enveloping.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
## Solvability is detected by the associative enveloping algebra

The proof transfers the adjoint representation through the algebra map. Over an
algebraically closed field, Lie's theorem supplies a common eigenline; quotienting
successive lines gives solvability by induction on dimension. Scalar extension
and faithful descent handle an arbitrary characteristic-zero field.

No preservation of augmentation, PBW filtration, or Hopf structure is assumed.
The proof does not use PBW, or even finite dimensionality of the solvable source.
-/

namespace EnvelopingIsomorphism.Identification

open scoped TensorProduct

universe u v w
variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]
variable {M : Type w} [LieRing M] [LieAlgebra k M] [Module.Finite k M]

/-- An ordinary associative isomorphism of enveloping algebras transports
solvability from the source to the finite-dimensional target. -/
theorem isSolvable_of_enveloping_equiv [LieAlgebra.IsSolvable L]
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    LieAlgebra.IsSolvable M := by
  let K := AlgebraicClosure k
  let ΦK : UniversalEnvelopingAlgebra K (K ⊗[k] L) ≃ₐ[K]
      UniversalEnvelopingAlgebra K (K ⊗[k] M) :=
    (EnvelopingIsomorphism.Enveloping.baseChangeEquiv k K L).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) Φ).trans
        (EnvelopingIsomorphism.Enveloping.baseChangeEquiv k K M).symm)
  haveI : LieAlgebra.IsSolvable (K ⊗[k] M) :=
    isSolvable_of_surjective_enveloping_of_isAlgClosed (K ⊗[k] M)
      ΦK.toAlgHom ΦK.surjective
  exact (LieAlgebra.isSolvable_tensorProduct_iff (R := k) (A := K) (L := M)).mp
    inferInstance

/-- Solvability agrees on finite-dimensional Lie algebras whose enveloping
algebras are isomorphic as ordinary associative algebras. -/
theorem isSolvable_iff_of_enveloping_equiv [Module.Finite k L]
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    LieAlgebra.IsSolvable L ↔ LieAlgebra.IsSolvable M := by
  constructor
  · intro h
    exact isSolvable_of_enveloping_equiv Φ
  · intro h
    exact isSolvable_of_enveloping_equiv Φ.symm

end EnvelopingIsomorphism.Identification
