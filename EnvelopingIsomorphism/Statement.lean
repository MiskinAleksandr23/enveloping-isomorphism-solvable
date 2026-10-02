import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Solvable

/-!
The proposition targeted by this project. Defining it does not prove it.
Only the source Lie algebra is assumed solvable.
-/

namespace EnvelopingIsomorphism

universe u v w

def Statement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (L : Type v) [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    (M : Type w) [LieRing M] [LieAlgebra k M] [Module.Finite k M],
    LieAlgebra.IsSolvable L →
    (UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) →
    Nonempty (L ≃ₗ⁅k⁆ M)

end EnvelopingIsomorphism
