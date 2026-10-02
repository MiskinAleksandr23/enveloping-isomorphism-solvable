import EnvelopingIsomorphism.Deformation.MainCanonicalScalarBoundary
import EnvelopingIsomorphism.Deformation.MixedCanonicalScalarBoundary
import EnvelopingIsomorphism.SignedScalarBoundaryReduction

/-! The solvable enveloping-algebra isomorphism theorem, using the
proved real graph boundary identities and the actual signed correction. -/
namespace EnvelopingIsomorphism
universe u v w

/-- For arbitrary characteristic-zero fields, an ordinary enveloping-algebra
isomorphism determines a finite-dimensional solvable source Lie algebra. -/
theorem statement : Statement.{u,v,w} :=
  statement_of_signed_real_scalar_boundary_relations
    Deformation.MainCanonicalScalarBoundary.canonicalScalarBoundaryRelation
    Deformation.MixedCanonicalScalarBoundary.signedCanonicalScalarMixedBoundaryRelation

/-- An explicit native Mathlib interface to the identification theorem. -/
theorem lieEquiv_of_envelopingAlgEquiv
    (k : Type u) [Field k] [CharZero k]
    (L : Type v) [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    (M : Type w) [LieRing M] [LieAlgebra k M] [Module.Finite k M]
    (hL : LieAlgebra.IsSolvable L)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M) :
    Nonempty (L ≃ₗ⁅k⁆ M) :=
  statement k L M hL Φ

end EnvelopingIsomorphism
