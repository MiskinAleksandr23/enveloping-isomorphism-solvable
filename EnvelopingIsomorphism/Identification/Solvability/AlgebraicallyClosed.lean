import EnvelopingIsomorphism.Identification.Solvability.AbelianExtension
import EnvelopingIsomorphism.Identification.Solvability.Eigenline

/-! Identification of solvability over an algebraically closed field. The proof builds
the invariant flag implicitly, by quotienting successive common eigenlines. -/

namespace EnvelopingIsomorphism.Identification

universe u v w
variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [LieAlgebra.IsSolvable L]

omit [CharZero k] [IsAlgClosed k] in
theorem finrank_quotient_lt_of_nonzero_ideal
    {M : Type w} [LieRing M] [LieAlgebra k M] [Module.Finite k M]
    (I : LieIdeal k M) (hI : I ≠ ⊥) :
    Module.finrank k (M ⧸ I) < Module.finrank k M := by
  haveI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot k M M).mpr hI
  have h := I.toSubmodule.finrank_quotient_add_finrank
  have hpos := Module.finrank_pos (R := k) (M := I)
  change Module.finrank k (M ⧸ I) + Module.finrank k I = Module.finrank k M at h
  omega

/-- A finite-dimensional target is solvable if its enveloping algebra is an
algebra quotient of the enveloping algebra of a solvable Lie algebra. This
version assumes an algebraically closed field, and needs no PBW theorem. -/
theorem isSolvable_of_surjective_enveloping_of_isAlgClosed
    (M : Type w) [LieRing M] [LieAlgebra k M] [Module.Finite k M]
    (Φ : UniversalEnvelopingAlgebra k L →ₐ[k] UniversalEnvelopingAlgebra k M)
    (hΦ : Function.Surjective Φ) : LieAlgebra.IsSolvable M := by
  classical
  obtain hM | hM := subsingleton_or_nontrivial M
  · infer_instance
  · obtain ⟨I, hI, habel⟩ := exists_nonzero_abelianIdeal_of_surjective_enveloping Φ hΦ
    haveI : LieAlgebra.IsSolvable (M ⧸ I) :=
      isSolvable_of_surjective_enveloping_of_isAlgClosed (M ⧸ I)
        ((EnvelopingIsomorphism.Enveloping.map (quotientLieHom I)).comp Φ)
        ((EnvelopingIsomorphism.Enveloping.map_surjective (quotientLieHom I)
          (quotientLieHom_surjective I)).comp hΦ)
    exact isSolvable_of_abelianIdeal_quotient I habel
termination_by Module.finrank k M
decreasing_by exact finrank_quotient_lt_of_nonzero_ideal I hI

end EnvelopingIsomorphism.Identification
