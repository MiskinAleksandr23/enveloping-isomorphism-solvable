import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient

/-! Elementary quotient and extension lemmas used in the identification of solvability. -/

namespace EnvelopingIsomorphism.Identification

universe u v
variable {k : Type u} [CommRing k]
variable {M : Type v} [LieRing M] [LieAlgebra k M]

/-- The canonical Lie homomorphism to the quotient by an ideal. -/
def quotientLieHom (I : LieIdeal k M) : M →ₗ⁅k⁆ M ⧸ I where
  toLinearMap := I.toSubmodule.mkQ
  map_lie' := rfl

theorem quotientLieHom_surjective (I : LieIdeal k M) :
    Function.Surjective (quotientLieHom I) :=
  I.toSubmodule.mkQ_surjective

@[simp] theorem quotientLieHom_ker (I : LieIdeal k M) :
    (quotientLieHom I).ker = I := by
  ext x
  exact Submodule.Quotient.mk_eq_zero I.toSubmodule

/-- An algebra with abelian ideal and solvable quotient is solvable. -/
theorem isSolvable_of_abelianIdeal_quotient (I : LieIdeal k M)
    (hI : ⁅I, I⁆ = ⊥) [LieAlgebra.IsSolvable (M ⧸ I)] :
    LieAlgebra.IsSolvable M := by
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable k (M ⧸ I)
  have hmap : (LieAlgebra.derivedSeries k M n).map (quotientLieHom I) = ⊥ := by
    rw [LieIdeal.derivedSeries_map_eq n (quotientLieHom_surjective I), hn]
  have hle : LieAlgebra.derivedSeries k M n ≤ I := by
    simpa using (LieIdeal.map_eq_bot_iff.mp hmap)
  apply LieAlgebra.IsSolvable.mk (R := k) (k := n + 1)
  apply le_antisymm _ bot_le
  simpa only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ, hI]
    using (LieSubmodule.mono_lie hle hle)

end EnvelopingIsomorphism.Identification
