import EnvelopingIsomorphism.Lie.NilpotentIdealSum

/-!
# The ordinary nilradical of a Lie algebra

The ideals in this definition are nilpotent as Lie algebras in their own right.
This differs from `LieAlgebra.maxNilpotentIdeal`, which uses nilpotence of the
action of the whole ambient Lie algebra.
-/

namespace EnvelopingIsomorphism.Lie

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The supremum of the nilpotent Lie ideals, with their intrinsic Lie brackets. -/
def nilradical : LieIdeal R L :=
  sSup { I : LieIdeal R L | LieRing.IsNilpotent I }

variable {R L}

/-- Every nilpotent Lie ideal is contained in the ordinary nilradical. -/
theorem le_nilradical (I : LieIdeal R L) [LieRing.IsNilpotent I] :
    I ≤ nilradical R L :=
  le_sSup (show LieRing.IsNilpotent I from inferInstance)

/-- Nilpotence is inherited by an included Lie ideal. -/
theorem isNilpotent_of_le {I J : LieIdeal R L} (h : I ≤ J)
    [LieRing.IsNilpotent J] : LieRing.IsNilpotent I :=
  (LieIdeal.inclusion_injective h).lieAlgebra_isNilpotent

/-- The ordinary nilradical of a Noetherian Lie algebra is nilpotent. -/
instance nilradicalIsNilpotent [IsNoetherian R L] :
    LieRing.IsNilpotent (nilradical R L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | LieRing.IsNilpotent I } ⟨⊥, ?_⟩ ?_
  · exact (inferInstance : LieRing.IsNilpotent (⊥ : LieIdeal R L))
  · intro I hI J hJ
    haveI : LieRing.IsNilpotent I := hI
    haveI : LieRing.IsNilpotent J := hJ
    exact isNilpotent_sup I J

/-- The ordinary nilradical is the largest nilpotent Lie ideal. -/
theorem isNilpotent_iff_le_nilradical [IsNoetherian R L] (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ I ≤ nilradical R L := by
  constructor
  · intro h
    haveI := h
    exact le_nilradical I
  · intro h
    exact isNilpotent_of_le (R := R) (L := L) h

/-- The lower central series of an ideal, retained as ideals of the ambient algebra.

Index zero is the ideal itself; thus index `n` corresponds to the usual `γ_(n+1)`.
-/
def lowerCentralSeriesOfIdeal (I : LieIdeal R L) (n : ℕ) : LieIdeal R L :=
  (fun J : LieIdeal R L => ⁅I, J⁆)^[n] I

@[simp]
theorem lowerCentralSeriesOfIdeal_zero (I : LieIdeal R L) :
    lowerCentralSeriesOfIdeal I 0 = I := rfl

@[simp]
theorem lowerCentralSeriesOfIdeal_succ (I : LieIdeal R L) (n : ℕ) :
    lowerCentralSeriesOfIdeal I (n + 1) = ⁅I, lowerCentralSeriesOfIdeal I n⁆ :=
  Function.iterate_succ_apply' _ _ _

variable {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- Restriction of a Lie homomorphism to an ideal and its ideal image. -/
def idealMapHom (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) : I →ₗ⁅R⁆ I.map f where
  toFun x := ⟨f x, LieIdeal.mem_map x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add f (x : L) (y : L)
  map_smul' r x := by apply Subtype.ext; exact map_smul f r (x : L)
  map_lie' := by intro x y; apply Subtype.ext; exact f.map_lie x y

/-- A surjective ambient homomorphism is surjective on each ideal image. -/
theorem idealMapHom_surjective (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f)
    (I : LieIdeal R L) : Function.Surjective (idealMapHom f I) := by
  intro y
  obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hf y.property
  exact ⟨x, Subtype.ext hx⟩

/-- Images of nilpotent ideals under surjective ambient Lie maps are nilpotent. -/
theorem isNilpotent_map_of_surjective (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f)
    (I : LieIdeal R L) [LieRing.IsNilpotent I] : LieRing.IsNilpotent (I.map f) :=
  (idealMapHom_surjective f hf I).lieAlgebra_isNilpotent

/-- Surjective Lie maps carry the nilradical into the target nilradical. -/
theorem map_nilradical_le (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) :
    (nilradical R L).map f ≤ nilradical R L' := by
  rw [LieIdeal.map_le_iff_le_comap]
  apply sSup_le
  intro I hI
  haveI : LieRing.IsNilpotent I := hI
  rw [← LieIdeal.map_le_iff_le_comap]
  haveI := isNilpotent_map_of_surjective f hf I
  exact le_nilradical (I.map f)

/-- The ordinary nilradical is preserved by every Lie algebra equivalence. -/
theorem map_nilradical (e : L ≃ₗ⁅R⁆ L') :
    (nilradical R L).map e.toLieHom = nilradical R L' := by
  apply le_antisymm (map_nilradical_le e.toLieHom e.surjective)
  intro y hy
  have h : e.symm y ∈ nilradical R L :=
    map_nilradical_le e.symm.toLieHom e.symm.surjective (LieIdeal.mem_map hy)
  simpa using (LieIdeal.mem_map (f := e.toLieHom) h)

/-- Membership in the ordinary nilradical is invariant under a Lie equivalence. -/
theorem mem_nilradical_iff (e : L ≃ₗ⁅R⁆ L') (x : L) :
    e x ∈ nilradical R L' ↔ x ∈ nilradical R L := by
  constructor
  · intro hx
    have h := map_nilradical_le e.symm.toLieHom e.symm.surjective (LieIdeal.mem_map hx)
    simpa using h
  · intro hx
    exact map_nilradical_le e.toLieHom e.surjective (LieIdeal.mem_map hx)

end EnvelopingIsomorphism.Lie
