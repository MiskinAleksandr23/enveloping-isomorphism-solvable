import EnvelopingIsomorphism.Identification.MetabelianBasic
import EnvelopingIsomorphism.Enveloping.UniversalProperties

/-! Naturality of the polynomial and linear-plus-polynomial parts under native Lie equivalences. -/

namespace EnvelopingIsomorphism.Identification

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- A native enveloping equivalence carries the polynomial part to the polynomial part of the image ideal. -/
theorem idealPolynomialPart_map_equiv (e : L ≃ₗ⁅R⁆ M) (H : LieIdeal R L) :
    (idealPolynomialPart H).map (Enveloping.congr e).toAlgHom =
      idealPolynomialPart (H.map e.toLieHom) := by
  simp only [idealPolynomialPart, AlgHom.map_adjoin]
  congr 1
  ext a
  constructor
  · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨e x, LieIdeal.mem_map x.property⟩, (Enveloping.congr_ι e x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective e.surjective x.property
    exact ⟨ι R (y : L), ⟨y, rfl⟩,
      (Enveloping.congr_ι e (y : L)).trans (congrArg (ι R) hy)⟩

/-- The linear Lie-generator space is carried to the linear Lie-generator space. -/
theorem generator_range_map_equiv (e : L ≃ₗ⁅R⁆ M) :
    ((ι R (L := L)).toLinearMap.range).map (Enveloping.congr e).toLinearMap =
      (ι R (L := M)).toLinearMap.range := by
  ext a
  constructor
  · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (Enveloping.congr_ι e x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨ι R (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
    simp only [AlgEquiv.toLinearMap_apply, Enveloping.congr_ι, e.apply_symm_apply]
    rfl

/-- The LF model subspace is natural under Lie equivalences. -/
theorem linearPolynomialPart_map_equiv (e : L ≃ₗ⁅R⁆ M) (H : LieIdeal R L) :
    (linearPolynomialPart H).map (Enveloping.congr e).toLinearMap =
      linearPolynomialPart (H.map e.toLieHom) := by
  rw [linearPolynomialPart, Submodule.map_sup, generator_range_map_equiv]
  have hp := congrArg Subalgebra.toSubmodule (idealPolynomialPart_map_equiv e H)
  rw [Subalgebra.map_toSubmodule] at hp
  exact congrArg (fun P => (ι R (L := M)).toLinearMap.range ⊔ P) hp

theorem mem_idealPolynomialPart_equiv_iff (e : L ≃ₗ⁅R⁆ M) (H : LieIdeal R L)
    (a : UniversalEnvelopingAlgebra R L) :
    Enveloping.congr e a ∈ idealPolynomialPart (H.map e.toLieHom) ↔ a ∈ idealPolynomialPart H := by
  rw [← idealPolynomialPart_map_equiv e H]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (Enveloping.congr e).injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem mem_linearPolynomialPart_equiv_iff (e : L ≃ₗ⁅R⁆ M) (H : LieIdeal R L)
    (a : UniversalEnvelopingAlgebra R L) :
    Enveloping.congr e a ∈ linearPolynomialPart (H.map e.toLieHom) ↔ a ∈ linearPolynomialPart H := by
  rw [← linearPolynomialPart_map_equiv e H]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (Enveloping.congr e).injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

end EnvelopingIsomorphism.Identification
