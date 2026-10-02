import EnvelopingIsomorphism.PBW.Basis
import EnvelopingIsomorphism.Enveloping.UniversalProperties

/-! An enveloping equivalence which matches actual Lie basis generators is the enveloping
equivalence of their prescribed Lie equivalence. This is used after zero specialization in D3. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L M ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] [LinearOrder ι]
    (bL : Basis ι R L) (bM : Basis ι R M)
    (Φ : UniversalEnvelopingAlgebra R L ≃ₐ[R] UniversalEnvelopingAlgebra R M)
    (hΦ : ∀ i, Φ (UniversalEnvelopingAlgebra.ι R (bL i)) = UniversalEnvelopingAlgebra.ι R (bM i))

include hΦ

omit [LinearOrder ι] in
/-- Matching basis generators extends to every element of the Lie algebra by linearity. -/
theorem map_generator_of_basis (x : L) :
    Φ (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R ((bL.equiv bM (Equiv.refl ι)) x) := by
  have he : Φ.toAlgHom.toLinearMap.comp (UniversalEnvelopingAlgebra.ι R).toLinearMap =
      (UniversalEnvelopingAlgebra.ι R).toLinearMap.comp
        (bL.equiv bM (Equiv.refl ι)).toLinearMap := by
    apply bL.ext
    intro i
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LieHom.coe_toLinearMap,
      LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, AlgEquiv.coe_toAlgHom] using hΦ i
  exact LinearMap.congr_fun he x

/-- The native Lie equivalence determined by a matched enveloping-generator basis. -/
def lieEquivOfGenerators : L ≃ₗ⁅R⁆ M where
  __ := bL.equiv bM (Equiv.refl ι)
  map_lie' {x y} := by
    apply PBW.ι_injective_of_basis bM
    calc
      UniversalEnvelopingAlgebra.ι R ((bL.equiv bM (Equiv.refl ι)) ⁅x, y⁆) =
          Φ (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) := (map_generator_of_basis bL bM Φ hΦ _).symm
      _ = Φ ⁅UniversalEnvelopingAlgebra.ι R x, UniversalEnvelopingAlgebra.ι R y⁆ := by
        rw [LieHom.map_lie]
      _ = ⁅Φ (UniversalEnvelopingAlgebra.ι R x), Φ (UniversalEnvelopingAlgebra.ι R y)⁆ :=
        Φ.toAlgHom.toLieHom.map_lie _ _
      _ = ⁅UniversalEnvelopingAlgebra.ι R ((bL.equiv bM (Equiv.refl ι)) x),
          UniversalEnvelopingAlgebra.ι R ((bL.equiv bM (Equiv.refl ι)) y)⁆ := by
        rw [map_generator_of_basis bL bM Φ hΦ, map_generator_of_basis bL bM Φ hΦ]
      _ = UniversalEnvelopingAlgebra.ι R
          ⁅(bL.equiv bM (Equiv.refl ι)) x, (bL.equiv bM (Equiv.refl ι)) y⁆ :=
        (UniversalEnvelopingAlgebra.ι R).map_lie _ _ |>.symm

@[simp] theorem lieEquivOfGenerators_basis (i : ι) :
    lieEquivOfGenerators bL bM Φ hΦ (bL i) = bM i := by
  change bL.equiv bM (Equiv.refl ι) (bL i) = bM i
  exact Basis.equiv_apply _ _ _ _

/-- Its linear map is the prescribed basis identification, independently of higher UEA data. -/
@[simp] theorem lieEquivOfGenerators_toLinearEquiv :
    (lieEquivOfGenerators bL bM Φ hΦ).toLinearEquiv = bL.equiv bM (Equiv.refl ι) := rfl

/-- Matching generators determines the entire enveloping equivalence, not merely its first jet. -/
theorem eq_congr_lieEquivOfGenerators :
    Φ = EnvelopingIsomorphism.Enveloping.congr (lieEquivOfGenerators bL bM Φ hΦ) := by
  have he : Φ.toAlgHom =
      (EnvelopingIsomorphism.Enveloping.congr (lieEquivOfGenerators bL bM Φ hΦ)).toAlgHom := by
    apply EnvelopingIsomorphism.Enveloping.hom_ext_ι
    intro x
    change Φ (UniversalEnvelopingAlgebra.ι R x) =
      EnvelopingIsomorphism.Enveloping.congr (lieEquivOfGenerators bL bM Φ hΦ)
        (UniversalEnvelopingAlgebra.ι R x)
    rw [EnvelopingIsomorphism.Enveloping.congr_ι]
    exact map_generator_of_basis bL bM Φ hΦ x
  exact AlgEquiv.ext (AlgHom.congr_fun he)

end EnvelopingIsomorphism.Rees
