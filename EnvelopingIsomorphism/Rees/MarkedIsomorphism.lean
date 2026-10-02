import EnvelopingIsomorphism.Rees.Isomorphism
import EnvelopingIsomorphism.Rees.EnvelopingSpecialization
import EnvelopingIsomorphism.Rees.GeneratorEquivalence

/-!
# The marked zero specialization of the actual Rees equivalence

The zero-fiber Lie identification below is the prescribed linear basis identification.
The entire specialized enveloping equivalence is its enveloping map; after this fixed
identification, the specialized equivalence is the identity on the whole enveloping algebra.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.EnvelopingFamily

open Module
open scoped EnvelopingSpecialization

variable {k ι L M : Type*} [Field k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Basis ι k L} {bM : Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- Actual scalar specialization of the constructed polynomial Rees equivalence. -/
def zeroSpecialization :
    UniversalEnvelopingAlgebra k (Family.Fiber dL 0) ≃ₐ[k]
      UniversalEnvelopingAlgebra k (Family.Fiber dM 0) :=
  EnvelopingSpecialization.specialize 0 dL dM (ofLeading dL dM Φ hw hΦ hΦ')

/-- The actual specialized map is exactly the prescribed map on the common indexed generators. -/
theorem zeroSpecialization_ι_basis (i : ι) :
    zeroSpecialization dL dM Φ hw hΦ hΦ'
      (UniversalEnvelopingAlgebra.ι k (Family.fiberBasis dL 0 i)) =
        UniversalEnvelopingAlgebra.ι k (Family.fiberBasis dM 0 i) := by
  rw [zeroSpecialization, EnvelopingSpecialization.specialize_ι_basis]
  rw [ofLeading_specializes_ι_basis dL dM Φ hw hΦ hΦ'
    (EnvelopingSpecialization.evalMap 0 dM) (EnvelopingSpecialization.zero_algebraMap_X dM)]
  exact EnvelopingSpecialization.evalMap_ι_basis 0 dM i

/-- The prescribed zero-fiber basis identification is a Lie equivalence. -/
def zeroLieEquiv : Family.Fiber dL 0 ≃ₗ⁅k⁆ Family.Fiber dM 0 :=
  lieEquivOfGenerators (Family.fiberBasis dL 0) (Family.fiberBasis dM 0)
    (zeroSpecialization dL dM Φ hw hΦ hΦ') (zeroSpecialization_ι_basis dL dM Φ hw hΦ hΦ')

/-- The zero-fiber identification has the originally prescribed linear map. -/
@[simp] theorem zeroLieEquiv_toLinearEquiv :
    (zeroLieEquiv dL dM Φ hw hΦ hΦ').toLinearEquiv =
      (Family.fiberBasis dL 0).equiv (Family.fiberBasis dM 0) (Equiv.refl ι) := rfl

@[simp] theorem zeroLieEquiv_basis (i : ι) :
    zeroLieEquiv dL dM Φ hw hΦ hΦ' (Family.fiberBasis dL 0 i) = Family.fiberBasis dM 0 i :=
  lieEquivOfGenerators_basis _ _ _ _ _

/-- The identity marking holds on the whole native enveloping algebra of the zero fiber. -/
theorem zeroSpecialization_eq_congr :
    zeroSpecialization dL dM Φ hw hΦ hΦ' =
      EnvelopingIsomorphism.Enveloping.congr (zeroLieEquiv dL dM Φ hw hΦ hΦ') :=
  eq_congr_lieEquivOfGenerators _ _ _ _

/-- After the fixed basis identification, the actual zero specialization is literally the identity. -/
theorem identifiedZeroSpecialization_eq_refl :
    (zeroSpecialization dL dM Φ hw hΦ hΦ').trans
      (EnvelopingIsomorphism.Enveloping.congr (zeroLieEquiv dL dM Φ hw hΦ hΦ')).symm =
        AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  change (EnvelopingIsomorphism.Enveloping.congr (zeroLieEquiv dL dM Φ hw hΦ hΦ')).symm
    (zeroSpecialization dL dM Φ hw hΦ hΦ' a) = a
  rw [DFunLike.congr_fun (zeroSpecialization_eq_congr dL dM Φ hw hΦ hΦ') a]
  exact AlgEquiv.symm_apply_apply _ _

end EnvelopingIsomorphism.Rees.EnvelopingFamily
