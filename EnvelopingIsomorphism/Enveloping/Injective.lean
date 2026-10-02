import EnvelopingIsomorphism.PBW.Symmetrization
import EnvelopingIsomorphism.Enveloping.UniversalProperties
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Injectivity of enveloping maps, using naturality of the existing PBW symmetrization. -/

noncomputable section

namespace EnvelopingIsomorphism.Enveloping

section SymmetricMap

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The standard functorial map of symmetric algebras. -/
def symmetricMap (f : V →ₗ[R] W) : SymmetricAlgebra R V →ₐ[R] SymmetricAlgebra R W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R W).comp f)

@[simp] theorem symmetricMap_ι (f : V →ₗ[R] W) (x : V) :
    symmetricMap f (SymmetricAlgebra.ι R V x) = SymmetricAlgebra.ι R W (f x) := by
  simp [symmetricMap]

theorem symmetricMap_injective_of_leftInverse (f : V →ₗ[R] W) (g : W →ₗ[R] V)
    (hgf : g.comp f = LinearMap.id) : Function.Injective (symmetricMap f) := by
  have h : (symmetricMap g).comp (symmetricMap f) = AlgHom.id R _ := by
    ext x
    change symmetricMap g (symmetricMap f (SymmetricAlgebra.ι R V x)) =
      SymmetricAlgebra.ι R V x
    rw [symmetricMap_ι, symmetricMap_ι]
    have hx := LinearMap.congr_fun hgf x
    exact congrArg (SymmetricAlgebra.ι R V) hx
  exact (show Function.LeftInverse (symmetricMap g) (symmetricMap f) from
    fun x ↦ DFunLike.congr_fun h x).injective

end SymmetricMap

section Naturality

variable {R L M α β : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  [LinearOrder α] [LinearOrder β]

open EnvelopingIsomorphism.PBW

theorem averagedProduct_map {A B : Type*} [Ring A] [Algebra R A]
    [Ring B] [Algebra R B] (φ : A →ₐ[R] B) (n : ℕ) (v : Fin n → A) :
    φ (averagedProduct R A n v) = averagedProduct R B n (φ ∘ v) := by
  simp [averagedProduct_apply, map_list_prod, List.map_ofFn, Function.comp_def]

/-- PBW symmetrization commutes with every Lie homomorphism. -/
theorem symmetrization_natural (b : Module.Basis α R L) (c : Module.Basis β R M)
    (f : L →ₗ⁅R⁆ M) (p : SymmetricAlgebra R L) :
    map f (symmetrization b p) = symmetrization c (symmetricMap f.toLinearMap p) := by
  have h : (map f).toLinearMap.comp (symmetrization b) =
      (symmetrization c).comp (symmetricMap f.toLinearMap).toLinearMap := by
    apply b.symmetricAlgebra.ext
    intro m
    change map f (symmetrization b (b.symmetricAlgebra m)) =
      symmetrization c (symmetricMap f.toLinearMap (b.symmetricAlgebra m))
    have hm := symmetricAlgebra_basis_wordIndex b (orderedWord m)
    rw [wordIndex_orderedWord] at hm
    rw [hm]
    have hw : (orderedWord m).map (SymmetricAlgebra.ι R L ∘ b) =
        List.ofFn (fun i ↦ SymmetricAlgebra.ι R L (b ((orderedWord m).get i))) := by
      change _ = List.ofFn ((SymmetricAlgebra.ι R L ∘ b) ∘ (orderedWord m).get)
      rw [← List.map_ofFn, List.ofFn_get]
    rw [hw]
    simp only [map_list_prod, List.map_ofFn, Function.comp_def, symmetricMap_ι]
    rw [symmetrization_prod, symmetrization_prod, averagedProduct_map]
    congr 1
    funext i
    exact map_ι f (b ((orderedWord m).get i))
  exact LinearMap.congr_fun h p

end Naturality

section Fields

variable {k L M : Type*} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  [FiniteDimensional k L] [FiniteDimensional k M]

/-- An injective Lie map induces an injective map of native enveloping algebras. -/
theorem map_injective (f : L →ₗ⁅k⁆ M) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  have hs := symmetricMap_injective_of_leftInverse f.toLinearMap g hg
  let b := Module.finBasis k L
  let c := Module.finBasis k M
  intro x y hxy
  apply (PBW.symmetrizationEquiv b).symm.injective
  apply hs
  apply (PBW.symmetrization_bijective c).injective
  rw [← symmetrization_natural b c f, ← symmetrization_natural b c f]
  simpa only [← PBW.symmetrizationEquiv_apply, LinearEquiv.apply_symm_apply] using hxy

end Fields

end EnvelopingIsomorphism.Enveloping
