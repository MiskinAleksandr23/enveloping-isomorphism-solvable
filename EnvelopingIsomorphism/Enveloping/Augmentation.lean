import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Character
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.Abel

/-!
Augmentation normalization for universal enveloping algebras (block A3).
This block works over a commutative ring: PBW, finite dimension, and
characteristic zero are unnecessary.
-/

namespace EnvelopingIsomorphism.Enveloping

open UniversalEnvelopingAlgebra

universe u v w
variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev U := UniversalEnvelopingAlgebra R L

/-- The canonical augmentation, obtained from the zero Lie character. -/
def augmentation : U R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

@[simp] theorem augmentation_ι (x : L) :
    augmentation R L (ι R x) = 0 := by
  rw [augmentation, lift_ι_apply]
  rfl

variable {R L}

/-- Negation is not an existing operation on `LieHom`, so bundle it explicitly. -/
def negCharacter (χ : LieAlgebra.LieCharacter R L) : LieAlgebra.LieCharacter R L where
  toLinearMap := -χ.toLinearMap
  map_lie' {x y} := by
    change -χ ⁅x, y⁆ = ⁅-χ x, -χ y⁆
    rw [LieAlgebra.lieCharacter_apply_lie]
    simp [LieRing.of_associative_ring_bracket, mul_comm]

@[simp] theorem negCharacter_apply (χ : LieAlgebra.LieCharacter R L) (x : L) :
    negCharacter χ x = -χ x := rfl

@[simp] theorem negCharacter_negCharacter (χ : LieAlgebra.LieCharacter R L) :
    negCharacter (negCharacter χ) = χ := by
  ext x
  simp

/-- Translation of the generators by a Lie character. -/
def translationLieHom (χ : LieAlgebra.LieCharacter R L) : L →ₗ⁅R⁆ U R L where
  toLinearMap := (ι R).toLinearMap + (Algebra.linearMap R (U R L)).comp χ.toLinearMap
  map_lie' {x y} := by
    change ι R ⁅x, y⁆ + algebraMap R (U R L) (χ ⁅x, y⁆) =
      ⁅ι R x + algebraMap R (U R L) (χ x),
        ι R y + algebraMap R (U R L) (χ y)⁆
    rw [LieAlgebra.lieCharacter_apply_lie, map_zero, add_zero, LieHom.map_lie]
    simp only [add_lie, lie_add, Algebra.algebraMap_eq_smul_one, smul_lie]
    simp [LieRing.of_associative_ring_bracket]

/-- The algebra endomorphism associated to a character. -/
def translation (χ : LieAlgebra.LieCharacter R L) : U R L →ₐ[R] U R L :=
  UniversalEnvelopingAlgebra.lift R (translationLieHom χ)

@[simp] theorem translation_ι (χ : LieAlgebra.LieCharacter R L) (x : L) :
    translation χ (ι R x) = ι R x + algebraMap R (U R L) (χ x) := by
  rw [translation, lift_ι_apply]
  rfl

theorem translation_comp_neg (χ : LieAlgebra.LieCharacter R L) :
    (translation χ).comp (translation (negCharacter χ)) = AlgHom.id R (U R L) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change translation χ (translation (negCharacter χ) (ι R x)) = ι R x
  simp only [translation_ι, map_add, AlgHom.commutes, negCharacter_apply, map_neg]
  abel

theorem translation_neg_comp (χ : LieAlgebra.LieCharacter R L) :
    (translation (negCharacter χ)).comp (translation χ) = AlgHom.id R (U R L) := by
  simpa only [negCharacter_negCharacter] using translation_comp_neg (negCharacter χ)

/-- Character translation is an algebra automorphism; the inverse translates by `-χ`. -/
def translationEquiv (χ : LieAlgebra.LieCharacter R L) : U R L ≃ₐ[R] U R L :=
  AlgEquiv.ofAlgHom (translation χ) (translation (negCharacter χ))
    (translation_comp_neg χ) (translation_neg_comp χ)

@[simp] theorem translationEquiv_ι (χ : LieAlgebra.LieCharacter R L) (x : L) :
    translationEquiv χ (ι R x) = ι R x + algebraMap R (U R L) (χ x) :=
  translation_ι χ x

variable {M : Type w} [LieRing M] [LieAlgebra R M]

/-- The character pulled back from the augmentation of the target. -/
def pulledBackCharacter (Φ : U R L ≃ₐ[R] U R M) : LieAlgebra.LieCharacter R L :=
  (augmentation R M).toLieHom.comp (Φ.toAlgHom.toLieHom.comp (ι R))

@[simp] theorem pulledBackCharacter_apply (Φ : U R L ≃ₐ[R] U R M) (x : L) :
    pulledBackCharacter Φ x = augmentation R M (Φ (ι R x)) := rfl

/-- Explicit normalization, with the translation on the source. -/
def normalized (Φ : U R L ≃ₐ[R] U R M) : U R L ≃ₐ[R] U R M :=
  (translationEquiv (negCharacter (pulledBackCharacter Φ))).trans Φ

/-- The normalized equivalence preserves the canonical augmentation on the entire UEA. -/
theorem normalized_preserves_augmentation (Φ : U R L ≃ₐ[R] U R M) :
    (augmentation R M).comp (normalized Φ).toAlgHom = augmentation R L := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change augmentation R M
    (Φ (translationEquiv (negCharacter (pulledBackCharacter Φ)) (ι R x))) =
    augmentation R L (ι R x)
  simp only [translationEquiv_ι, negCharacter_apply, map_add, AlgEquiv.commutes,
    AlgHom.commutes, augmentation_ι, pulledBackCharacter_apply, map_neg]
  simp

end EnvelopingIsomorphism.Enveloping
