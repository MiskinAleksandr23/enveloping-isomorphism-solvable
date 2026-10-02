import EnvelopingIsomorphism.FormalSeries.DifferentialAlgebra
import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition

/-!
# Actual completed Laurent vector fields

A lower-bounded Laurent series of coefficient derivations acts by convolution
on genuine Laurent series. Leibniz is proved on the whole completed algebra,
using the uniform bounds and the existing bounded trilinear extensionality.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentDerivationSeries

open scoped LaurentAlgebra
open LaurentModule

universe u v
variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

abbrev Series := LaurentModule k (Derivation k A A)

/-- The actual underlying coefficient endomorphism of a derivation. -/
def coefficientLinear : Derivation k A A →ₗ[k] Module.End k A where
  toFun D := D.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Include a completed derivation series into completed coefficient endomorphisms. -/
def coefficients : Series (k := k) (A := A) →ₗ[LaurentSeries k]
    LaurentModule k (Module.End k A) :=
  LaurentModule.map (k := k) (X := Derivation k A A) (Y := Module.End k A) coefficientLinear

@[simp] theorem coeff_coefficients (D : Series (k := k) (A := A)) (j : ℤ) :
    coeff (k := k) (X := Module.End k A) (coefficients D) j = (coeff D j).toLinearMap := rfl

/-- The convolution action before transporting to the actual Laurent-series ring. -/
def seriesAction : Series (k := k) (A := A) →ₗ[LaurentSeries k]
    Module.End (LaurentSeries k) (LaurentModule k A) :=
  (linearApply (k := k) (V := A) (W := A)).comp coefficients

theorem seriesAction_single (e d : ℤ) (D : Derivation k A A) (a : A) :
    seriesAction (single e D) (single d a) = single (e + d) (D a) := by
  change linearApply (coefficients (single e D)) (single d a) = _
  rw [coefficients, LaurentModule.map_single, linearApply_single]
  rfl

theorem boundedBelow_seriesAction (D : Series (k := k) (A := A)) (x : LaurentModule k A)
    {B b : ℤ} (hD : BoundedBelow B D) (hx : BoundedBelow b x) :
    BoundedBelow (B + b) (seriesAction D x) :=
  boundedBelow_linearApply _ x
    (boundedBelow_map (k := k) (X := Derivation k A A) (Y := Module.End k A)
      coefficientLinear hD) hx

/-- Multiplication on Laurent modules transported from the actual Laurent-series algebra. -/
def moduleMul : LaurentModule k A →ₗ[LaurentSeries k]
    LaurentModule k A →ₗ[LaurentSeries k] LaurentModule k A :=
  ((LinearMap.mul (LaurentSeries k) (LaurentSeries A)).compl₁₂
    (LaurentAlgebra.moduleEquiv (k := k) (A := A)).toLinearMap
    (LaurentAlgebra.moduleEquiv (k := k) (A := A)).toLinearMap).compr₂
      (LaurentAlgebra.moduleEquiv (k := k) (A := A)).symm.toLinearMap

theorem moduleEquiv_mul (x y : LaurentModule k A) :
    LaurentAlgebra.moduleEquiv (moduleMul x y) =
      LaurentAlgebra.moduleEquiv x * LaurentAlgebra.moduleEquiv y := rfl

theorem moduleMul_single (e d : ℤ) (a b : A) :
    moduleMul (k := k) (single e a) (single d b) = single (e + d) (a * b) := by
  apply LaurentModule.ext
  intro j
  change (HahnSeries.single e a * HahnSeries.single d b).coeff j = _
  rw [HahnSeries.single_mul_single]
  rfl

theorem boundedBelow_moduleMul (x y : LaurentModule k A) {b c : ℤ}
    (hx : BoundedBelow b x) (hy : BoundedBelow c y) :
    BoundedBelow (b + c) (moduleMul x y) := by
  intro d hd
  change (((HahnModule.of k).symm x) * ((HahnModule.of k).symm y)).coeff d = 0
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have heq : p.1 + p.2 = d := (Finset.mem_antidiagonal.mp hp).2.2
  by_cases h : p.1 < b
  · change coeff x p.1 * coeff y p.2 = 0
    rw [hx _ h, zero_mul]
  · change coeff x p.1 * coeff y p.2 = 0
    rw [hy _ (by omega), mul_zero]

/-- Leibniz for every completed derivation and both completed inputs. -/
theorem seriesAction_leibniz (D : Series (k := k) (A := A)) (x y : LaurentModule k A) :
    seriesAction D (moduleMul x y) =
      moduleMul (seriesAction D x) y + moduleMul (seriesAction D y) x := by
  let act := restrictBilinear (seriesAction (k := k) (A := A))
  let mul := restrictBilinear (moduleMul (k := k) (A := A))
  let L := nestRight act mul
  let C := act.compr₂ mul
  let R := C + (LinearMap.lflip (R₀ := k)).toLinearMap.comp C
  have heq : L = R := by
    apply trilinear_ext_of_bounded _ _ 0
    · intro D x y B b c hD hx hy
      change BoundedBelow (((B + b) + c) + 0) (seriesAction D (moduleMul x y))
      simpa only [add_zero, add_assoc] using boundedBelow_seriesAction D _ hD
        (boundedBelow_moduleMul x y hx hy)
    · intro D x y B b c hD hx hy
      change BoundedBelow (((B + b) + c) + 0)
        (moduleMul (seriesAction D x) y + moduleMul (seriesAction D y) x)
      apply boundedBelow_add
      · simpa only [add_zero] using boundedBelow_moduleMul (seriesAction D x) y
          (boundedBelow_seriesAction D x hD hx) hy
      · have h := boundedBelow_moduleMul (seriesAction D y) x
          (boundedBelow_seriesAction D y hD hy) hx
        convert h using 1
        omega
    · intro e f g D a b
      change seriesAction (single e D) (moduleMul (single f a) (single g b)) =
        moduleMul (seriesAction (single e D) (single f a)) (single g b) +
          moduleMul (seriesAction (single e D) (single g b)) (single f a)
      rw [moduleMul_single, seriesAction_single, seriesAction_single, seriesAction_single,
        moduleMul_single, moduleMul_single]
      have hsum : (e + g) + f = e + (f + g) := by omega
      rw [add_assoc, hsum, ← single_add]
      congr 1
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun heq D) x) y

/-- Transport the actual convolution action onto `LaurentSeries A`. -/
def linearAction : Series (k := k) (A := A) →ₗ[LaurentSeries k]
    Module.End (LaurentSeries k) (LaurentSeries A) :=
  ((LaurentAlgebra.moduleEquiv (k := k) (A := A)).arrowCongr
    (LaurentAlgebra.moduleEquiv (k := k) (A := A))).toLinearMap.comp seriesAction

theorem linearAction_apply (D : Series (k := k) (A := A)) (x : LaurentSeries A) :
    linearAction D x = LaurentAlgebra.moduleEquiv
      (seriesAction D ((LaurentAlgebra.moduleEquiv (k := k) (A := A)).symm x)) := rfl

theorem linearAction_leibniz (D : Series (k := k) (A := A)) (x y : LaurentSeries A) :
    linearAction D (x * y) = x * linearAction D y + y * linearAction D x := by
  have h := congrArg (LaurentAlgebra.moduleEquiv (k := k) (A := A))
    (seriesAction_leibniz D (LaurentAlgebra.moduleEquiv.symm x) (LaurentAlgebra.moduleEquiv.symm y))
  change linearAction D (x * y) = linearAction D x * y + linearAction D y * x at h
  rw [h]
  ring

theorem linearAction_one (D : Series (k := k) (A := A)) : linearAction D 1 = 0 := by
  have h := linearAction_leibniz D 1 1
  simp only [one_mul] at h
  have hz : linearAction D 1 + linearAction D 1 = linearAction D 1 + 0 := by simpa using h.symm
  exact add_left_cancel hz

/-- A genuine Laurent-linear derivation, proved from its completed coefficient series. -/
def toDerivation : Series (k := k) (A := A) →ₗ[LaurentSeries k]
    Derivation (LaurentSeries k) (LaurentSeries A) (LaurentSeries A) where
  toFun D :=
    { toLinearMap := linearAction D
      map_one_eq_zero' := linearAction_one D
      leibniz' := linearAction_leibniz D }
  map_add' D E := by
    apply Derivation.ext
    intro x
    exact LinearMap.congr_fun (linearAction.map_add D E) x
  map_smul' c D := by
    apply Derivation.ext
    intro x
    exact LinearMap.congr_fun (linearAction.map_smul c D) x

/-- The included coefficients as an actual Laurent series in the endomorphism ring. -/
def operatorSeries (D : Series (k := k) (A := A)) : LaurentSeries (Module.End k A) :=
  (HahnModule.of k).symm (coefficients D)

@[simp] theorem coeff_operatorSeries (D : Series (k := k) (A := A)) (j : ℤ) :
    (operatorSeries D).coeff j = (coeff D j).toLinearMap := rfl

/-- The cochain convolution is exactly the pre-existing genuine operator-ring action. -/
theorem seriesAction_eq_actionHom (D : Series (k := k) (A := A)) :
    seriesAction D = LaurentOperator.actionHom (operatorSeries D) :=
  linearApply_eq_actionHom (operatorSeries D)

/-- No new action is postulated: the resulting derivation is the actual Hahn
operator action transported through the established module equivalence. -/
theorem toDerivation_toLinearMap (D : Series (k := k) (A := A)) :
    (toDerivation D).toLinearMap =
      (LaurentAlgebra.moduleEquiv (k := k) (A := A)).toLinearMap.comp
        ((LaurentOperator.actionHom (operatorSeries D)).comp
          (LaurentAlgebra.moduleEquiv (k := k) (A := A)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change LaurentAlgebra.moduleEquiv (seriesAction D (LaurentAlgebra.moduleEquiv.symm x)) =
    LaurentAlgebra.moduleEquiv
      (LaurentOperator.actionHom (operatorSeries D) (LaurentAlgebra.moduleEquiv.symm x))
  rw [seriesAction_eq_actionHom]

/-- The exact finite convolution formula on every Laurent coefficient. -/
theorem coeff_toDerivation (D : Series (k := k) (A := A)) (x : LaurentSeries A) (j : ℤ) :
    (toDerivation D x).coeff j =
      ∑ᶠ a : Fin 2 → ℤ, if ∑ i, a i = j then (coeff D (a 0)) (x.coeff (a 1)) else 0 := rfl

theorem boundedBelow_toDerivation (D : Series (k := k) (A := A)) (x : LaurentSeries A)
    {B b : ℤ} (hD : BoundedBelow B D) (hx : ∀ j < b, x.coeff j = 0) :
    ∀ j < B + b, (toDerivation D x).coeff j = 0 :=
  boundedBelow_seriesAction D (LaurentAlgebra.moduleEquiv.symm x) hD hx

@[simp] theorem coeff_toDerivation_C (D : Series (k := k) (A := A)) (a : A) (j : ℤ) :
    (toDerivation D (HahnSeries.C a)).coeff j = (coeff D j) a := by
  change coeff (seriesAction D (single 0 a)) j = _
  rw [seriesAction_eq_actionHom, coeff_operatorAction_constant]
  rfl

/-- A constant derivation series recovers the already verified fixed-derivation extension. -/
@[simp] theorem toDerivation_single_zero (D : Derivation k A A) :
    toDerivation (single 0 D) = LaurentAlgebra.derivation D := by
  apply Derivation.ext
  intro x
  change LaurentAlgebra.moduleEquiv
    (linearApply (coefficients (single 0 D)) (LaurentAlgebra.moduleEquiv.symm x)) = _
  rw [coefficients, LaurentModule.map_single, linearApply_single_zero]
  rfl

/-- A Laurent monomial derivation is the corresponding scalar multiple of the fixed extension. -/
theorem toDerivation_single (e : ℤ) (D : Derivation k A A) :
    toDerivation (single e D) =
      (HahnSeries.single e (1 : k) : LaurentSeries k) • LaurentAlgebra.derivation D := by
  rw [single_as_series_smul, map_smul, toDerivation_single_zero]

theorem toDerivation_single_apply_single (e d : ℤ) (D : Derivation k A A) (a : A) :
    toDerivation (single e D) (HahnSeries.single d a) = HahnSeries.single (e + d) (D a) := by
  exact congrArg (LaurentAlgebra.moduleEquiv (k := k) (A := A)) (seriesAction_single e d D a)

/-- The completed vector-field representation is faithful; no surjectivity onto
all Laurent-linear derivations is asserted. -/
theorem toDerivation_injective : Function.Injective (toDerivation (k := k) (A := A)) := by
  intro D E h
  apply LaurentModule.ext
  intro j
  apply Derivation.ext
  intro a
  have ha := congrArg (fun δ : Derivation (LaurentSeries k) (LaurentSeries A) (LaurentSeries A) ↦
    (δ (HahnSeries.C a)).coeff j) h
  simpa only [coeff_toDerivation_C] using ha

end EnvelopingIsomorphism.FormalSeries.LaurentDerivationSeries
