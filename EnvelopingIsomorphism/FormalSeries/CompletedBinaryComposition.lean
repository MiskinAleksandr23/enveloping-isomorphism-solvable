import EnvelopingIsomorphism.FormalSeries.CompletedOperatorAction
import EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

/-!
Binary Laurent-cochain families act faithfully on the genuine double completion.
Closed precomposition and postcomposition reuse the coefficient convolutions, so
identities on vectors constant in both parameters extend to all completed vectors.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.CompletedBinary

open EnvelopingIsomorphism.Deformation
open CompletedOperator
open scoped CompletedOperator

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

/-- Each outer coefficient is a Laurent series of full binary cochains. -/
abbrev Families (k A : Type*) [CommRing k] [AddCommGroup A] [Module k A] :=
  PowerSeriesModule (LaurentSeries k) (LaurentModule k (Binary k A))

/-- Evaluation is linear in the cochain family over the full scalar series ring. -/
def binaryAction : Families k A →ₗ[PowerSeries (LaurentSeries k)]
    Binary (PowerSeries (LaurentSeries k)) (Vectors k A) :=
  ((LinearMap.compRight (PowerSeries (LaurentSeries k))
      (PowerSeriesModule.linearApply (k := LaurentSeries k)
        (V := LaurentModule k A) (W := LaurentModule k A))).comp
    (PowerSeriesModule.linearApply (k := LaurentSeries k)
      (V := LaurentModule k A)
      (W := LaurentModule k A →ₗ[LaurentSeries k] LaurentModule k A))).comp
    Gauge.LaurentConjugation.embed

@[simp] theorem binaryAction_apply (B : Families k A) (x y : Vectors k A) :
    binaryAction B x y =
      PowerSeriesModule.extendBinary (Gauge.LaurentConjugation.embed B) x y := rfl

/-- The two coefficient extractions recover exactly the original binary cochain. -/
theorem coeff_binaryAction_constants (B : Families k A) (a b : A) (r : ℕ) (j : ℤ) :
    LaurentModule.coeff
        (PowerSeriesModule.coeffV r (binaryAction B (constant a) (constant b))) j =
      LaurentModule.coeff (PowerSeriesModule.coeffV r B) j a b := by
  rw [binaryAction_apply, constant, constant, Gauge.coeffV_extendBinary_constants]
  change LaurentModule.coeff
      (LaurentModule.extendBinary (PowerSeriesModule.coeffV r B)
        (LaurentModule.single 0 a) (LaurentModule.single 0 b)) j = _
  exact LaurentModule.coeff_extendBinary_constants _ a b j

/-- Constant-input equality detects the coefficient family; no spanning claim is used. -/
theorem ext_on_constants {B C : Families k A}
    (h : ∀ a b, binaryAction B (constant a) (constant b) =
      binaryAction C (constant a) (constant b)) : B = C := by
  apply PowerSeriesModule.ext
  intro r
  apply LaurentModule.ext
  intro j
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  have hc := congrArg
    (fun x ↦ LaurentModule.coeff (PowerSeriesModule.coeffV r x) j) (h a b)
  simpa only [coeff_binaryAction_constants] using hc

theorem binaryAction_injective : Function.Injective (binaryAction (k := k) (A := A)) := by
  intro B C h
  exact ext_on_constants (fun a b ↦ DFunLike.congr_fun
    (DFunLike.congr_fun h (constant a)) (constant b))

theorem binaryAction_eq_of_constants {B C : Families k A}
    (h : ∀ a b, binaryAction B (constant a) (constant b) =
      binaryAction C (constant a) (constant b)) : binaryAction B = binaryAction C :=
  congrArg binaryAction (ext_on_constants h)

/-- Precomposition in the first input remains a family of Laurent cochains. -/
abbrev preLeft (B : Families k A) (F : Operators k A) : Families k A :=
  Gauge.LaurentConjugation.preLeft B F

/-- Precomposition in the second input remains a family of Laurent cochains. -/
abbrev preRight (B : Families k A) (F : Operators k A) : Families k A :=
  Gauge.LaurentConjugation.preRight B F

/-- Postcomposition remains a family of Laurent cochains. -/
abbrev post (F : Operators k A) (B : Families k A) : Families k A :=
  Gauge.LaurentConjugation.post F B

theorem ambientOperator_action (F : Operators k A) (x : Vectors k A) :
    PowerSeriesModule.linearApply
      (Gauge.operatorSeries (Gauge.LaurentConjugation.ambientOperators F)) x =
      actionHom F x := by
  rw [actionHom_apply, PowerSeriesModule.actV_eq_linearApply]
  rfl

@[simp] theorem binaryAction_preLeft (B : Families k A) (F : Operators k A)
    (x y : Vectors k A) :
    binaryAction (preLeft B F) x y = binaryAction B (actionHom F x) y := by
  rw [binaryAction_apply, preLeft, Gauge.LaurentConjugation.embed_preLeft,
    PowerSeriesModule.extendBinary_precomp_left, ambientOperator_action]
  rfl

@[simp] theorem binaryAction_preRight (B : Families k A) (F : Operators k A)
    (x y : Vectors k A) :
    binaryAction (preRight B F) x y = binaryAction B x (actionHom F y) := by
  rw [binaryAction_apply, preRight, Gauge.LaurentConjugation.embed_preRight,
    PowerSeriesModule.extendBinary_precomp_right, ambientOperator_action]
  rfl

@[simp] theorem binaryAction_post (F : Operators k A) (B : Families k A)
    (x y : Vectors k A) :
    binaryAction (post F B) x y = actionHom F (binaryAction B x y) := by
  rw [binaryAction_apply, post, Gauge.LaurentConjugation.embed_post,
    PowerSeriesModule.extendBinary_postcomp, ambientOperator_action]
  rfl

/-- An intertwining equation between closed families can be checked on constants. -/
theorem intertwines_of_constants (F : Operators k A) (B C : Families k A)
    (h : ∀ a b, actionHom F (binaryAction B (constant a) (constant b)) =
      binaryAction C (actionHom F (constant a)) (actionHom F (constant b)))
    (x y : Vectors k A) :
    actionHom F (binaryAction B x y) =
      binaryAction C (actionHom F x) (actionHom F y) := by
  have hc : post F B = preRight (preLeft C F) F := by
    apply ext_on_constants
    intro a b
    simpa only [binaryAction_post, binaryAction_preRight, binaryAction_preLeft] using h a b
  have he := congrArg (fun D ↦ binaryAction D x y) hc
  simpa only [binaryAction_post, binaryAction_preRight, binaryAction_preLeft] using he

/-- The corresponding equality holds between the actual completed bilinear maps. -/
theorem intertwines_eq_of_constants (F : Operators k A) (B C : Families k A)
    (h : ∀ a b, actionHom F (binaryAction B (constant a) (constant b)) =
      binaryAction C (actionHom F (constant a)) (actionHom F (constant b))) :
    (binaryAction B).compr₂ (actionHom F) =
      ((binaryAction C).comp (actionHom F)).compl₂ (actionHom F) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact intertwines_of_constants F B C h x y

end EnvelopingIsomorphism.FormalSeries.CompletedBinary
