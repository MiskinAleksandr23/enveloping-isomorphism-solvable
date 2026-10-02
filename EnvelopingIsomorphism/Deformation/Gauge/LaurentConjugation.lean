import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition
import EnvelopingIsomorphism.Deformation.Gauge.AssociativeEmbedding
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationAction
import EnvelopingIsomorphism.Deformation.Gauge.GeneratedAction

/-!
Closed conjugation on Laurent-cochain coefficient families, evaluated faithfully
on the actual iterated function module A((h))[[t]]. No global h-bound in t is used.
-/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries

universe u v
variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

abbrev Scalars := LaurentSeries k
abbrev Functions := LaurentModule k A
abbrev OperatorRing := LaurentSeries (Module.End k A)
abbrev OperatorCoefficients := LaurentModule k (Module.End k A)
abbrev BinaryCoefficients := LaurentModule k (Binary k A)
abbrev Families := PowerSeriesModule (Scalars (k := k)) (BinaryCoefficients (k := k) (A := A))
abbrev AmbientFamilies := PowerSeriesModule (Scalars (k := k))
  (Binary (Scalars (k := k)) (Functions (k := k) (A := A)))
abbrev CompletedFunctions := PowerSeriesModule (Scalars (k := k)) (Functions (k := k) (A := A))

def evaluateCoefficient : BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    Binary (Scalars (k := k)) (Functions (k := k) (A := A)) := LaurentModule.binaryEvaluation

def embed : Families (k := k) (A := A) →ₗ[PowerSeries (Scalars (k := k))] AmbientFamilies (k := k) (A := A) :=
  PowerSeriesModule.map (evaluateCoefficient (k := k) (A := A))

theorem embed_injective : Function.Injective (embed (k := k) (A := A)) :=
  seriesMap_injective evaluateCoefficient LaurentModule.binaryEvaluation_injective

def operatorCoefficients (F : PowerSeries (OperatorRing (k := k) (A := A))) :
    PowerSeriesModule (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A)) :=
  PowerSeriesModule.mk (fun n ↦ HahnModule.of k (PowerSeries.coeff n F))

def ambientOperators : PowerSeries (OperatorRing (k := k) (A := A)) →+*
    PowerSeries (Module.End (Scalars (k := k)) (Functions (k := k) (A := A))) :=
  PowerSeries.map LaurentOperator.actionHom

def ambientUnit : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ →*
    (PowerSeries (Module.End (Scalars (k := k)) (Functions (k := k) (A := A))))ˣ :=
  Units.map (ambientOperators (k := k) (A := A)).toMonoidHom

/-- Only an additive coordinate bridge is needed for the raw operator ring. -/
def operatorCoordinates : OperatorRing (k := k) (A := A) ≃+ OperatorCoefficients (k := k) (A := A) where
  toEquiv := HahnModule.of k
  map_add' _ _ := rfl

def evaluateOperator : OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    Module.End (Scalars (k := k)) (Functions (k := k) (A := A)) := LaurentModule.linearApply

theorem evaluateOperator_coordinates (F : OperatorRing (k := k) (A := A)) :
    evaluateOperator (operatorCoordinates F) = LaurentOperator.actionHom F :=
  LaurentModule.linearApply_eq_actionHom F

theorem evaluate_operators (F : PowerSeries (OperatorRing (k := k) (A := A))) :
    PowerSeriesModule.map (LaurentModule.linearApply (k := k) (V := A) (W := A)) (operatorCoefficients F) =
      operatorSeries (ambientOperators F) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [PowerSeriesModule.coeffV_map, operatorCoefficients, PowerSeriesModule.coeffV_mk,
    coeffV_operatorSeries, ambientOperators, PowerSeries.coeff_map]
  exact LaurentModule.linearApply_eq_actionHom (PowerSeries.coeff n F)

def preLeftCoefficient : BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)] BinaryCoefficients (k := k) (A := A) :=
  LaurentModule.linearCompose

def flipCoefficients : Families (k := k) (A := A) →ₗ[PowerSeries (Scalars (k := k))] Families (k := k) (A := A) :=
  PowerSeriesModule.map (LaurentModule.flipBinarySeries (k := k) (V := A) (W := A) (X := A))

def postCoefficient : OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)] BinaryCoefficients (k := k) (A := A) :=
  (LaurentModule.linearCompose (k := k) (V := A) (W := Unary k A) (X := Unary k A)).comp
    (LaurentModule.map (LinearMap.llcomp k A A A))

def preLeft (B : Families (k := k) (A := A))
    (F : PowerSeries (OperatorRing (k := k) (A := A))) : Families (k := k) (A := A) :=
  PowerSeriesModule.applyBilinear preLeftCoefficient B (operatorCoefficients F)

def preRight (B : Families (k := k) (A := A))
    (F : PowerSeries (OperatorRing (k := k) (A := A))) : Families (k := k) (A := A) :=
  flipCoefficients (preLeft (flipCoefficients B) F)

def post (F : PowerSeries (OperatorRing (k := k) (A := A)))
    (B : Families (k := k) (A := A)) : Families (k := k) (A := A) :=
  PowerSeriesModule.applyBilinear postCoefficient (operatorCoefficients F) B

theorem evaluate_preLeftCoefficient (B : BinaryCoefficients (k := k) (A := A))
    (F : OperatorCoefficients (k := k) (A := A)) :
    evaluateCoefficient (preLeftCoefficient B F) =
      (evaluateCoefficient B).comp (LaurentModule.linearApply F) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact LaurentModule.extendBinary_precomp_left B F x y

theorem evaluate_postCoefficient (F : OperatorCoefficients (k := k) (A := A))
    (B : BinaryCoefficients (k := k) (A := A)) :
    evaluateCoefficient (postCoefficient F B) =
      (evaluateCoefficient B).compr₂ (LaurentModule.linearApply F) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact LaurentModule.extendBinary_postcomp F B x y

theorem embed_flip (B : Families (k := k) (A := A)) :
    embed (flipCoefficients B) = PowerSeriesModule.flipBinarySeries (embed B) := by
  apply PowerSeriesModule.ext
  intro n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change LaurentModule.extendBinary
      (LaurentModule.flipBinarySeries (PowerSeriesModule.coeffV n B)) x y =
    LaurentModule.extendBinary (PowerSeriesModule.coeffV n B) y x
  exact (LaurentModule.extendBinary_flip _ y x).symm

theorem embed_preLeft (B : Families (k := k) (A := A))
    (F : PowerSeries (OperatorRing (k := k) (A := A))) :
    embed (preLeft B F) = PowerSeriesModule.linearCompose (embed B) (operatorSeries (ambientOperators F)) := by
  rw [← evaluate_operators]
  apply PowerSeriesModule.ext
  intro n
  simp only [embed, preLeft, PowerSeriesModule.coeffV_map, PowerSeriesModule.coeffV_applyBilinear,
    map_sum, PowerSeriesModule.linearCompose, PowerSeriesModule.extendBilinear_apply]
  apply Finset.sum_congr rfl
  intro ij hij
  exact evaluate_preLeftCoefficient _ _

theorem embed_preRight (B : Families (k := k) (A := A))
    (F : PowerSeries (OperatorRing (k := k) (A := A))) :
    embed (preRight B F) = PowerSeriesModule.precomposeBinaryRight (embed B)
      (operatorSeries (ambientOperators F)) := by
  rw [preRight, embed_flip, embed_preLeft, embed_flip]
  rfl

theorem embed_post (F : PowerSeries (OperatorRing (k := k) (A := A))) (B : Families (k := k) (A := A)) :
    embed (post F B) = PowerSeriesModule.postcomposeBinary (operatorSeries (ambientOperators F)) (embed B) := by
  rw [← evaluate_operators]
  apply PowerSeriesModule.ext
  intro n
  simp only [embed, post, PowerSeriesModule.coeffV_map, PowerSeriesModule.coeffV_applyBilinear,
    map_sum, PowerSeriesModule.postcomposeBinary, PowerSeriesModule.linearCompose,
    PowerSeriesModule.extendBilinear_apply]
  apply Finset.sum_congr rfl
  intro ij hij
  exact evaluate_postCoefficient _ _

/-- Raw formal operator units act by a closed coefficient construction. -/
def conjugateFamily (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) : Families (k := k) (A := A) :=
  post (G : PowerSeries (OperatorRing (k := k) (A := A)))
    (preRight (preLeft B (↑(G⁻¹) : PowerSeries (OperatorRing (k := k) (A := A))))
      (↑(G⁻¹) : PowerSeries (OperatorRing (k := k) (A := A))))

/-- The closed operation evaluates to the already verified full ambient conjugation. -/
theorem embed_conjugateFamily (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) :
    embed (conjugateFamily G B) = conjugateBinarySeries (ambientUnit G) (embed B) := by
  rw [conjugateFamily, embed_post, embed_preRight, embed_preLeft]
  rfl

@[simp] theorem conjugateFamily_one (B : Families (k := k) (A := A)) :
    conjugateFamily 1 B = B := by
  apply embed_injective
  rw [embed_conjugateFamily, map_one, conjugateBinarySeries_one]

theorem conjugateFamily_mul (G H : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) :
    conjugateFamily (G * H) B = conjugateFamily G (conjugateFamily H B) := by
  apply embed_injective
  rw [embed_conjugateFamily, map_mul, conjugateBinarySeries_mul,
    embed_conjugateFamily, embed_conjugateFamily]

@[simp] theorem conjugateFamily_inv (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) : conjugateFamily G⁻¹ (conjugateFamily G B) = B := by
  rw [← conjugateFamily_mul, inv_mul_cancel, conjugateFamily_one]

@[simp] theorem conjugateFamily_inv_right (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) : conjugateFamily G (conjugateFamily G⁻¹ B) = B := by
  rw [← conjugateFamily_mul, mul_inv_cancel, conjugateFamily_one]

def evaluateFamily (B : Families (k := k) (A := A)) :
    Binary (PowerSeries (Scalars (k := k))) (CompletedFunctions (k := k) (A := A)) :=
  PowerSeriesModule.extendBinary (embed B)

theorem evaluateFamily_injective : Function.Injective (evaluateFamily (k := k) (A := A)) := by
  intro B C h
  apply embed_injective
  exact Gauge.extendBinary_injective h

theorem evaluateFamily_conjugate (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) :
    evaluateFamily (conjugateFamily G B) =
      EnvelopingIsomorphism.Deformation.conjugate (operatorUnitEquiv (ambientUnit G)) (evaluateFamily B) := by
  rw [evaluateFamily, embed_conjugateFamily, extendBinary_conjugateBinarySeries_eq]
  rfl

theorem near_ambientOperators {N : ℕ} {F : PowerSeries (OperatorRing (k := k) (A := A))}
    (hF : NearIdentity N F) : NearIdentity N (ambientOperators F) := by
  change toJet N (ambientOperators F) = 1
  rw [← map_one (toJet N), toJet_eq_iff]
  intro n hn
  change LaurentOperator.actionHom (PowerSeries.coeff n F) = PowerSeries.coeff n 1
  rw [hF.coeff n hn, PowerSeries.coeff_one, PowerSeries.coeff_one]
  split_ifs <;> simp only [map_one, map_zero]

def ambientGauge : GaugeUnit (OperatorRing (k := k) (A := A)) →*
    GaugeUnit (Module.End (Scalars (k := k)) (Functions (k := k) (A := A))) where
  toFun G := ⟨ambientUnit G.val, near_ambientOperators G.near_one⟩
  map_one' := Subtype.ext (map_one ambientUnit)
  map_mul' G H := Subtype.ext (map_mul ambientUnit G.val H.val)

def representation : GaugeUnit (OperatorRing (k := k) (A := A)) →*
    (CompletedFunctions (k := k) (A := A) ≃ₗ[PowerSeries (Scalars (k := k))]
      CompletedFunctions (k := k) (A := A)) :=
  gaugeRepresentation LaurentOperator.actionHom

@[reducible] def familyMulAction : MulAction (GaugeUnit (OperatorRing (k := k) (A := A))) (Families (k := k) (A := A)) where
  smul G B := conjugateFamily G.val B
  one_smul := conjugateFamily_one
  mul_smul G H B := conjugateFamily_mul G.val H.val B

theorem conjugateFamily_agree (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) {N : ℕ}
    (hG : NearIdentity N (G : PowerSeries (OperatorRing (k := k) (A := A)))) :
    AgreeBelow N (conjugateFamily G B) B := by
  intro n hn
  apply LaurentModule.binaryEvaluation_injective
  have h := conjugateBinarySeries_agree (ambientUnit G) (embed B) (near_ambientOperators hG) n hn
  rw [← embed_conjugateFamily] at h
  exact h

def preRightCoefficient : BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)] BinaryCoefficients (k := k) (A := A) :=
  ((preLeftCoefficient (k := k) (A := A)).comp
    (LaurentModule.flipBinarySeries (k := k) (V := A) (W := A) (X := A))).compr₂
      (LaurentModule.flipBinarySeries (k := k) (V := A) (W := A) (X := A))

theorem evaluate_preRightCoefficient (B : BinaryCoefficients (k := k) (A := A))
    (F : OperatorCoefficients (k := k) (A := A)) :
    evaluateCoefficient (preRightCoefficient B F) =
      (evaluateCoefficient B).compl₂ (LaurentModule.linearApply F) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact LaurentModule.extendBinary_precomp_right B F x y

/-- The leading coefficient action stays in the original Laurent full-cochain space. -/
def unaryCoefficientAction : OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)] BinaryCoefficients (k := k) (A := A) :=
  postCoefficient - (preLeftCoefficient (k := k) (A := A)).flip - (preRightCoefficient (k := k) (A := A)).flip

theorem evaluate_unaryCoefficientAction (F : OperatorCoefficients (k := k) (A := A))
    (B : BinaryCoefficients (k := k) (A := A)) :
    evaluateCoefficient (unaryCoefficientAction F B) =
      unaryAction (LaurentModule.linearApply F) (evaluateCoefficient B) := by
  change evaluateCoefficient (postCoefficient F B - preLeftCoefficient B F - preRightCoefficient B F) = _
  rw [map_sub, map_sub, evaluate_postCoefficient, evaluate_preLeftCoefficient, evaluate_preRightCoefficient]
  rfl

theorem conjugateFamily_leading (G : (PowerSeries (OperatorRing (k := k) (A := A)))ˣ)
    (B : Families (k := k) (A := A)) {N : ℕ} (hN : 0 < N)
    (hG : NearIdentity N (G : PowerSeries (OperatorRing (k := k) (A := A)))) :
    PowerSeriesModule.coeffV N (conjugateFamily G B) = PowerSeriesModule.coeffV N B +
      unaryCoefficientAction (operatorCoordinates (PowerSeries.coeff N (G : PowerSeries (OperatorRing (k := k) (A := A)))))
        (PowerSeriesModule.coeffV 0 B) := by
  apply LaurentModule.binaryEvaluation_injective
  have h := conjugateBinarySeries_leading (ambientUnit G) (embed B) hN (near_ambientOperators hG)
  rw [← embed_conjugateFamily] at h
  change evaluateCoefficient (PowerSeriesModule.coeffV N (conjugateFamily G B)) =
    evaluateCoefficient (PowerSeriesModule.coeffV N B) +
      unaryAction (LaurentOperator.actionHom (PowerSeries.coeff N (G : PowerSeries (OperatorRing (k := k) (A := A)))))
        (evaluateCoefficient (PowerSeriesModule.coeffV 0 B)) at h
  change evaluateCoefficient _ = evaluateCoefficient _
  rw [map_add, evaluate_unaryCoefficientAction]
  change _ = _ + unaryAction (evaluateOperator (operatorCoordinates _)) _
  rw [evaluateOperator_coordinates]
  exact h

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
