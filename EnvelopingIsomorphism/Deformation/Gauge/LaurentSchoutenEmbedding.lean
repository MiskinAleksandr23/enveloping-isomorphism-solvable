import EnvelopingIsomorphism.Deformation.Gauge.SchoutenMCSeries
import EnvelopingIsomorphism.Deformation.SignedDGLASeries
import EnvelopingIsomorphism.Deformation.Twist
import EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
import EnvelopingIsomorphism.FormalSeries.LaurentBilinearNaturality
import EnvelopingIsomorphism.FormalSeries.LaurentDerivationSeries

/-! Faithful raw evaluation and actual action of Laurent-completed polynomial polyvectors. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten

open EnvelopingIsomorphism.FormalSeries

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

section CoefficientOperations

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

def unaryActionLinear : Module.End k A →ₗ[k] Binary k A →ₗ[k] Binary k A where
  toFun := NilpotentConjugation.unaryActionEnd
  map_add' D E := by
    apply LinearMap.ext
    intro B
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [NilpotentConjugation.unaryActionEnd_apply, unaryAction_apply,
      LinearMap.add_apply, map_add]
    abel
  map_smul' c D := by
    apply LinearMap.ext
    intro B
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [NilpotentConjugation.unaryActionEnd_apply, unaryAction_apply,
      LinearMap.smul_apply, map_smul, smul_sub, RingHom.id_apply]

theorem extend_unaryAction (D : LaurentModule k (Module.End k A))
    (B : LaurentModule k (Binary k A)) :
    LaurentModule.extendBilinear unaryActionLinear D B =
      LaurentConjugation.unaryCoefficientAction D B := by
  let out : Module.End k A →ₗ[k] Binary k A →ₗ[k] Binary k A :=
    (LinearMap.llcomp k A (Unary k A) (Unary k A)).comp (LinearMap.llcomp k A A A)
  let left : Module.End k A →ₗ[k] Binary k A →ₗ[k] Binary k A :=
    (LinearMap.llcomp k A A (Unary k A)).flip
  let right : Module.End k A →ₗ[k] Binary k A →ₗ[k] Binary k A :=
    (left.compl₂ (LinearMap.lflip (R₀ := k)).toLinearMap).compr₂ (LinearMap.lflip (R₀ := k)).toLinearMap
  have h : unaryActionLinear (k := k) (A := A) = (out - left - right : Module.End k A →ₗ[k] Binary k A →ₗ[k] Binary k A) := by
    apply LinearMap.ext
    intro D
    apply LinearMap.ext
    intro B
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  rw [h, LaurentModule.extendBilinear_coeff_sub, LaurentModule.extendBilinear_coeff_sub]
  change _ = LaurentConjugation.postCoefficient D B - LaurentConjugation.preLeftCoefficient B D -
    LaurentConjugation.preRightCoefficient B D
  have hout : LaurentModule.extendBilinear out D B = LaurentConjugation.postCoefficient D B := by
    change LaurentModule.extendBilinear out D B =
      LaurentModule.extendBilinear (LinearMap.llcomp k A (Unary k A) (Unary k A))
        (LaurentModule.map (LinearMap.llcomp k A A A) D) B
    rw [LaurentModule.extendBilinear_precomp_left]
  have hleft : LaurentModule.extendBilinear left D B = LaurentConjugation.preLeftCoefficient B D :=
    LaurentModule.extendBilinear_coeff_flip _ D B
  have hright : LaurentModule.extendBilinear right D B = LaurentConjugation.preRightCoefficient B D := by
    change LaurentModule.extendBilinear right D B =
      LaurentModule.map (LinearMap.lflip (R₀ := k)).toLinearMap
        (LaurentModule.extendBilinear (LinearMap.llcomp k A A (Unary k A))
          (LaurentModule.map (LinearMap.lflip (R₀ := k)).toLinearMap B) D)
    rw [LaurentModule.extendBilinear_precomp_left, LaurentModule.extendBilinear_postcomp,
      ← LaurentModule.extendBilinear_coeff_flip]
    rfl
  rw [hout, hleft, hright]

theorem evaluate_extended_jacobi (B C : LaurentModule k (Binary k A)) :
    LaurentModule.ternaryEvaluation
      (LaurentModule.extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) (jacobiInsertLinear (k := k) (A := A)) B C) =
      jacobiInsert (LaurentModule.binaryEvaluation B) (LaurentModule.binaryEvaluation C) := by
  change LaurentModule.ternaryEvaluation
    (LaurentModule.extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A)
      (PowerSeriesModule.insertLeftLinear + PowerSeriesModule.insertLeftLinear.compr₂ PowerSeriesModule.rotateTernary +
        PowerSeriesModule.insertLeftLinear.compr₂ (PowerSeriesModule.rotateTernary.comp PowerSeriesModule.rotateTernary)) B C) = _
  rw [LaurentModule.extendBilinear_coeff_add, LaurentModule.extendBilinear_coeff_add,
    ← LaurentModule.extendBilinear_postcomp, ← LaurentModule.extendBilinear_postcomp]
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro c
  simp only [map_add, LinearMap.add_apply, jacobiInsert_apply]
  change LaurentModule.extendTernary (LaurentModule.insertLeftSeries B C) a b c +
      LaurentModule.extendTernary (LaurentModule.map LaurentModule.rotateTernary
        (LaurentModule.insertLeftSeries B C)) a b c +
      LaurentModule.extendTernary (LaurentModule.map (LaurentModule.rotateTernary.comp
        LaurentModule.rotateTernary) (LaurentModule.insertLeftSeries B C)) a b c = _
  have hc : LaurentModule.map (LaurentModule.rotateTernary.comp LaurentModule.rotateTernary)
      (LaurentModule.insertLeftSeries B C) =
      LaurentModule.map LaurentModule.rotateTernary
        (LaurentModule.map LaurentModule.rotateTernary (LaurentModule.insertLeftSeries B C)) := by
    apply LaurentModule.ext
    intro j
    rfl
  rw [hc, LaurentModule.extendTernary_rotate, LaurentModule.extendTernary_rotate,
    LaurentModule.extendTernary_rotate, LaurentModule.extendTernary_insertLeft,
    LaurentModule.extendTernary_insertLeft, LaurentModule.extendTernary_insertLeft]
  rfl

end CoefficientOperations

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

abbrev Scalars (K : Type*) [Field K] := LaurentSeries K

local instance scalarCharZero : CharZero (Scalars K) where
  cast_injective m n h := by
    apply Nat.cast_injective (R := K)
    have hc := congrArg (fun F : LaurentSeries K => F.coeff 0) h
    simpa only [← HahnSeries.single_zero_natCast, HahnSeries.coeff_single_same] using hc
abbrev Functions (K : Type*) [Field K] (d : ℕ) := LaurentModule K (PolynomialFunctions K d)
abbrev Vector (K : Type*) [Field K] (d : ℕ) := LaurentModule K (SchoutenVector K d)
abbrev Bivector (K : Type*) [Field K] (d : ℕ) := LaurentModule K (SchoutenBivector K d)
abbrev Trivector (K : Type*) [Field K] (d : ℕ) := LaurentModule K (SchoutenTrivector K d)

def rawBivectorCoefficients : Bivector K d →ₗ[Scalars K] LaurentModule K (Binary K (PolynomialFunctions K d)) :=
  LaurentModule.map (k := K) (X := SchoutenBivector K d) (Y := Binary K (PolynomialFunctions K d)) rawBivectorLinearMap

def rawTrivectorCoefficients : Trivector K d →ₗ[Scalars K] LaurentModule K (Ternary K (PolynomialFunctions K d)) :=
  LaurentModule.map (k := K) (X := SchoutenTrivector K d) (Y := Ternary K (PolynomialFunctions K d)) (rawTrivectorLinearMap (K := K) (d := d))

def evaluateBivector : Bivector K d →ₗ[Scalars K] Binary (Scalars K) (Functions K d) :=
  LaurentModule.binaryEvaluation.comp rawBivectorCoefficients

def evaluateTrivector : Trivector K d →ₗ[Scalars K] Ternary (Scalars K) (Functions K d) :=
  LaurentModule.ternaryEvaluation.comp rawTrivectorCoefficients

omit [CharZero K] in
theorem evaluateBivector_injective : Function.Injective (evaluateBivector (K := K) (d := d)) := by
  intro F G h
  have h' := LaurentModule.binaryEvaluation_injective h
  apply LaurentModule.ext (k := K) (X := SchoutenBivector K d)
  intro j
  apply rawBivector_injective
  exact congrArg (fun T => LaurentModule.coeff T j) h'

omit [CharZero K] in
theorem evaluateTrivector_injective : Function.Injective (evaluateTrivector (K := K) (d := d)) := by
  intro F G h
  have h' := LaurentModule.ternaryEvaluation_injective h
  apply LaurentModule.ext (k := K) (X := SchoutenTrivector K d)
  intro j
  apply rawTrivector_injective
  exact congrArg (fun T => LaurentModule.coeff T j) h'

def bivectorBracket : Bivector K d →ₗ[Scalars K] Bivector K d →ₗ[Scalars K] Trivector K d :=
  (polynomialSchoutenDGLA K d).laurent.bracket 1 1

theorem evaluate_bivectorBracket (F G : Bivector K d) :
    evaluateTrivector (bivectorBracket F G) =
      jacobiInsert (evaluateBivector F) (evaluateBivector G) +
        jacobiInsert (evaluateBivector G) (evaluateBivector F) := by
  let J : SchoutenBivector K d →ₗ[K] SchoutenBivector K d →ₗ[K] Ternary K (PolynomialFunctions K d) :=
    (jacobiInsertLinear.comp rawBivectorLinearMap).compl₂ rawBivectorLinearMap
  have h : (schoutenBivectorBracket (K := K) (d := d)).compr₂ rawTrivectorLinearMap = J + J.flip := by
    apply LinearMap.ext
    intro F
    apply LinearMap.ext
    intro G
    exact rawTrivector_schoutenBracket F G
  change LaurentModule.ternaryEvaluation
    (LaurentModule.map (rawTrivectorLinearMap (K := K) (d := d))
      (LaurentModule.extendBilinear schoutenBivectorBracket F G)) = _
  rw [LaurentModule.extendBilinear_postcomp, h, LaurentModule.extendBilinear_coeff_add,
    LaurentModule.extendBilinear_coeff_flip, map_add]
  have hJ (F G : Bivector K d) : LaurentModule.extendBilinear J F G =
      LaurentModule.extendBilinear jacobiInsertLinear (rawBivectorCoefficients F) (rawBivectorCoefficients G) := by
    rw [rawBivectorCoefficients, LaurentModule.extendBilinear_precomp_left,
      LaurentModule.extendBilinear_precomp_right]
  rw [hJ, hJ, evaluate_extended_jacobi, evaluate_extended_jacobi]
  rfl

def vectorCoefficientLinear : SchoutenVector K d →ₗ[K] Module.End K (PolynomialFunctions K d) :=
  LaurentDerivationSeries.coefficientLinear.comp (Multiderivation.oneEquiv.toLinearMap.restrictScalars K)

def vectorDerivations : Vector K d →ₗ[Scalars K]
    LaurentModule K (Derivation K (PolynomialFunctions K d) (PolynomialFunctions K d)) :=
  LaurentModule.map (Multiderivation.oneEquiv.toLinearMap.restrictScalars K)

def vectorOperatorCoefficients : Vector K d →ₗ[Scalars K]
    LaurentModule K (Module.End K (PolynomialFunctions K d)) :=
  LaurentModule.map vectorCoefficientLinear

/-- The actual lower-bounded Laurent series of polynomial derivations' underlying operators. -/
def vectorOperator (X : Vector K d) : LaurentSeries (Module.End K (PolynomialFunctions K d)) :=
  LaurentDerivationSeries.operatorSeries (vectorDerivations X)

omit [CharZero K] in
theorem vectorOperator_coordinates (X : Vector K d) :
    LaurentConjugation.operatorCoordinates (vectorOperator X) = vectorOperatorCoefficients X := rfl

def coordinateEnd (X : Vector K d) : Module.End (Scalars K) (Functions K d) :=
  LaurentModule.linearApply (vectorOperatorCoefficients X)

omit [CharZero K] in
theorem coordinateEnd_eq_actionHom (X : Vector K d) :
    coordinateEnd X = LaurentOperator.actionHom (vectorOperator X) := by
  rw [coordinateEnd, ← vectorOperator_coordinates]
  exact LaurentConjugation.evaluateOperator_coordinates _

def coefficientAction : SchoutenVector K d →ₗ[K] Module.End K (SchoutenBivector K d) :=
  (polynomialSchoutenDGLA K d).zeroAction 1

/-- This is the genuine degree-zero representation of the completed source DGLA. -/
def action : Vector K d →ₗ[Scalars K] Module.End (Scalars K) (Bivector K d) :=
  (polynomialSchoutenDGLA K d).laurent.zeroAction 1

theorem rawCoefficients_action (X : Vector K d) (F : Bivector K d) :
    rawBivectorCoefficients (action X F) =
      LaurentConjugation.unaryCoefficientAction (vectorOperatorCoefficients X) (rawBivectorCoefficients F) := by
  have h : (coefficientAction (K := K) (d := d)).compr₂ rawBivectorLinearMap =
      (unaryActionLinear.comp vectorCoefficientLinear).compl₂ rawBivectorLinearMap := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro F
    exact rawBivector_schoutenVectorAction X F
  change LaurentModule.map rawBivectorLinearMap
      (LaurentModule.extendBilinear coefficientAction X F) = _
  rw [LaurentModule.extendBilinear_postcomp, h, ← LaurentModule.extendBilinear_precomp_right,
    ← LaurentModule.extendBilinear_precomp_left, extend_unaryAction]
  rfl

/-- No degree bound on the polynomial coefficients of the vector field is required. -/
theorem evaluate_action (X : Vector K d) (F : Bivector K d) :
    evaluateBivector (action X F) = unaryAction (coordinateEnd X) (evaluateBivector F) := by
  change LaurentModule.binaryEvaluation (rawBivectorCoefficients (action X F)) = _
  rw [rawCoefficients_action]
  exact LaurentConjugation.evaluate_unaryCoefficientAction _ _

theorem laurent_d_zero (p : ℤ) : (polynomialSchoutenDGLA K d).laurent.d p = 0 := by
  rw [SignedDGLA.laurent_d]
  apply LinearMap.ext
  intro X
  apply LaurentModule.ext (k := K) (X := (polynomialSchoutenDGLA K d).Obj (p + 1))
  intro j
  change (polynomialSchoutenDGLA K d).d p
    (LaurentModule.coeff (k := K) (X := (polynomialSchoutenDGLA K d).Obj p) X j) = 0
  simp only [SignedDGLA.d, polynomialSchoutenDGLA_d]
  rfl

theorem baseMC_iff_Jacobi (π : Bivector K d) :
    (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π ↔
      ∀ a b c, jacobiInsert (evaluateBivector π) (evaluateBivector π) a b c = 0 := by
  change (polynomialSchoutenDGLA K d).laurent.curvature π = 0 ↔ _
  have hcurv : (polynomialSchoutenDGLA K d).laurent.curvature π =
      (2 : Scalars K)⁻¹ • bivectorBracket π π := by
    unfold SignedDGLA.curvature
    rw [laurent_d_zero]
    simp only [LinearMap.zero_apply, zero_add]
    rfl
  rw [hcurv]
  constructor
  · intro h a b c
    have he := congrArg evaluateTrivector h
    rw [map_smul, evaluate_bivectorBracket, map_zero, ← two_smul (Scalars K),
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at he
    exact congrArg (fun T : Ternary (Scalars K) (Functions K d) => T a b c) he
  · intro h
    apply evaluateTrivector_injective
    rw [map_smul, evaluate_bivectorBracket, map_zero]
    have hj : jacobiInsert (evaluateBivector π) (evaluateBivector π) = 0 := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      apply LinearMap.ext
      intro c
      exact h a b c
    rw [hj, add_zero, smul_zero]

abbrev MC (π : Bivector K d) :=
  MCSeries (bivectorBracket π) ((2 : Scalars K)⁻¹ • bivectorBracket)

/-- Actual Laurent-completed source curvature is detected on all iterated formal inputs. -/
theorem curvature_iff_Jacobi (π : Bivector K d)
    (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan π)
    (b : PowerSeriesModule (Scalars K) (Bivector K d)) :
    quadraticCurvature (bivectorBracket π) ((2 : Scalars K)⁻¹ • bivectorBracket) b = 0 ↔
      ∀ p q r, jacobiInsert
        (PowerSeriesModule.extendBinary (PowerSeriesModule.single 0 (evaluateBivector π) +
          PowerSeriesModule.map evaluateBivector b))
        (PowerSeriesModule.extendBinary (PowerSeriesModule.single 0 (evaluateBivector π) +
          PowerSeriesModule.map evaluateBivector b)) p q r = 0 := by
  apply quadratic_MC_iff_Jacobi_of_embedding _ _ evaluateBivector evaluateTrivector
    evaluateTrivector_injective (evaluateBivector π) ((baseMC_iff_Jacobi π).mp hπ)
  · intro F
    exact evaluate_bivectorBracket π F
  · intro F G
    change evaluateTrivector ((2 : Scalars K)⁻¹ • bivectorBracket F G) = _
    rw [map_smul, evaluate_bivectorBracket]

end EnvelopingIsomorphism.Deformation.Gauge.LaurentSchouten
