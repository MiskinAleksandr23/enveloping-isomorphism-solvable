import EnvelopingIsomorphism.Deformation.Gauge.LaurentTargetComplex
import EnvelopingIsomorphism.Deformation.Gauge.SymmetricMiddleExact
import EnvelopingIsomorphism.Deformation.MiddleExactPerturbation

/-! The actual low Laurent Hochschild differentials are convolutions of
nonnegative operator series whenever the base product has nonnegative Laurent
coefficients. The coefficient maps use all unary, binary, and ternary cochains. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.PositiveTargetOperators

open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation LaurentConjugation

universe u v
variable {k : Type u} [Field k]

section Extension

variable {X Y Z : Type v} [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]

/-- Currying a coefficient map and then applying its Laurent operator is precisely
its existing finite-convolution bilinear extension. -/
theorem linearApply_map_eq_extendBilinear (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.linearApply (LaurentModule.map f x) y = LaurentModule.extendBilinear f x y := by
  change LaurentModule.extendBilinear (LinearMap.id : (Y →ₗ[k] Z) →ₗ[k] Y →ₗ[k] Z)
    (LaurentModule.map f x) y = _
  rw [LaurentModule.extendBilinear_precomp_left]
  rfl

theorem act_map_eq_extendBilinear (f : X →ₗ[k] Y →ₗ[k] Z) (S : PowerSeriesModule k X)
    (y : LaurentModule k Y) :
    act (PowerSeriesModule.map f S) y = LaurentModule.extendBilinear f (toLaurent S) y := by
  rw [act, toLaurent_map, linearApply_map_eq_extendBilinear]

private theorem extend_add (f g : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.extendBilinear (f + g) x y =
      LaurentModule.extendBilinear f x y + LaurentModule.extendBilinear g x y := by
  have h : LaurentModule.map (f + g) x = LaurentModule.map f x + LaurentModule.map g x := by
    apply LaurentModule.ext
    intro d
    rfl
  rw [← linearApply_map_eq_extendBilinear, h, map_add, LinearMap.add_apply,
    linearApply_map_eq_extendBilinear, linearApply_map_eq_extendBilinear]

private theorem extend_sub (f g : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.extendBilinear (f - g) x y =
      LaurentModule.extendBilinear f x y - LaurentModule.extendBilinear g x y := by
  have h : LaurentModule.map (f - g) x = LaurentModule.map f x - LaurentModule.map g x := by
    apply LaurentModule.ext
    intro d
    rfl
  rw [← linearApply_map_eq_extendBilinear, h, map_sub, LinearMap.sub_apply,
    linearApply_map_eq_extendBilinear, linearApply_map_eq_extendBilinear]

private theorem extend_eq_single (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.extendBilinear f x y = LaurentModule.extendBinary (LaurentModule.single 0 f) x y := by
  rw [LaurentModule.extendBinary_apply, LaurentModule.linearApply_single_zero,
    linearApply_map_eq_extendBilinear]

private theorem extend_flip (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    LaurentModule.extendBilinear f.flip y x = LaurentModule.extendBilinear f x y := by
  rw [extend_eq_single, extend_eq_single, LaurentModule.extendBinary_flip]
  rw [LaurentModule.flipBinarySeries, LaurentModule.map_single]
  rfl

end Extension

variable {A : Type v} [AddCommGroup A] [Module k A]

/-- Degree minus one: contraction with the binary product. -/
def deltaNegOne : Binary k A →ₗ[k] A →ₗ[k] Unary k A :=
  LinearMap.id - (LinearMap.lflip (R₀ := k)).toLinearMap

private def leftCoefficient : Binary k A →ₗ[k] Unary k A →ₗ[k] Binary k A :=
  LinearMap.llcomp k A A (Unary k A)

private def rightCoefficient : Binary k A →ₗ[k] Unary k A →ₗ[k] Binary k A :=
  (leftCoefficient.comp (LinearMap.lflip (R₀ := k)).toLinearMap).compr₂
    (LinearMap.lflip (R₀ := k)).toLinearMap

private def outputCoefficient : Unary k A →ₗ[k] Binary k A →ₗ[k] Binary k A :=
  (LinearMap.llcomp k A (Unary k A) (Unary k A)).comp (LinearMap.llcomp k A A A)

/-- Degree zero: the actual Hochschild coboundary of a full unary cochain. -/
def deltaZero : Binary k A →ₗ[k] Unary k A →ₗ[k] Binary k A :=
  leftCoefficient + rightCoefficient - outputCoefficient.flip

/-- Degree one: the symmetric binary Gerstenhaber bracket. -/
def deltaOne : Binary k A →ₗ[k] Binary k A →ₗ[k] Ternary k A :=
  PowerSeriesModule.insertBinaryLinear + PowerSeriesModule.insertBinaryLinear.flip

@[simp] theorem deltaNegOne_apply (μ : Binary k A) (a : A) : deltaNegOne μ a = differentialZero μ a := rfl

@[simp] theorem deltaZero_apply (μ : Binary k A) (X : Unary k A) : deltaZero μ X = differentialOne μ X := rfl

@[simp] theorem deltaOne_apply (μ ν : Binary k A) : deltaOne μ ν = differentialTwo μ ν := rfl

private theorem extend_left (μ : BinaryCoefficients (k := k) (A := A))
    (X : OperatorCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear leftCoefficient μ X = preLeftCoefficient μ X := rfl

private theorem extend_right (μ : BinaryCoefficients (k := k) (A := A))
    (X : OperatorCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear rightCoefficient μ X = preRightCoefficient μ X := by
  change LaurentModule.extendBilinear
    ((leftCoefficient.comp (LinearMap.lflip (R₀ := k)).toLinearMap).compr₂
      (LinearMap.lflip (R₀ := k)).toLinearMap) μ X = _
  rw [← LaurentModule.extendBilinear_postcomp, ← LaurentModule.extendBilinear_precomp_left]
  rfl

private theorem extend_output (X : OperatorCoefficients (k := k) (A := A))
    (μ : BinaryCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear outputCoefficient X μ = postCoefficient X μ := by
  change LaurentModule.extendBilinear
    ((LinearMap.llcomp k A (Unary k A) (Unary k A)).comp (LinearMap.llcomp k A A A)) X μ = _
  rw [← LaurentModule.extendBilinear_precomp_left]
  rfl

theorem extend_deltaNegOne (μ : BinaryCoefficients (k := k) (A := A))
    (a : Functions (k := k) (A := A)) :
    LaurentModule.extendBilinear deltaNegOne μ a = innerCoefficient μ a := by
  have h : LaurentModule.map (deltaNegOne (k := k) (A := A)) μ = μ - LaurentModule.flipBinarySeries μ := by
    apply LaurentModule.ext
    intro d
    rfl
  rw [← linearApply_map_eq_extendBilinear, h, map_sub, LinearMap.sub_apply]
  rfl

theorem extend_deltaZero (μ : BinaryCoefficients (k := k) (A := A))
    (X : OperatorCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear deltaZero μ X = differentialUnary μ X := by
  rw [deltaZero, extend_sub, extend_add, extend_left, extend_right, extend_flip, extend_output]
  change preLeftCoefficient μ X + preRightCoefficient μ X - postCoefficient X μ =
    -(postCoefficient X μ - preLeftCoefficient μ X - preRightCoefficient μ X)
  abel

private theorem extend_insertion (μ ν : BinaryCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear PowerSeriesModule.insertBinaryLinear μ ν =
      LaurentModule.insertBinarySeries μ ν := by
  change LaurentModule.extendBilinear
    (LaurentModule.insertLeftCoefficient - LaurentModule.insertRightCoefficient) μ ν = _
  rw [extend_sub]
  rfl

theorem extend_deltaOne (μ ν : BinaryCoefficients (k := k) (A := A)) :
    LaurentModule.extendBilinear deltaOne μ ν = LaurentModule.differentialBinarySeries μ ν := by
  rw [deltaOne, extend_add, extend_flip, extend_insertion, extend_insertion]
  rfl

/-- Coefficients are actual maps on the original coefficient cochain spaces. -/
def operatorNegOne (S : PowerSeriesModule k (Binary k A)) : OperatorSeries (k := k) A (Unary k A) :=
  PowerSeriesModule.map deltaNegOne S

def operatorZero (S : PowerSeriesModule k (Binary k A)) : OperatorSeries (k := k) (Unary k A) (Binary k A) :=
  PowerSeriesModule.map deltaZero S

def operatorOne (S : PowerSeriesModule k (Binary k A)) : OperatorSeries (k := k) (Binary k A) (Ternary k A) :=
  PowerSeriesModule.map deltaOne S

@[simp] theorem coeff_operatorNegOne (S : PowerSeriesModule k (Binary k A)) (n : ℕ) :
    PowerSeriesModule.coeffV n (operatorNegOne S) = deltaNegOne (PowerSeriesModule.coeffV n S) := rfl

@[simp] theorem coeff_operatorZero (S : PowerSeriesModule k (Binary k A)) (n : ℕ) :
    PowerSeriesModule.coeffV n (operatorZero S) = deltaZero (PowerSeriesModule.coeffV n S) := rfl

@[simp] theorem coeff_operatorOne (S : PowerSeriesModule k (Binary k A)) (n : ℕ) :
    PowerSeriesModule.coeffV n (operatorOne S) = deltaOne (PowerSeriesModule.coeffV n S) := rfl

theorem act_operatorNegOne (S : PowerSeriesModule k (Binary k A)) :
    act (operatorNegOne S) = innerCoefficient (toLaurent S) := by
  apply LinearMap.ext
  intro a
  rw [operatorNegOne, act_map_eq_extendBilinear, extend_deltaNegOne]

theorem act_operatorZero (S : PowerSeriesModule k (Binary k A)) :
    act (operatorZero S) = differentialUnary (toLaurent S) := by
  apply LinearMap.ext
  intro X
  rw [operatorZero, act_map_eq_extendBilinear, extend_deltaZero]

theorem act_operatorOne (S : PowerSeriesModule k (Binary k A)) :
    act (operatorOne S) = LaurentModule.differentialBinarySeries (toLaurent S) := by
  apply LinearMap.ext
  intro ν
  rw [operatorOne, act_map_eq_extendBilinear, extend_deltaOne]


section TargetComplex

variable (S : PowerSeriesModule k (Binary k A))
variable (hS : ∀ a b c, evaluateCoefficient (toLaurent S) (evaluateCoefficient (toLaurent S) a b) c =
  evaluateCoefficient (toLaurent S) a (evaluateCoefficient (toLaurent S) b c))

/-- The native degree-minus-one differential is the actual positive-series action. -/
theorem target_d_negative_one :
    ((targetComplex (toLaurent S) hS).d (-1) 0).hom = act (operatorNegOne S) := by
  rw [targetComplex_d_negative_one, act_operatorNegOne]

theorem target_d_zero :
    ((targetComplex (toLaurent S) hS).d 0 1).hom = act (operatorZero S) := by
  rw [targetComplex_d_zero, act_operatorZero]

theorem target_d_one :
    ((targetComplex (toLaurent S) hS).d 1 2).hom = act (operatorOne S) := by
  rw [targetComplex_d_one, act_operatorOne]

end TargetComplex

section CommutativeBase

variable {B : Type v} [CommRing B] [Algebra k B]

@[simp] theorem deltaNegOne_mul : deltaNegOne (LinearMap.mul k B) = 0 := by
  apply LinearMap.ext
  intro b
  rw [deltaNegOne_apply]
  exact SymmetricMiddle.differentialZero_eq_zero b

/-- The constant unary differential is exactly the map used in symmetric middle exactness. -/
theorem deltaZero_mul : deltaZero (LinearMap.mul k B) = SymmetricMiddle.coboundary := by
  apply LinearMap.ext
  intro X
  rfl

@[simp] theorem deltaOne_mul :
    deltaOne (LinearMap.mul k B) = PowerSeriesModule.differentialTwoLinear (LinearMap.mul k B) := rfl

theorem coeff0_operatorNegOne (S : PowerSeriesModule k (Binary k B))
    (hS : PowerSeriesModule.coeffV 0 S = LinearMap.mul k B) :
    PowerSeriesModule.coeffV 0 (operatorNegOne S) = 0 := by
  rw [coeff_operatorNegOne, hS, deltaNegOne_mul]

theorem coeff0_operatorZero (S : PowerSeriesModule k (Binary k B))
    (hS : PowerSeriesModule.coeffV 0 S = LinearMap.mul k B) :
    PowerSeriesModule.coeffV 0 (operatorZero S) = SymmetricMiddle.coboundary := by
  rw [coeff_operatorZero, hS, deltaZero_mul]

theorem coeff0_operatorOne (S : PowerSeriesModule k (Binary k B))
    (hS : PowerSeriesModule.coeffV 0 S = LinearMap.mul k B) :
    PowerSeriesModule.coeffV 0 (operatorOne S) = PowerSeriesModule.differentialTwoLinear (LinearMap.mul k B) := by
  rw [coeff_operatorOne, hS, deltaOne_mul]

end CommutativeBase

end EnvelopingIsomorphism.Deformation.Gauge.PositiveTargetOperators
