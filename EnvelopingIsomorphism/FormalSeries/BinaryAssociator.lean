import EnvelopingIsomorphism.Deformation.LowArity
import EnvelopingIsomorphism.Deformation.Gauge.ElementaryOperators
import EnvelopingIsomorphism.Deformation.Gauge.CurvatureLeading

/-! Associativity of a complete binary family is the actual quadratic
Hochschild Maurer-Cartan equation on its coefficient cochains. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

open EnvelopingIsomorphism.Deformation

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

def extendTernary (F : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) : PowerSeriesModule k V :=
  linearApply (extendBinary F p q) r

theorem extendTernary_apply (F : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary F p q r = extendBinary (linearApply F p) q r := rfl

theorem linearApply_map_post {W X : Type*} [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] (h : W →ₗ[k] X)
    (F : PowerSeriesModule k (V →ₗ[k] W)) (p : PowerSeriesModule k V) :
    linearApply (map (LinearMap.llcomp k V W X h) F) p = map h (linearApply F p) := by
  ext n
  simp [map_sum]

def flipTernaryInner : Ternary k V →ₗ[k] Ternary k V :=
  LinearMap.llcomp k V (Binary k V) (Binary k V) (LinearMap.lflip (R₀ := k)).toLinearMap

@[simp] theorem flipTernaryInner_apply (F : Ternary k V) (a b c : V) :
    flipTernaryInner F a b c = F a c b := rfl

def rotateTernary : Ternary k V →ₗ[k] Ternary k V :=
  (LinearMap.lflip (R₀ := k)).toLinearMap.comp flipTernaryInner

@[simp] theorem rotateTernary_apply (F : Ternary k V) (a b c : V) :
    rotateTernary F a b c = F b c a := rfl

theorem extendTernary_flipInner (F : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (map flipTernaryInner F) p q r = extendTernary F p r q := by
  rw [extendTernary_apply, flipTernaryInner, linearApply_map_post]
  change extendBinary (flipBinarySeries (linearApply F p)) q r = _
  rw [← extendBinary_flip]
  rfl

theorem extendTernary_flipOuter (F : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (flipBinarySeries F) p q r = extendTernary F q p r := by
  rw [extendTernary, ← extendBinary_flip]
  rfl

theorem extendTernary_rotate (F : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (map rotateTernary F) p q r = extendTernary F q r p := by
  have h : map rotateTernary F = flipBinarySeries (map flipTernaryInner F) := by
    ext n
    rfl
  rw [h, extendTernary_flipOuter, extendTernary_flipInner]

def insertLeftLinear : Binary k V →ₗ[k] Binary k V →ₗ[k] Ternary k V where
  toFun B :=
    { toFun := insertLeft B
      map_add' _ _ := by ext a b c; simp
      map_smul' _ _ := by ext a b c; simp }
  map_add' _ _ := by ext C a b c; simp
  map_smul' _ _ := by ext C a b c; simp

def insertRightLinear : Binary k V →ₗ[k] Binary k V →ₗ[k] Ternary k V where
  toFun B :=
    { toFun := insertRight B
      map_add' _ _ := by ext a b c; simp
      map_smul' _ _ := by ext a b c; simp }
  map_add' _ _ := by ext C a b c; simp
  map_smul' _ _ := by ext C a b c; simp

def insertBinaryLinear : Binary k V →ₗ[k] Binary k V →ₗ[k] Ternary k V :=
  (insertLeftLinear (k := k) (V := V)) - (insertRightLinear (k := k) (V := V))

@[simp] theorem insertBinaryLinear_apply (B C : Binary k V) :
    insertBinaryLinear B C = insertBinary B C := rfl

theorem applyBilinear_insertLeft (B C : PowerSeriesModule k (Binary k V)) :
    applyBilinear (X := Ternary k V) (insertLeftLinear (k := k) (V := V)) B C = postcomposeBinary B C := by
  ext n a b c
  simp only [coeffV_applyBilinear, LinearMap.sum_apply, postcomposeBinary, linearCompose,
    extendBilinear_apply, coeffV_map, LinearMap.llcomp_apply]
  rfl

theorem applyBilinear_insertRight (B C : PowerSeriesModule k (Binary k V)) :
    applyBilinear (X := Ternary k V) (insertRightLinear (k := k) (V := V)) B C =
      map rotateTernary (postcomposeBinary (flipBinarySeries B) C) := by
  rw [← applyBilinear_insertLeft]
  ext n a b c
  simp only [coeffV_applyBilinear, coeffV_map, map_sum, LinearMap.sum_apply,
    coeffV_flipBinarySeries, rotateTernary_apply]
  rfl

theorem extendTernary_insertLeft (B C : PowerSeriesModule k (Binary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (applyBilinear (X := Ternary k V) (insertLeftLinear (k := k) (V := V)) B C) p q r =
      extendBinary B (extendBinary C p q) r := by
  rw [applyBilinear_insertLeft, extendTernary, extendBinary_postcomp]
  rfl

theorem extendTernary_insertRight (B C : PowerSeriesModule k (Binary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (applyBilinear (X := Ternary k V) (insertRightLinear (k := k) (V := V)) B C) p q r =
      extendBinary B p (extendBinary C q r) := by
  rw [applyBilinear_insertRight, extendTernary_rotate, ← applyBilinear_insertLeft,
    extendTernary_insertLeft, ← extendBinary_flip]

theorem applyBilinear_insertBinary (B C : PowerSeriesModule k (Binary k V)) :
    applyBilinear (insertBinaryLinear (k := k) (V := V)) B C =
      applyBilinear (insertLeftLinear (k := k) (V := V)) B C -
      applyBilinear (insertRightLinear (k := k) (V := V)) B C := by
  ext n
  simp [insertBinaryLinear, Finset.sum_sub_distrib]

@[simp] theorem extendTernary_sub (F G : PowerSeriesModule k (Ternary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (F - G) p q r = extendTernary F p q r - extendTernary G p q r := by
  simp [extendTernary, extendBinary_apply]

@[simp] theorem extendTernary_zero (p q r : PowerSeriesModule k V) :
    extendTernary (0 : PowerSeriesModule k (Ternary k V)) p q r = 0 := by
  simp [extendTernary, extendBinary_apply]

theorem coeffV_extendTernary_constants (F : PowerSeriesModule k (Ternary k V))
    (a b c : V) (n : ℕ) :
    coeffV n (extendTernary F (single 0 a) (single 0 b) (single 0 c)) = coeffV n F a b c := by
  simp only [extendTernary, extendBinary_apply, Gauge.coeffV_linearApply_single_zero]

theorem extendTernary_eq_zero_iff (F : PowerSeriesModule k (Ternary k V)) :
    (∀ p q r, extendTernary F p q r = 0) ↔ F = 0 := by
  constructor
  · intro h
    ext n a b c
    have he := congrArg (coeffV n) (h (single 0 a) (single 0 b) (single 0 c))
    simpa only [coeffV_extendTernary_constants, coeffV_zero, LinearMap.zero_apply] using he
  · rintro rfl
    exact extendTernary_zero

/-- The insertion convolution is precisely the complete associator. -/
theorem extendTernary_insertBinary (B C : PowerSeriesModule k (Binary k V))
    (p q r : PowerSeriesModule k V) :
    extendTernary (applyBilinear (insertBinaryLinear (k := k) (V := V)) B C) p q r =
      extendBinary B (extendBinary C p q) r - extendBinary B p (extendBinary C q r) := by
  rw [applyBilinear_insertBinary, extendTernary_sub,
    extendTernary_insertLeft, extendTernary_insertRight]

theorem associative_iff_insertion_zero (B : PowerSeriesModule k (Binary k V)) :
    (∀ p q r, extendBinary B (extendBinary B p q) r = extendBinary B p (extendBinary B q r)) ↔
      applyBilinear (insertBinaryLinear (k := k) (V := V)) B B = 0 := by
  rw [← extendTernary_eq_zero_iff]
  simp only [extendTernary_insertBinary, sub_eq_zero]

def differentialTwoLinear (μ : Binary k V) : Binary k V →ₗ[k] Ternary k V :=
  insertBinaryLinear μ + (insertBinaryLinear (k := k) (V := V)).flip μ

@[simp] theorem differentialTwoLinear_apply (μ ν : Binary k V) :
    differentialTwoLinear μ ν = differentialTwo μ ν := rfl

theorem applyBilinear_single_zero_right {W X : Type*} [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] (f : V →ₗ[k] W →ₗ[k] X)
    (p : PowerSeriesModule k V) (w : W) :
    applyBilinear f p (single 0 w) = map (f.flip w) p := by
  ext n
  rw [Gauge.coeffV_applyBilinear_single_right, coeffV_map, LinearMap.flip_apply]

theorem applyBilinear_single_zero_left {W X : Type*} [AddCommGroup W] [Module k W]
    [AddCommGroup X] [Module k X] (f : V →ₗ[k] W →ₗ[k] X)
    (v : V) (q : PowerSeriesModule k W) :
    applyBilinear f (single 0 v) q = map (f v) q := by
  rw [applyBilinear_flip, applyBilinear_single_zero_right]
  rfl

theorem insertion_constant_self_zero (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    applyBilinear (insertBinaryLinear (k := k) (V := V)) (single 0 μ) (single 0 μ) = 0 := by
  rw [applyBilinear_single_zero_left]
  apply PowerSeriesModule.ext
  intro n
  simp only [coeffV_map, coeffV_single, coeffV_zero]
  split_ifs
  · exact (insertBinary_self_eq_zero_iff μ).mpr hμ
  · exact map_zero _

/-- Exact expansion, including every coefficient of the nonlinear insertion square. -/
theorem insertion_eq_quadraticCurvature (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (b : PowerSeriesModule k (Binary k V)) :
    applyBilinear (insertBinaryLinear (k := k) (V := V)) (single 0 μ + b) (single 0 μ + b) =
      Gauge.quadraticCurvature (differentialTwoLinear μ) insertBinaryLinear b := by
  change extendBilinear insertBinaryLinear (single 0 μ + b) (single 0 μ + b) = _
  simp only [map_add, LinearMap.add_apply, extendBilinear_apply]
  rw [insertion_constant_self_zero μ hμ, zero_add, applyBilinear_single_zero_left,
    applyBilinear_single_zero_right]
  simp only [Gauge.quadraticCurvature]
  ext n
  simp only [coeffV_add, coeffV_map, differentialTwoLinear, LinearMap.add_apply]
  abel

/-- The coefficient MC equation is equivalent to associativity on actual vector series. -/
theorem quadratic_MC_iff_associative (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (b : PowerSeriesModule k (Binary k V)) :
    Gauge.quadraticCurvature (differentialTwoLinear μ) insertBinaryLinear b = 0 ↔
      ∀ p q r, extendBinary (single 0 μ + b) (extendBinary (single 0 μ + b) p q) r =
        extendBinary (single 0 μ + b) p (extendBinary (single 0 μ + b) q r) := by
  rw [associative_iff_insertion_zero, insertion_eq_quadraticCurvature μ hμ]

end EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
