import EnvelopingIsomorphism.FormalSeries.LaurentBilinear
import EnvelopingIsomorphism.FormalSeries.LaurentOperatorAction
import EnvelopingIsomorphism.Deformation.LowArity

/-!
Composition and insertion stay inside Laurent series of full coefficient cochains.
Evaluation is faithful and takes place on the actual vector-valued Laurent modules.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

universe u v
variable {k : Type u} [CommRing k]
variable {V W X Y : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- Evaluate a Laurent series of arbitrary linear maps on a Laurent vector. -/
def linearApply : LaurentModule k (V →ₗ[k] W) →ₗ[LaurentSeries k]
    LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k W :=
  extendBilinear (LinearMap.id : (V →ₗ[k] W) →ₗ[k] V →ₗ[k] W)

theorem coeff_linearApply (F : LaurentModule k (V →ₗ[k] W)) (x : LaurentModule k V) (d : ℤ) :
    coeff (linearApply F x) d =
      ∑ᶠ a : Fin 2 → ℤ, if ∑ i, a i = d then coeff F (a 0) (coeff x (a 1)) else 0 := rfl

theorem boundedBelow_linearApply (F : LaurentModule k (V →ₗ[k] W)) (x : LaurentModule k V)
    {B b : ℤ} (hF : BoundedBelow B F) (hx : BoundedBelow b x) :
    BoundedBelow (B + b) (linearApply F x) := boundedBelow_extendBilinear _ F x hF hx

theorem linearApply_single (e d : ℤ) (f : V →ₗ[k] W) (x : V) :
    linearApply (single e f) (single d x) = single (e + d) (f x) :=
  extendBilinear_single _ e d f x

/-- The coefficientwise composition convolution, with no enlargement to all E-linear maps. -/
def linearCompose : LaurentModule k (W →ₗ[k] X) →ₗ[LaurentSeries k]
    LaurentModule k (V →ₗ[k] W) →ₗ[LaurentSeries k] LaurentModule k (V →ₗ[k] X) :=
  extendBilinear (LinearMap.llcomp k V W X)

theorem boundedBelow_linearCompose (G : LaurentModule k (W →ₗ[k] X))
    (F : LaurentModule k (V →ₗ[k] W)) {B C : ℤ} (hG : BoundedBelow B G) (hF : BoundedBelow C F) :
    BoundedBelow (B + C) (linearCompose G F) := boundedBelow_extendBilinear _ G F hG hF

theorem linearCompose_single (e d : ℤ) (g : W →ₗ[k] X) (f : V →ₗ[k] W) :
    linearCompose (single e g) (single d f) = single (e + d) (g.comp f) :=
  extendBilinear_single _ e d g f

theorem linearApply_comp (G : LaurentModule k (W →ₗ[k] X))
    (F : LaurentModule k (V →ₗ[k] W)) (x : LaurentModule k V) :
    linearApply (linearCompose G F) x = linearApply G (linearApply F x) := by
  let L := (restrictBilinear (linearCompose (k := k) (V := V) (W := W) (X := X))).compr₂
    (restrictBilinear (linearApply (k := k) (V := V) (W := X)))
  let R := nestRight (restrictBilinear (linearApply (k := k) (V := W) (W := X)))
    (restrictBilinear (linearApply (k := k) (V := V) (W := W)))
  have heq : L = R := by
    apply trilinear_ext_of_bounded _ _ 0
    · intro G F x b c d hG hF hx
      change BoundedBelow (((b + c) + d) + 0) (linearApply (linearCompose G F) x)
      simpa only [add_zero] using boundedBelow_linearApply (linearCompose G F) x
        (boundedBelow_linearCompose G F hG hF) hx
    · intro G F x b c d hG hF hx
      change BoundedBelow (((b + c) + d) + 0) (linearApply G (linearApply F x))
      simpa only [add_zero, add_assoc] using boundedBelow_linearApply G (linearApply F x)
        hG (boundedBelow_linearApply F x hF hx)
    · intro b c d g f x
      change linearApply (linearCompose (single b g) (single c f)) (single d x) =
        linearApply (single b g) (linearApply (single c f) (single d x))
      rw [linearCompose_single, linearApply_single, linearApply_single, linearApply_single]
      rw [add_assoc]
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun heq G) F) x

theorem linearApply_constant (F : LaurentModule k (V →ₗ[k] W)) (x : V) :
    linearApply F (single 0 x) = map (LinearMap.applyₗ x) F := by
  have heq : (restrictBilinear (linearApply (k := k) (V := V) (W := W))).flip (single 0 x) =
      (map (LinearMap.applyₗ x)).restrictScalars k := by
    apply linear_ext_of_bounded _ _ 0
    · intro B G hG
      change BoundedBelow (B + 0) (linearApply G (single 0 x))
      exact boundedBelow_linearApply G (single 0 x) hG (boundedBelow_single 0 x)
    · intro B G hG
      change BoundedBelow (B + 0) (map (LinearMap.applyₗ x) G)
      simpa only [add_zero] using boundedBelow_map (LinearMap.applyₗ x) hG
    · intro e f
      change linearApply (single e f) (single 0 x) = map (LinearMap.applyₗ x) (single e f)
      rw [linearApply_single, map_single, add_zero]
      rfl
  exact DFunLike.congr_fun heq F

theorem linearApply_injective : Function.Injective (linearApply (k := k) (V := V) (W := W)) := by
  intro F G h
  apply LaurentModule.ext
  intro d
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun H : LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k W ↦
    coeff (H (single 0 x)) d) h
  simp only [linearApply_constant, coeff_map] at hx
  exact hx

/-- Actual evaluation of a Laurent family of full binary cochains. -/
def extendBinary (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) :
    LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k W →ₗ[LaurentSeries k] LaurentModule k X :=
  linearApply.comp (linearApply F)

/-- Evaluation is linear in the full Laurent binary coefficient family. -/
def binaryEvaluation : LaurentModule k (V →ₗ[k] W →ₗ[k] X) →ₗ[LaurentSeries k]
    LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k W →ₗ[LaurentSeries k] LaurentModule k X :=
  (LinearMap.compRight (LaurentSeries k) (linearApply (k := k) (V := W) (W := X))).comp
    (linearApply (k := k) (V := V) (W := W →ₗ[k] X))

@[simp] theorem binaryEvaluation_apply (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X))
    (x : LaurentModule k V) (y : LaurentModule k W) : binaryEvaluation F x y = extendBinary F x y := rfl

theorem extendBinary_apply (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X))
    (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBinary F x y = linearApply (linearApply F x) y := rfl

theorem boundedBelow_extendBinary (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X))
    (x : LaurentModule k V) (y : LaurentModule k W) {B b c : ℤ}
    (hF : BoundedBelow B F) (hx : BoundedBelow b x) (hy : BoundedBelow c y) :
    BoundedBelow ((B + b) + c) (extendBinary F x y) :=
  boundedBelow_linearApply (linearApply F x) y (boundedBelow_linearApply F x hF hx) hy

def flipBinarySeries : LaurentModule k (V →ₗ[k] W →ₗ[k] X) →ₗ[LaurentSeries k]
    LaurentModule k (W →ₗ[k] V →ₗ[k] X) := map (LinearMap.lflip (R₀ := k)).toLinearMap

@[simp] theorem coeff_flipBinarySeries (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (d : ℤ) :
    coeff (flipBinarySeries F) d = (coeff F d).flip := rfl

theorem extendBinary_flip (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X))
    (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBinary F x y = extendBinary (flipBinarySeries F) y x := by
  let L := (restrictBilinear (linearApply (k := k) (V := V) (W := W →ₗ[k] X))).compr₂
    (restrictBilinear (linearApply (k := k) (V := W) (W := X)))
  let R₀ := ((restrictBilinear (linearApply (k := k) (V := W) (W := V →ₗ[k] X))).compr₂
    (restrictBilinear (linearApply (k := k) (V := V) (W := X)))).comp
      ((flipBinarySeries (k := k) (V := V) (W := W) (X := X)).restrictScalars k)
  let R := (LinearMap.lflip (R₀ := k)).toLinearMap.comp R₀
  have heq : L = R := by
    apply trilinear_ext_of_bounded _ _ 0
    · intro F x y B b c hF hx hy
      change BoundedBelow (((B + b) + c) + 0) (extendBinary F x y)
      simpa only [add_zero] using boundedBelow_extendBinary F x y hF hx hy
    · intro F x y B b c hF hx hy
      change BoundedBelow (((B + b) + c) + 0) (extendBinary (flipBinarySeries F) y x)
      have h := boundedBelow_extendBinary (flipBinarySeries F) y x
        (boundedBelow_map (LinearMap.lflip (R₀ := k)).toLinearMap hF) hy hx
      convert h using 1
      omega
    · intro B b c f x y
      change linearApply (linearApply (single B f) (single b x)) (single c y) =
        linearApply (linearApply (flipBinarySeries (single B f)) (single c y)) (single b x)
      change linearApply (linearApply (single B f) (single b x)) (single c y) =
        linearApply (linearApply (map (LinearMap.lflip (R₀ := k)).toLinearMap (single B f))
          (single c y)) (single b x)
      rw [map_single, linearApply_single, linearApply_single, linearApply_single, linearApply_single]
      congr 1
      omega
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun heq F) x) y

theorem extendBinary_precomp_left
    {V' : Type v} [AddCommGroup V'] [Module k V']
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (G : LaurentModule k (V' →ₗ[k] V))
    (x : LaurentModule k V') (y : LaurentModule k W) :
    extendBinary (linearCompose F G) x y = extendBinary F (linearApply G x) y := by
  rw [extendBinary_apply, linearApply_comp, ← extendBinary_apply]

def precomposeBinaryRight
    {W' : Type v} [AddCommGroup W'] [Module k W']
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (G : LaurentModule k (W' →ₗ[k] W)) :
    LaurentModule k (V →ₗ[k] W' →ₗ[k] X) :=
  flipBinarySeries (linearCompose (flipBinarySeries F) G)

theorem extendBinary_precomp_right
    {W' : Type v} [AddCommGroup W'] [Module k W']
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (G : LaurentModule k (W' →ₗ[k] W))
    (x : LaurentModule k V) (y : LaurentModule k W') :
    extendBinary (precomposeBinaryRight F G) x y = extendBinary F x (linearApply G y) := by
  change extendBinary (flipBinarySeries (linearCompose (flipBinarySeries F) G)) x y = _
  rw [← extendBinary_flip, extendBinary_precomp_left, ← extendBinary_flip]

def postcomposeBinary (G : LaurentModule k (X →ₗ[k] Y))
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) : LaurentModule k (V →ₗ[k] W →ₗ[k] Y) :=
  linearCompose (map (LinearMap.llcomp k W X Y) G) F

theorem extendBinary_postcomp (G : LaurentModule k (X →ₗ[k] Y))
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (x : LaurentModule k V) (y : LaurentModule k W) :
    extendBinary (postcomposeBinary G F) x y = linearApply G (extendBinary F x y) := by
  rw [extendBinary_apply, postcomposeBinary, linearApply_comp]
  have h : linearApply (map (LinearMap.llcomp k W X Y) G) (linearApply F x) =
      linearCompose G (linearApply F x) := by
    apply LaurentModule.ext
    intro d
    rfl
  rw [h, linearApply_comp, ← extendBinary_apply]

theorem extendBilinear_precomp_left
    {V' : Type v} [AddCommGroup V'] [Module k V']
    (f : V →ₗ[k] W →ₗ[k] X) (g : V' →ₗ[k] V)
    (x : LaurentModule k V') (y : LaurentModule k W) :
    extendBilinear f (map g x) y = extendBilinear (f.comp g) x y := by
  apply LaurentModule.ext
  intro d
  rfl

theorem extendBilinear_postcomp (f : V →ₗ[k] W →ₗ[k] X) (g : X →ₗ[k] Y)
    (x : LaurentModule k V) (y : LaurentModule k W) :
    map g (extendBilinear f x y) = extendBilinear (f.compr₂ g) x y := by
  rw [extendBilinear_apply, extendBilinear_apply, ← applyMultilinear_postcomp]
  congr 1

theorem linearApply_map_post (h : W →ₗ[k] X) (F : LaurentModule k (V →ₗ[k] W)) (x : LaurentModule k V) :
    linearApply (map (LinearMap.llcomp k V W X h) F) x = map h (linearApply F x) := by
  change extendBilinear (LinearMap.id : (V →ₗ[k] X) →ₗ[k] V →ₗ[k] X)
      (map (LinearMap.llcomp k V W X h) F) x =
    map h (extendBilinear (LinearMap.id : (V →ₗ[k] W) →ₗ[k] V →ₗ[k] W) F x)
  rw [extendBilinear_precomp_left, extendBilinear_postcomp]
  apply LaurentModule.ext
  intro d
  rfl

theorem coeff_extendBinary_constants (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X))
    (x : V) (y : W) (d : ℤ) :
    coeff (extendBinary F (single 0 x) (single 0 y)) d = coeff F d x y := by
  simp only [extendBinary_apply, linearApply_constant, coeff_map]
  rfl

theorem extendBinary_injective : Function.Injective (extendBinary (k := k) (V := V) (W := W) (X := X)) := by
  intro F G h
  apply LaurentModule.ext
  intro d
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hxy := congrArg
    (fun B : LaurentModule k V →ₗ[LaurentSeries k] LaurentModule k W →ₗ[LaurentSeries k] LaurentModule k X ↦
      coeff (B (single 0 x) (single 0 y)) d) h
  simpa only [coeff_extendBinary_constants] using hxy

theorem binaryEvaluation_injective :
    Function.Injective (binaryEvaluation (k := k) (V := V) (W := W) (X := X)) := extendBinary_injective

theorem boundedBelow_postcomposeBinary (G : LaurentModule k (X →ₗ[k] Y))
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) {B C : ℤ}
    (hG : BoundedBelow B G) (hF : BoundedBelow C F) :
    BoundedBelow (B + C) (postcomposeBinary G F) :=
  boundedBelow_linearCompose _ F (boundedBelow_map (LinearMap.llcomp k W X Y) hG) hF

theorem boundedBelow_precomposeBinaryRight
    {W' : Type v} [AddCommGroup W'] [Module k W']
    (F : LaurentModule k (V →ₗ[k] W →ₗ[k] X)) (G : LaurentModule k (W' →ₗ[k] W))
    {B C : ℤ} (hF : BoundedBelow B F) (hG : BoundedBelow C G) :
    BoundedBelow (B + C) (precomposeBinaryRight F G) := by
  unfold precomposeBinaryRight flipBinarySeries
  apply boundedBelow_map
  apply boundedBelow_linearCompose _ _ ?_ hG
  exact boundedBelow_map _ hF

theorem single_as_series_smul (e : ℤ) (x : V) :
    single e x = (HahnSeries.single e (1 : k) : LaurentSeries k) • (single 0 x : LaurentModule k V) := by
  apply LaurentModule.ext
  intro d
  rw [coeff_series_single_smul]
  by_cases h : d = e
  · subst d; simp
  · have h' : d - e ≠ 0 := sub_ne_zero.mpr h
    simp [h, h']

/-- Constant vectors recover the original coefficient operators of the actual Hahn action. -/
theorem coeff_operatorAction_constant (F : LaurentSeries (Module.End k V)) (x : V) (d : ℤ) :
    coeff (LaurentOperator.actionHom F (single 0 x)) d = F.coeff d x := by
  classical
  change ((HahnModule.of (Module.End k V)).symm
    (F • LaurentOperator.endModuleEquiv (single 0 x))).coeff d = _
  have hs : ((HahnModule.of (Module.End k V)).symm
      (LaurentOperator.endModuleEquiv (single 0 x))).support ⊆ ({0} : Set ℤ) :=
    HahnSeries.support_single_subset
  rw [HahnModule.coeff_smul_right (R := Module.End k V) (x := F)
    (y := LaurentOperator.endModuleEquiv (single 0 x)) (Set.isPWO_singleton 0) hs]
  rw [Finset.sum_eq_single (d, 0)]
  · change F.coeff d (coeff (single 0 x : LaurentModule k V) 0) = _
    simp
  · intro p hp hne
    have hp' := (Finset.mem_vaddAntidiagonal _ _).mp hp
    have hzero : p.2 = 0 := hp'.2.1
    have heq : p.1 + p.2 = d := hp'.2.2
    have hpair : p = (d, 0) := Prod.ext (by omega) hzero
    exact (hne hpair).elim
  · intro hnot
    have hzero : F.coeff d = 0 := by
      by_contra h
      apply hnot
      simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, Set.mem_singleton_iff,
        vadd_eq_add, add_zero]
      exact ⟨h, trivial, trivial⟩
    simp [hzero]

/-- The full-cochain unary evaluation agrees with the already verified operator ring action. -/
theorem linearApply_eq_actionHom (F : LaurentSeries (Module.End k V)) :
    linearApply (HahnModule.of k F) = LaurentOperator.actionHom F := by
  have hconstant (x : V) : linearApply (HahnModule.of k F) (single 0 x) =
      LaurentOperator.actionHom F (single 0 x) := by
    apply LaurentModule.ext
    intro d
    rw [linearApply_constant, coeff_map, coeff_operatorAction_constant]
    rfl
  have heq : (linearApply (HahnModule.of k F)).restrictScalars k =
      (LaurentOperator.actionHom F).restrictScalars k := by
    apply linear_ext_of_bounded _ _ F.order
    · intro b x hx
      change BoundedBelow (b + F.order) (linearApply (HahnModule.of k F) x)
      simpa only [add_comm] using boundedBelow_linearApply (B := F.order) (HahnModule.of k F) x
        (fun _ hd ↦ HahnSeries.coeff_eq_zero_of_lt_order (x := F) hd) hx
    · intro b x hx
      change BoundedBelow (b + F.order) (LaurentOperator.act F x)
      simpa only [add_comm] using LaurentOperator.boundedBelow_act F x
        (fun _ hd ↦ HahnSeries.coeff_eq_zero_of_lt_order hd) hx
    · intro e x
      change linearApply (HahnModule.of k F) (single e x) = LaurentOperator.actionHom F (single e x)
      rw [single_as_series_smul e x]
      simp only [map_smul, hconstant]
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun heq x

theorem linearApply_single_zero (f : V →ₗ[k] W) : linearApply (single 0 f) = map f := by
  have heq : (linearApply (single 0 f)).restrictScalars k = (map f).restrictScalars k := by
    apply linear_ext_of_bounded _ _ 0
    · intro b x hx
      change BoundedBelow (b + 0) (linearApply (single 0 f) x)
      simpa only [zero_add, add_zero] using boundedBelow_linearApply (single 0 f) x
        (boundedBelow_single 0 f) hx
    · intro b x hx
      change BoundedBelow (b + 0) (map f x)
      simpa only [add_zero] using boundedBelow_map f hx
    · intro e x
      change linearApply (single 0 f) (single e x) = map f (single e x)
      rw [linearApply_single, map_single, zero_add]
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun heq x

/-- Unary composition is exactly multiplication in the noncommutative Laurent operator ring. -/
theorem linearCompose_eq_multiplication (F G : LaurentSeries (Module.End k V)) :
    linearCompose (HahnModule.of k F) (HahnModule.of k G) = HahnModule.of k (F * G) := by
  apply linearApply_injective
  apply LinearMap.ext
  intro x
  rw [linearApply_comp, linearApply_eq_actionHom, linearApply_eq_actionHom, linearApply_eq_actionHom, map_mul]
  rfl

section Insertions

open EnvelopingIsomorphism.Deformation

variable {A : Type v} [AddCommGroup A] [Module k A]

def extendTernary (F : LaurentModule k (Ternary k A))
    (x y z : LaurentModule k A) : LaurentModule k A := linearApply (extendBinary F x y) z

/-- Linear evaluation of Laurent ternary coefficients into actual E-trilinear maps. -/
def ternaryEvaluation : LaurentModule k (Ternary k A) →ₗ[LaurentSeries k]
    Ternary (LaurentSeries k) (LaurentModule k A) :=
  (LinearMap.compRight (LaurentSeries k)
    (binaryEvaluation (k := k) (V := A) (W := A) (X := A))).comp
      (linearApply (k := k) (V := A) (W := Binary k A))

@[simp] theorem ternaryEvaluation_apply (F : LaurentModule k (Ternary k A))
    (x y z : LaurentModule k A) : ternaryEvaluation F x y z = extendTernary F x y z := rfl

theorem extendTernary_apply (F : LaurentModule k (Ternary k A)) (x y z : LaurentModule k A) :
    extendTernary F x y z = extendBinary (linearApply F x) y z := rfl

theorem boundedBelow_extendTernary (F : LaurentModule k (Ternary k A))
    (x y z : LaurentModule k A) {B b c d : ℤ} (hF : BoundedBelow (k := k) (X := Ternary k A) B F)
    (hx : BoundedBelow b x) (hy : BoundedBelow c y) (hz : BoundedBelow d z) :
    BoundedBelow (((B + b) + c) + d) (extendTernary F x y z) :=
  boundedBelow_linearApply _ z (boundedBelow_extendBinary F x y hF hx hy) hz

def flipTernaryInner : Ternary k A →ₗ[k] Ternary k A :=
  LinearMap.llcomp k A (Binary k A) (Binary k A) (LinearMap.lflip (R₀ := k)).toLinearMap

def rotateTernary : Ternary k A →ₗ[k] Ternary k A :=
  (LinearMap.lflip (R₀ := k)).toLinearMap.comp flipTernaryInner

@[simp] theorem flipTernaryInner_apply (F : Ternary k A) (a b c : A) : flipTernaryInner F a b c = F a c b := rfl
@[simp] theorem rotateTernary_apply (F : Ternary k A) (a b c : A) : rotateTernary F a b c = F b c a := rfl

theorem extendTernary_flipInner (F : LaurentModule k (Ternary k A)) (x y z : LaurentModule k A) :
    extendTernary (map (k := k) (X := Ternary k A) (Y := Ternary k A) flipTernaryInner F) x y z =
      extendTernary F x z y := by
  rw [extendTernary_apply, flipTernaryInner, linearApply_map_post]
  change extendBinary (flipBinarySeries (linearApply F x)) y z = _
  rw [← extendBinary_flip]
  rfl

theorem extendTernary_flipOuter (F : LaurentModule k (Ternary k A)) (x y z : LaurentModule k A) :
    extendTernary (flipBinarySeries F) x y z = extendTernary F y x z := by
  rw [extendTernary, ← extendBinary_flip]
  rfl

theorem extendTernary_rotate (F : LaurentModule k (Ternary k A)) (x y z : LaurentModule k A) :
    extendTernary (map (k := k) (X := Ternary k A) (Y := Ternary k A) rotateTernary F) x y z =
      extendTernary F y z x := by
  have h : map (k := k) (X := Ternary k A) (Y := Ternary k A) rotateTernary F =
      flipBinarySeries (map (k := k) (X := Ternary k A) (Y := Ternary k A) flipTernaryInner F) := by
    apply LaurentModule.ext (k := k) (X := Ternary k A)
    intro d
    rfl
  rw [h, extendTernary_flipOuter, extendTernary_flipInner]

def insertLeftCoefficient : Binary k A →ₗ[k] Binary k A →ₗ[k] Ternary k A where
  toFun B :=
    { toFun := insertLeft B
      map_add' _ _ := by ext a b c; simp
      map_smul' _ _ := by ext a b c; simp }
  map_add' _ _ := by ext C a b c; simp
  map_smul' _ _ := by ext C a b c; simp

def insertRightCoefficient : Binary k A →ₗ[k] Binary k A →ₗ[k] Ternary k A where
  toFun B :=
    { toFun := insertRight B
      map_add' _ _ := by ext a b c; simp
      map_smul' _ _ := by ext a b c; simp }
  map_add' _ _ := by ext C a b c; simp
  map_smul' _ _ := by ext C a b c; simp

/-- First-slot insertion of Laurent binary cochains, as an actual Laurent ternary cochain. -/
def insertLeftSeries (B C : LaurentModule k (Binary k A)) : LaurentModule k (Ternary k A) :=
  extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) insertLeftCoefficient B C

/-- Second-slot insertion of Laurent binary cochains, with the same common-bound discipline. -/
def insertRightSeries (B C : LaurentModule k (Binary k A)) : LaurentModule k (Ternary k A) :=
  extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) insertRightCoefficient B C

theorem coeff_insertLeftSeries (B C : LaurentModule k (Binary k A)) (d : ℤ) :
    coeff (k := k) (X := Ternary k A) (insertLeftSeries B C) d = ∑ᶠ a : Fin 2 → ℤ,
      if ∑ i, a i = d then insertLeft (coeff B (a 0)) (coeff C (a 1)) else 0 := rfl

theorem coeff_insertRightSeries (B C : LaurentModule k (Binary k A)) (d : ℤ) :
    coeff (k := k) (X := Ternary k A) (insertRightSeries B C) d = ∑ᶠ a : Fin 2 → ℤ,
      if ∑ i, a i = d then insertRight (coeff B (a 0)) (coeff C (a 1)) else 0 := rfl

-- Restrict speculative typeclass search through the nested linear-map coefficient types.
set_option maxSynthPendingDepth 3 in
theorem boundedBelow_insertLeftSeries (B C : LaurentModule k (Binary k A)) {b c : ℤ}
    (hB : BoundedBelow (k := k) (X := Binary k A) b B) (hC : BoundedBelow (k := k) (X := Binary k A) c C) :
    BoundedBelow (k := k) (X := Ternary k A) (b + c) (insertLeftSeries B C) :=
  boundedBelow_extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A)
    (insertLeftCoefficient (k := k) (A := A)) B C hB hC

set_option maxSynthPendingDepth 3 in
theorem boundedBelow_insertRightSeries (B C : LaurentModule k (Binary k A)) {b c : ℤ}
    (hB : BoundedBelow (k := k) (X := Binary k A) b B) (hC : BoundedBelow (k := k) (X := Binary k A) c C) :
    BoundedBelow (k := k) (X := Ternary k A) (b + c) (insertRightSeries B C) :=
  boundedBelow_extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A)
    (insertRightCoefficient (k := k) (A := A)) B C hB hC

theorem insertLeftSeries_eq_postcomposeBinary (B C : LaurentModule k (Binary k A)) :
    insertLeftSeries B C = postcomposeBinary B C := by
  apply LaurentModule.ext (k := k) (X := Ternary k A)
  intro d
  simp only [insertLeftSeries, postcomposeBinary, linearCompose, coeff_extendBilinear, coeff_map]
  apply finsum_congr
  intro a
  split <;> rfl

theorem insertRightSeries_eq_rotate (B C : LaurentModule k (Binary k A)) :
    insertRightSeries B C = map (k := k) (X := Ternary k A) (Y := Ternary k A) rotateTernary
      (insertLeftSeries (flipBinarySeries B) C) := by
  unfold insertRightSeries insertLeftSeries
  rw [extendBilinear_postcomp]
  change extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A)
      (insertRightCoefficient (k := k) (A := A)) B C =
    extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A)
      ((insertLeftCoefficient (k := k) (A := A)).compr₂ (rotateTernary (k := k) (A := A)))
      (map (k := k) (X := Binary k A) (Y := Binary k A) (LinearMap.lflip (R₀ := k)).toLinearMap B) C
  rw [extendBilinear_precomp_left]
  apply congrArg (fun f : Binary k A →ₗ[k] Binary k A →ₗ[k] Ternary k A ↦
    extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) f B C)
  ext μ ν a b c
  rfl

/-- Closure agrees with genuine composition of the evaluated binary operations. -/
theorem extendTernary_insertLeft (B C : LaurentModule k (Binary k A)) (x y z : LaurentModule k A) :
    extendTernary (insertLeftSeries B C) x y z = extendBinary B (extendBinary C x y) z := by
  rw [insertLeftSeries_eq_postcomposeBinary, extendTernary, extendBinary_postcomp]
  rfl

theorem extendTernary_insertRight (B C : LaurentModule k (Binary k A)) (x y z : LaurentModule k A) :
    extendTernary (insertRightSeries B C) x y z = extendBinary B x (extendBinary C y z) := by
  rw [insertRightSeries_eq_rotate, extendTernary_rotate, extendTernary_insertLeft, ← extendBinary_flip]

theorem coeff_extendTernary_constants (F : LaurentModule k (Ternary k A)) (a b c : A) (d : ℤ) :
    coeff (extendTernary F (single 0 a) (single 0 b) (single 0 c)) d =
      coeff (k := k) (X := Ternary k A) F d a b c := by
  simp only [extendTernary, extendBinary_apply, linearApply_constant, coeff_map]
  rfl

theorem extendTernary_injective :
    Function.Injective (fun F : LaurentModule k (Ternary k A) ↦
      fun x y z : LaurentModule k A ↦ extendTernary F x y z) := by
  intro F G h
  apply LaurentModule.ext (k := k) (X := Ternary k A)
  intro d
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro c
  have he := congrArg (fun H : LaurentModule k A → LaurentModule k A → LaurentModule k A → LaurentModule k A ↦
    coeff (H (single 0 a) (single 0 b) (single 0 c)) d) h
  simpa only [coeff_extendTernary_constants] using he

theorem ternaryEvaluation_injective : Function.Injective (ternaryEvaluation (k := k) (A := A)) := by
  intro F G h
  apply extendTernary_injective
  funext x y z
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun h x) y) z

theorem ternaryEvaluation_insertLeft (B C : LaurentModule k (Binary k A)) :
    ternaryEvaluation (insertLeftSeries B C) = insertLeft (binaryEvaluation B) (binaryEvaluation C) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  exact extendTernary_insertLeft B C x y z

theorem ternaryEvaluation_insertRight (B C : LaurentModule k (Binary k A)) :
    ternaryEvaluation (insertRightSeries B C) = insertRight (binaryEvaluation B) (binaryEvaluation C) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  exact extendTernary_insertRight B C x y z

/-- Signed binary insertion, as a closed Laurent-cochain operation. -/
def insertBinarySeries : LaurentModule k (Binary k A) →ₗ[LaurentSeries k]
    LaurentModule k (Binary k A) →ₗ[LaurentSeries k] LaurentModule k (Ternary k A) :=
  extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) insertLeftCoefficient -
    extendBilinear (k := k) (X := Binary k A) (Y := Binary k A) (Z := Ternary k A) insertRightCoefficient

set_option maxSynthPendingDepth 3 in
theorem insertBinarySeries_apply (B C : LaurentModule k (Binary k A)) :
    insertBinarySeries (k := k) (A := A) B C =
      (insertLeftSeries (k := k) (A := A) B C - insertRightSeries (k := k) (A := A) B C :
        LaurentModule k (Ternary k A)) := rfl

set_option maxSynthPendingDepth 3 in
theorem ternaryEvaluation_insertBinary (B C : LaurentModule k (Binary k A)) :
    ternaryEvaluation (insertBinarySeries B C) = insertBinary (binaryEvaluation B) (binaryEvaluation C) := by
  rw [insertBinarySeries_apply, map_sub, ternaryEvaluation_insertLeft, ternaryEvaluation_insertRight]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  rfl

/-- The binary-cochain Hochschild differential around a Laurent binary base point. -/
def differentialBinarySeries (μ : LaurentModule k (Binary k A)) :
    LaurentModule k (Binary k A) →ₗ[LaurentSeries k] LaurentModule k (Ternary k A) :=
  insertBinarySeries μ + (insertBinarySeries (k := k) (A := A)).flip μ

set_option maxSynthPendingDepth 3 in
theorem ternaryEvaluation_differentialBinarySeries (μ B : LaurentModule k (Binary k A)) :
    ternaryEvaluation (differentialBinarySeries μ B) =
      differentialTwo (binaryEvaluation μ) (binaryEvaluation B) := by
  rw [differentialBinarySeries, LinearMap.add_apply, LinearMap.flip_apply, map_add,
    ternaryEvaluation_insertBinary, ternaryEvaluation_insertBinary]
  rfl

end Insertions

end EnvelopingIsomorphism.FormalSeries.LaurentModule
