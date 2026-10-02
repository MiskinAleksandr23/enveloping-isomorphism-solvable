import EnvelopingIsomorphism.FormalSeries.Module

/-!
Laurent series of endomorphisms act on actual Laurent modules by convolution.
Multiplication acts as composition. Coefficient modules may be infinite-dimensional.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentOperator

open LaurentModule

variable {k X : Type*} [CommRing k] [AddCommGroup X] [Module k X]

/-- Changing the coefficient scalar parameter of a Hahn module preserves its vectors. -/
def endModuleEquiv : LaurentModule k X ≃+ HahnModule ℤ (Module.End k X) X where
  toEquiv := (HahnModule.of k).symm.trans (HahnModule.of (Module.End k X))
  map_add' _ _ := rfl

/-- The actual Hahn convolution action of a lower-bounded series of operators. -/
def act (F : LaurentSeries (Module.End k X)) (x : LaurentModule k X) : LaurentModule k X :=
  endModuleEquiv.symm (F • endModuleEquiv x)

theorem coeff_act (F : LaurentSeries (Module.End k X)) (x : LaurentModule k X) (d : ℤ) :
    coeff (act F x) d =
      ∑ p ∈ Finset.VAddAntidiagonal d (Set.VAddAntidiagonal.finite_of_isPWO
        F.isPWO_support ((HahnModule.of k).symm x).isPWO_support d),
        F.coeff p.1 (coeff x p.2) := rfl

@[simp] theorem act_one (x : LaurentModule k X) : act (1 : LaurentSeries (Module.End k X)) x = x := by
  simp [act]

theorem act_mul (F G : LaurentSeries (Module.End k X)) (x : LaurentModule k X) :
    act (F * G) x = act F (act G x) := by
  simp only [act, AddEquiv.apply_symm_apply]
  exact congrArg (endModuleEquiv (k := k) (X := X)).symm (mul_smul F G (endModuleEquiv x))

@[simp] theorem act_zero_left (x : LaurentModule k X) :
    act (0 : LaurentSeries (Module.End k X)) x = 0 := by simp [act]

@[simp] theorem act_zero_right (F : LaurentSeries (Module.End k X)) : act F 0 = 0 := by
  simp [act]

theorem act_add_left (F G : LaurentSeries (Module.End k X)) (x : LaurentModule k X) :
    act (F + G) x = act F x + act G x := by simp [act, add_smul]

theorem act_add_right (F : LaurentSeries (Module.End k X)) (x y : LaurentModule k X) :
    act F (x + y) = act F x + act F y := by simp [act, smul_add]

theorem act_smul_right (F : LaurentSeries (Module.End k X)) (c : k) (x : LaurentModule k X) :
    act F (c • x) = c • act F x := by
  apply LaurentModule.ext
  intro d
  change ((HahnModule.of (Module.End k X)).symm (F • endModuleEquiv (c • x))).coeff d =
    c • ((HahnModule.of (Module.End k X)).symm (F • endModuleEquiv x)).coeff d
  have hs : ((HahnModule.of (Module.End k X)).symm (endModuleEquiv (c • x))).support ⊆
      ((HahnModule.of k).symm x).support := by
    intro j hj
    change c • coeff x j ≠ 0 at hj
    intro hz
    change coeff x j = 0 at hz
    exact hj (by rw [hz, smul_zero])
  rw [HahnModule.coeff_smul_right (R := Module.End k X) (x := F)
    (y := endModuleEquiv (c • x)) ((HahnModule.of k).symm x).isPWO_support hs]
  rw [HahnModule.coeff_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact (F.coeff p.1).map_smul c (coeff x p.2)

/-- Preliminary coefficient-linear action; its multiplication law comes from the Hahn module. -/
def actionKHom : LaurentSeries (Module.End k X) →+* Module.End k (LaurentModule k X) where
  toFun F :=
    { toFun := act F
      map_add' := act_add_right F
      map_smul' := act_smul_right F }
  map_one' := LinearMap.ext act_one
  map_mul' F G := LinearMap.ext (act_mul F G)
  map_zero' := LinearMap.ext act_zero_left
  map_add' F G := LinearMap.ext (act_add_left F G)

theorem boundedBelow_act (F : LaurentSeries (Module.End k X)) (x : LaurentModule k X)
    {B b : ℤ} (hF : ∀ d < B, F.coeff d = 0) (hx : BoundedBelow b x) :
    BoundedBelow (B + b) (act F x) := by
  intro d hd
  rw [coeff_act]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := (Finset.mem_vaddAntidiagonal _ _).mp hp
  have heq : p.1 + p.2 = d := hp'.2.2
  by_cases h : p.1 < B
  · rw [hF _ h]; rfl
  · have h' : p.2 < b := by omega
    rw [hx _ h', map_zero]

/-- Action of a monomial operator has the expected shifted coefficient formula. -/
theorem coeff_act_single (e : ℤ) (T : Module.End k X) (x : LaurentModule k X) (d : ℤ) :
    coeff (act (HahnSeries.single e T) x) d = T (coeff x (d - e)) := by
  have h := HahnModule.coeff_single_smul_vadd (R := Module.End k X)
    (x := endModuleEquiv x) (r := T) (b := e) (a := d - e)
  convert h using 1
  · congr 1
    simp only [vadd_eq_add, add_sub_cancel]
  · rfl

/-- Scalar monomials act as monomials of scalar endomorphisms. -/
theorem act_scalar_single (e : ℤ) (c : k) (x : LaurentModule k X) :
    act (HahnSeries.single e (c • (1 : Module.End k X))) x = HahnSeries.single e c • x := by
  apply LaurentModule.ext
  intro d
  rw [coeff_act_single, coeff_series_single_smul]
  rfl

theorem commute_scalar_single (F : LaurentSeries (Module.End k X)) (e : ℤ) (c : k) :
    F * HahnSeries.single e (c • (1 : Module.End k X)) =
      HahnSeries.single e (c • (1 : Module.End k X)) * F := by
  apply HahnSeries.ext
  funext d
  rw [HahnSeries.coeff_mul_single, HahnSeries.coeff_single_mul]
  apply LinearMap.ext
  intro x
  exact (F.coeff (d - e)).map_smul c x

/-- The operator action is linear over the full Laurent scalar ring. -/
theorem act_series_smul (F : LaurentSeries (Module.End k X)) (a : LaurentSeries k)
    (x : LaurentModule k X) : act F (a • x) = a • act F x := by
  apply map_series_smul_of_bounded (actionKHom F) F.order
  · intro b y hy
    change BoundedBelow (b + F.order) (act F y)
    simpa only [add_comm] using boundedBelow_act F y
      (fun _ hd ↦ HahnSeries.coeff_eq_zero_of_lt_order hd) hy
  · intro e c y
    change act F (HahnSeries.single e c • y) = HahnSeries.single e c • act F y
    rw [← act_scalar_single, ← act_mul, commute_scalar_single, act_mul, act_scalar_single]

/-- Ring homomorphism from actual Laurent operator series to Laurent-linear endomorphisms. -/
def actionHom : LaurentSeries (Module.End k X) →+* Module.End (LaurentSeries k) (LaurentModule k X) where
  toFun F :=
    { toFun := act F
      map_add' := act_add_right F
      map_smul' := act_series_smul F }
  map_one' := LinearMap.ext act_one
  map_mul' F G := LinearMap.ext (act_mul F G)
  map_zero' := LinearMap.ext act_zero_left
  map_add' F G := LinearMap.ext (act_add_left F G)

@[simp] theorem actionHom_apply (F : LaurentSeries (Module.End k X)) (x : LaurentModule k X) :
    actionHom F x = act F x := rfl

/-- Constant operator series act by coefficientwise extension of the operator. -/
@[simp] theorem actionHom_C (T : Module.End k X) :
    actionHom (HahnSeries.C T) = LaurentModule.map T := by
  apply LinearMap.ext
  intro x
  apply LaurentModule.ext
  intro d
  change coeff (act (HahnSeries.single 0 T) x) d = T (coeff x d)
  rw [coeff_act_single, sub_zero]

end EnvelopingIsomorphism.FormalSeries.LaurentOperator
