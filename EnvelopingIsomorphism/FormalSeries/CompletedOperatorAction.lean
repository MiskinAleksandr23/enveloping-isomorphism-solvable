import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

/-! Genuine operator series in two formal parameters and their action on completed modules. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.CompletedOperator

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

/-- The outer parameter has power-series support; each coefficient has Laurent support. -/
abbrev Operators (k A : Type*) [CommRing k] [AddCommGroup A] [Module k A] :=
  PowerSeries (LaurentSeries (Module.End k A))

/-- Completed vectors retain the genuine Laurent support condition. -/
abbrev Vectors (k A : Type*) [CommRing k] [AddCommGroup A] [Module k A] :=
  PowerSeriesModule (LaurentSeries k) (LaurentModule k A)

-- Pin the native Hahn ring to avoid competing inferred zero instances on `Module.End`.
scoped instance operatorLaurentRing : Ring (LaurentSeries (Module.End k A)) :=
  HahnSeries.instRing (Γ := ℤ) (R := Module.End k A)

open scoped CompletedOperator

/-- The action is linear over the full scalar power-series ring. -/
def actionHom : Operators k A →+*
    Module.End (PowerSeries (LaurentSeries k)) (Vectors k A) where
  toFun F :=
    { toFun := PowerSeriesModule.actV (PowerSeries.map LaurentOperator.actionHom F)
      map_add' := PowerSeriesModule.actV_add_right _
      map_smul' := PowerSeriesModule.actV_series_smul _ }
  map_one' := by ext x; simp
  map_mul' F G := by
    apply LinearMap.ext
    intro x
    simp only [map_mul, Module.End.mul_apply]
    exact PowerSeriesModule.actV_mul _ _ x
  map_zero' := by ext x; simp
  map_add' F G := by
    apply LinearMap.ext
    intro x
    simp only [map_add, LinearMap.add_apply]
    exact PowerSeriesModule.actV_add_left _ _ x

@[simp] theorem actionHom_apply (F : Operators k A) (x : Vectors k A) :
    actionHom F x = PowerSeriesModule.actV
      (PowerSeries.map LaurentOperator.actionHom F) x := rfl

/-- An invertible operator series acts by an actual linear equivalence on the completion. -/
def actionEquiv (F : (Operators k A)ˣ) :
    Vectors k A ≃ₗ[PowerSeries (LaurentSeries k)] Vectors k A where
  toLinearMap := actionHom (F : Operators k A)
  invFun := actionHom (↑(F⁻¹) : Operators k A)
  left_inv x := by
    change (actionHom (↑(F⁻¹) : Operators k A) * actionHom (F : Operators k A)) x = x
    rw [← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
  right_inv x := by
    change (actionHom (F : Operators k A) * actionHom (↑(F⁻¹) : Operators k A)) x = x
    rw [← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

@[simp] theorem actionEquiv_apply (F : (Operators k A)ˣ) (x : Vectors k A) :
    actionEquiv F x = actionHom (F : Operators k A) x := rfl

@[simp] theorem actionEquiv_symm_apply (F : (Operators k A)ˣ) (x : Vectors k A) :
    (actionEquiv F).symm x = actionHom (↑(F⁻¹) : Operators k A) x := rfl

@[simp] theorem actionEquiv_mul_apply (F G : (Operators k A)ˣ) (x : Vectors k A) :
    actionEquiv (F * G) x = actionEquiv F (actionEquiv G x) := by
  simp only [actionEquiv_apply, Units.val_mul, map_mul, Module.End.mul_apply]

@[simp] theorem actionEquiv_inv (F : (Operators k A)ˣ) :
    actionEquiv F⁻¹ = (actionEquiv F).symm := by ext x; rfl

/-- A coefficient vector is included as the constant series in both parameters. -/
def constant (a : A) : Vectors k A :=
  PowerSeriesModule.single 0 (LaurentModule.single 0 a)

theorem coeff_action_constant (F : Operators k A) (a : A) (r : ℕ) (j : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV r (actionHom F (constant a))) j =
      (PowerSeries.coeff r F).coeff j a := by
  rw [actionHom_apply, PowerSeriesModule.coeffV_actV]
  simp only [constant, PowerSeriesModule.coeffV_single, PowerSeries.coeff_map]
  rw [Finset.sum_eq_single (r, 0)]
  · simp only [ite_true]
    exact LaurentModule.coeff_operatorAction_constant _ _ _
  · intro ij hij hne
    have hs : ij.1 + ij.2 = r := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hsecond : ij.2 ≠ 0 := by
      intro hz
      apply hne
      exact Prod.ext (by simpa [hz] using hs) hz
    simp [hsecond]
  · simp

/-- Operator equality is detected on vectors constant in both parameters. -/
theorem ext_on_constants {F G : Operators k A}
    (h : ∀ a, actionHom F (constant a) = actionHom G (constant a)) : F = G := by
  apply PowerSeries.ext
  intro r
  apply HahnSeries.ext
  funext j
  apply LinearMap.ext
  intro a
  have he := congrArg (fun x ↦ LaurentModule.coeff (PowerSeriesModule.coeffV r x) j) (h a)
  simpa only [coeff_action_constant] using he

theorem actionHom_injective : Function.Injective (actionHom (k := k) (A := A)) := by
  intro F G h
  exact ext_on_constants (fun a ↦ LinearMap.congr_fun h (constant a))

end EnvelopingIsomorphism.FormalSeries.CompletedOperator
