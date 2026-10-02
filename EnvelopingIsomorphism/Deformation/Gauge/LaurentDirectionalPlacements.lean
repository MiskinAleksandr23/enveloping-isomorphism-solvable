import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity
import EnvelopingIsomorphism.Deformation.Gauge.TaylorDirectionalPath
import EnvelopingIsomorphism.FormalSeries.PolynomialDirectionalIdentity

/-! Finite-arity directional recombination of every actual placement. The
finite degree-one polynomial argument precedes t/h coefficient truncation,
so it introduces no uniform third-parameter bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalPlacements

open EnvelopingIsomorphism.FormalSeries PolynomialDirectionalIdentity
open scoped BigOperators Classical

section CoefficientOperation

variable {E V W : Type*} [CommRing E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

def coefficientOperation {r : ℕ} (F : MultilinearMap E (fun _ : Fin r => V) W) (D : ℕ) :
    MultilinearMap E (fun _ : Fin r => PowerSeriesModule E V) W :=
  (PowerSeriesModule.coefficient D).compMultilinearMap ((PowerSeriesModule.extendMultilinear F).restrictScalars E)

def directionalTerm {r : ℕ} (F : MultilinearMap E (fun _ : Fin r => V) W)
    (β δ : PowerSeriesModule E V) : PowerSeriesModule E W :=
  ∑ i : Fin r, PowerSeriesModule.applyMultilinear F (Function.update (fun _ => β) i δ)

theorem coefficient_directionalTerm {r : ℕ} (F : MultilinearMap E (fun _ : Fin r => V) W)
    (β δ : PowerSeriesModule E V) (D : ℕ) :
    PowerSeriesModule.coeffV D (directionalTerm F β δ) = directional (coefficientOperation F D) β δ := by
  simp only [directionalTerm, PowerSeriesModule.coeffV_sum, directional, coefficientOperation,
    LinearMap.compMultilinearMap_apply, MultilinearMap.coe_restrictScalars, PowerSeriesModule.extendMultilinear_apply]
  rfl

end CoefficientOperation

section Laurent

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem infinite_laurentSeries : Infinite (LaurentSeries k) :=
  Infinite.of_injective (fun a : ℤ => (HahnSeries.single a (1 : k) : LaurentSeries k)) (fun a b h => by
    have ho := congrArg HahnSeries.order h
    simpa only [HahnSeries.order_single one_ne_zero, WithTop.coe_inj] using ho)

theorem directional_arity_eq_placements
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D m : ℕ) :
    PowerSeriesModule.coeffV D (directionalTerm (LaurentModule.extendScalars (C m))
      (LaurentTaylorArityBounds.fullInput π₀ β) δ) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, if p.1 = 0 then 0 else
        PowerSeriesModule.coeffV D (directionalTerm
          (placementComponent (fun r => LaurentModule.extendScalars (C r)) (LaurentModule.single 1 π₀)
            p.1 (p.1 + p.2)) β δ) := by
  letI : Infinite (LaurentSeries k) := infinite_laurentSeries (k := k)
  let CE : GraphTaylorFamily (k := LaurentSeries k) (V := LaurentModule k V) (W := LaurentModule k W) :=
    fun r => LaurentModule.extendScalars (C r)
  let a : PowerSeriesModule (LaurentSeries k) (LaurentModule k V) :=
    PowerSeriesModule.single 0 (LaurentModule.single (k := k) 1 π₀)
  let G (p : ℕ × ℕ) : MultilinearMap (LaurentSeries k)
      (fun _ : Fin p.1 => PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (LaurentModule k W) :=
    if p.1 = 0 then 0 else coefficientOperation
      (placementComponent CE (LaurentModule.single 1 π₀) p.1 (p.1 + p.2)) D
  have ht (z : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
      coefficientOperation (CE m) D (fun _ => a + z) - coefficientOperation (CE m) D (fun _ => a) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, G p (fun _ => z) := by
    change PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear (CE m) (fun _ => a + z)) -
      PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear (CE m) (fun _ => a)) = _
    rw [← twistedMCCoefficient_translation CE (LaurentModule.single 1 π₀) z m D,
      twistedMCCoefficient_eq_components]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hr : p.1 = 0
    · simp [G, hr]
    · simp only [G, if_neg hr]
      rfl
  have hd := directional_of_finite_translation (Finset.HasAntidiagonal.antidiagonal m) Prod.fst
    (coefficientOperation (CE m) D) G a β δ ht
  rw [coefficient_directionalTerm]
  change directional (coefficientOperation (CE m) D) (a + β) δ = _
  rw [hd]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hr : p.1 = 0
  · simp [G, hr, directional]
  · simp only [G, if_neg hr, ← coefficient_directionalTerm]
    rfl

end Laurent

end EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalPlacements
