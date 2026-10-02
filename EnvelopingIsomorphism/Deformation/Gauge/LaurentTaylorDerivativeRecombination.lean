import EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalTruncation

/-! The actual ordered Taylor derivative equals the all-arity directional
graph expansion, coefficient by coefficient, on arbitrary positive-t Laurent
inputs. All t/h cutoffs and allarity finite support are proved internally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorDerivativeRecombination

open EnvelopingIsomorphism.FormalSeries LaurentDirectionalPlacements LaurentDirectionalTruncation
open LaurentTaylorArityBounds
open LaurentPlacementRecombination (coeff_sum)
open scoped BigOperators Classical

section Scaling

variable {E A B : Type*} [CommRing E] [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]

theorem directionalTerm_smul {r : ℕ} (F : MultilinearMap E (fun _ : Fin r => A) B)
    (s : E) (β δ : PowerSeriesModule E A) :
    directionalTerm (s • F) β δ = s • directionalTerm F β δ := by
  unfold directionalTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (PowerSeriesModule.applyMultilinearLinear (Function.update (fun _ => β) i δ)).map_smul s F

end Scaling

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem component_shift_coefficient
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (directionalTerm
      (placementComponent (fun m => LaurentModule.extendScalars (C m))
        (LaurentModule.single 1 π₀) r (r + j)) β δ)) H = componentCoefficient C π₀ β δ D r j H := by
  rw [placementComponent_extendScalars_add_single_one, directionalTerm_smul,
    PowerSeriesModule.coeffV_smul, LaurentModule.coeff_series_single_smul, one_smul]
  rfl

def arityCoefficient (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D m : ℕ) (H : ℤ) : W :=
  LaurentModule.coeff (PowerSeriesModule.coeffV D (directionalTerm
    (LaurentModule.extendScalars (C m)) (fullInput π₀ β) δ)) H

theorem arityCoefficient_eq_components
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D m : ℕ) (H : ℤ) :
    arityCoefficient C π₀ β δ D m H =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        if p.1 = 0 then 0 else componentCoefficient C π₀ β δ D p.1 p.2 H := by
  rw [arityCoefficient, directional_arity_eq_placements, coeff_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hr : p.1 = 0
  · simp only [if_pos hr, LaurentModule.coeff_zero]
  · simp only [if_neg hr]
    exact component_shift_coefficient C π₀ β δ D p.1 p.2 H

/-- Full directional arity support inherits the genuine placement bounds
through the proved finite identity; no separate summability premise is used. -/
theorem arityCoefficient_zero_of_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0)
    (D m : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ))
    (hm : arityCutoff D H L ≤ m) : arityCoefficient C π₀ β δ D m H = 0 := by
  rw [arityCoefficient_eq_components]
  apply Finset.sum_eq_zero
  intro p hp
  have hcount := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases hr : p.1 = 0
  · exact if_pos hr
  · rw [if_neg hr]
    apply componentCoefficient_zero_of_total_cutoff C π₀ β δ hβ hδ D p.1 p.2 H L hL hβL hδL
    simpa only [hcount] using hm

theorem arityCoefficient_finiteSupport
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0) (D : ℕ) (H : ℤ) :
    (Function.support (fun m => arityCoefficient C π₀ β δ D m H)).Finite := by
  obtain ⟨L, hL, hβL, hδL⟩ := exists_common_jet_bound β δ D
  apply (Finset.finite_toSet (Finset.range (arityCutoff D H L))).subset
  intro m hm
  by_contra hn
  exact hm (arityCoefficient_zero_of_cutoff C π₀ β δ hβ hδ D m H L hL hβL hδL (by simpa using hn))

theorem finsum_arityCoefficient_eq_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0)
    (D : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ)) :
    (∑ᶠ m : ℕ, arityCoefficient C π₀ β δ D m H) =
      ∑ m ∈ Finset.range (arityCutoff D H L), arityCoefficient C π₀ β δ D m H := by
  apply finsum_eq_sum_of_support_subset
  intro m hm
  by_contra hn
  exact hm (arityCoefficient_zero_of_cutoff C π₀ β δ hβ hδ D m H L hL hβL hδL (by simpa using hn))

/-- Literal coefficientwise all-arity recombination of the actual ordered
Taylor directional derivative, preserving every original distinguished slot.
Neither beta nor delta is assumed positive in h. -/
theorem coeff_taylorDerivative_eq_allArity
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0) (D : ℕ) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (taylorDerivativeApply (laurentPlacementTaylorFamily C π₀) β δ)) H =
      ∑ᶠ m : ℕ, LaurentModule.coeff (PowerSeriesModule.coeffV D
        (∑ i : Fin m, PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars (C m))
          (Function.update (fun _ => fullInput π₀ β) i δ))) H := by
  obtain ⟨L, hL, hβL, hδL⟩ := exists_common_jet_bound β δ D
  change _ = ∑ᶠ m : ℕ, arityCoefficient C π₀ β δ D m H
  rw [coeff_taylorDerivative_common_cutoff C π₀ β δ hβ hδ D H L hL hβL hδL,
    finsum_arityCoefficient_eq_cutoff C π₀ β δ hβ hδ D H L hL hβL hδL]
  symm
  simp_rw [arityCoefficient_eq_components]
  apply taylor_total_arity_reindex (fun r j => componentCoefficient C π₀ β δ D r j H) D (arityCutoff D H L)
  · intro r j hr
    exact componentCoefficient_zero_of_large_arity C π₀ β δ hβ hδ D r j H hr
  · intro r j hm
    exact componentCoefficient_zero_of_total_cutoff C π₀ β δ hβ hδ D r j H L hL hβL hδL hm

end EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorDerivativeRecombination
