import EnvelopingIsomorphism.Deformation.Gauge.LaurentPlacementRecombination
import EnvelopingIsomorphism.Deformation.Gauge.LaurentPlacementPartialEvaluation
import EnvelopingIsomorphism.Deformation.Gauge.TaylorTotalArityReindex
import EnvelopingIsomorphism.FormalSeries.PowerSeriesGroupedMultilinear

/-! Actual all-placement Taylor translation on arbitrary Laurent perturbations.
Both t and h cutoffs are proved from the real input bounds. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity
open EnvelopingIsomorphism.FormalSeries
open LaurentTaylorArityBounds LaurentFullGraphEvaluation LaurentPlacementRecombination
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Fixing a base h monomial at j complementary vertices produces the exact
h^j factor inside the actual t-completed placement evaluation. -/
theorem component_shift_coefficient
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear
      (placementComponent (fun m ↦ LaurentModule.extendScalars (C m))
        (LaurentModule.single 1 π₀) r (r + j)) (fun _ ↦ β))) H =
      componentCoefficient C π₀ β D r j H := by
  rw [placementComponent_extendScalars_add_single_one]
  have hs := (PowerSeriesModule.applyMultilinearLinear (fun _ : Fin r ↦ β)).map_smul
    (HahnSeries.single (j : ℤ) (1 : k) : LaurentSeries k)
    (LaurentModule.extendScalars (placementComponent C π₀ r (r + j)))
  change PowerSeriesModule.applyMultilinear
      ((HahnSeries.single (j : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.extendScalars (placementComponent C π₀ r (r + j))) (fun _ ↦ β) =
      (HahnSeries.single (j : ℤ) (1 : k) : LaurentSeries k) •
        PowerSeriesModule.applyMultilinear
          (LaurentModule.extendScalars (placementComponent C π₀ r (r + j))) (fun _ ↦ β) at hs
  rw [hs, PowerSeriesModule.coeffV_smul, LaurentModule.coeff_series_single_smul, one_smul]
  rfl

private theorem constant_input_coeff_zero {m : ℕ}
    (F : MultilinearMap (LaurentSeries k) (fun _ : Fin m ↦ LaurentModule k V) (LaurentModule k W))
    (a : LaurentModule k V) (D : ℕ) (hD : D ≠ 0) :
    PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear F
      (fun _ ↦ PowerSeriesModule.single 0 a)) = 0 := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  rw [PowerSeriesModule.coeffV_applyMultilinear]
  apply Finset.sum_eq_zero
  intro p hp
  have hn : ¬ ∀ i, p i = 0 := by
    intro hz
    have hsum := (Finset.mem_piAntidiag.mp hp).1
    exact hD (by simpa [hz] using hsum.symm)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  exact F.map_coord_zero i (by simp [hi])

/-- At positive t degree, each fixed total graph arity is exactly its finite
sum of nonempty placements, with all actual h shifts retained. -/
theorem arityTerm_coefficient_eq_placements
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D m : ℕ)
    (hD : D ≠ 0) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (arityTerm C (fullInput π₀ β) m)) H =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        if p.1 = 0 then 0 else componentCoefficient C π₀ β D p.1 p.2 H := by
  have ht := twistedMCCoefficient_translation
    (fun m ↦ LaurentModule.extendScalars (C m)) (LaurentModule.single 1 π₀) β m D
  rw [constant_input_coeff_zero _ _ D hD, sub_zero] at ht
  change LaurentModule.coeff (PowerSeriesModule.coeffV D
    (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars (C m))
      (fun _ ↦ PowerSeriesModule.single 0 (LaurentModule.single 1 π₀) + β))) H = _
  rw [← ht, twistedMCCoefficient_eq_components, coeff_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r, j⟩ hp
  have hcount := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change r + j = m at hcount
  subst m
  by_cases hr : r = 0
  · simp [hr]
  · simp only [if_neg hr]
    exact component_shift_coefficient C π₀ β D r j H

/-- The full all-arity graph series equals the existing base plus the actual
Laurent placement Taylor family, for every positive-t Laurent perturbation. -/
theorem fullEvaluation_eq_base_add_taylor
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    fullEvaluation C π₀ β hβ =
      PowerSeriesModule.single 0 (MiddleExactPerturbation.toLaurent (baseMCImage C π₀)) +
        taylorApply (laurentPlacementTaylorFamily C π₀) β := by
  apply PowerSeriesModule.ext
  intro D
  by_cases hD : D = 0
  · subst D
    rw [fullEvaluation_constantCoeff, PowerSeriesModule.coeffV_add,
      taylorApply_constantCoeff, PowerSeriesModule.coeffV_single, if_pos rfl, add_zero]
  · rw [PowerSeriesModule.coeffV_add, PowerSeriesModule.coeffV_single, if_neg hD, zero_add]
    apply LaurentModule.ext
    intro H
    obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
    rw [fullEvaluation_coeff_cutoff C π₀ β hβ D H L hL hβL,
      coeff_taylorApply_common_cutoff C π₀ β hβ D H L hL hβL]
    simp_rw [arityTerm_coefficient_eq_placements C π₀ β D _ hD H]
    apply taylor_total_arity_reindex (fun r j ↦ componentCoefficient C π₀ β D r j H)
      D (arityCutoff D H L)
    · intro r j hr
      exact componentCoefficient_zero_of_large_arity C π₀ β hβ D r j H hr
    · intro r j hm
      exact componentCoefficient_zero_of_total_cutoff C π₀ β hβ D r j H L hL hβL hm

/-- Direct interface for the literal target perturbation in CanonicalGraph.MCIdentity. -/
theorem taylorApply_eq_fullEvaluation_sub_base
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    taylorApply (laurentPlacementTaylorFamily C π₀) β =
      fullEvaluation C π₀ β hβ -
        PowerSeriesModule.single 0 (MiddleExactPerturbation.toLaurent (baseMCImage C π₀)) := by
  rw [fullEvaluation_eq_base_add_taylor]
  abel

end EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity
