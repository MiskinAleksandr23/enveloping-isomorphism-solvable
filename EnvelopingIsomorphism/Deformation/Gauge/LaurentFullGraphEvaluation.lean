import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorArityBounds

/-! The actual all-arity graph evaluation on hπ₀+β(t), with arbitrary
positive-t Laurent perturbations. Every joint coefficient is a proved finite
arity sum; no global h-bound on the perturbation family is required. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphEvaluation
open EnvelopingIsomorphism.FormalSeries
open LaurentTaylorArityBounds
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def coefficientSum (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D : ℕ) (H : ℤ) : W :=
  ∑ᶠ m : ℕ, LaurentModule.coeff (PowerSeriesModule.coeffV D (arityTerm C α m)) H

theorem coefficientSum_eq_sum
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D : ℕ) (H L : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV j α)) :
    coefficientSum C α D H = ∑ m ∈ Finset.range (arityCutoff D H L),
      LaurentModule.coeff (PowerSeriesModule.coeffV D (arityTerm C α m)) H := by
  apply finsum_eq_sum_of_support_subset
  intro m hm
  by_contra hn
  exact hm (arityTerm_coeff_zero_of_cutoff C α D m H L hα (by simpa using hn))

theorem coefficientSum_eq_zero_of_lt
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D : ℕ) (H L : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV j α)) (hH : H < (D : ℤ) * (L - 1)) :
    coefficientSum C α D H = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  apply arityTerm_bound C α D m L hα
  omega

/-- A genuine bounded Laurent coefficient at the chosen t degree. -/
def fullCoefficient (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) : LaurentModule k W :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (coefficientSum C (fullInput π₀ β) D) (by
    obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
    refine ⟨(D : ℤ) * (L - 1), ?_⟩
    intro H hH
    by_contra hn
    exact hH (coefficientSum_eq_zero_of_lt C _ D H L
      (fullInput_affine_bound π₀ β hβ D L hL hβL) (lt_of_not_ge hn))))

@[simp] theorem coeff_fullCoefficient
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (H : ℤ) :
    LaurentModule.coeff (fullCoefficient C π₀ β hβ D) H = coefficientSum C (fullInput π₀ β) D H := rfl

/-- All graph arities evaluated in the original outer-t / inner-Laurent model. -/
def fullEvaluation (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  PowerSeriesModule.mk (fullCoefficient C π₀ β hβ)

@[simp] theorem coeff_fullEvaluation
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (fullEvaluation C π₀ β hβ)) H =
      coefficientSum C (fullInput π₀ β) D H := rfl

theorem fullEvaluation_coeff_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ j ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV j β)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (fullEvaluation C π₀ β hβ)) H =
      ∑ m ∈ Finset.range (arityCutoff D H L),
        LaurentModule.coeff (PowerSeriesModule.coeffV D (arityTerm C (fullInput π₀ β) m)) H :=
  coefficientSum_eq_sum C _ D H L (fullInput_affine_bound π₀ β hβ D L hL hβL)

theorem arityTerm_constantCoeff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (m : ℕ) :
    PowerSeriesModule.coeffV 0 (arityTerm C (fullInput π₀ β) m) =
      LaurentModule.single (m : ℤ) (C m (fun _ ↦ π₀)) := by
  rw [arityTerm, multilinear_constant_coefficient]
  simp only [fullInput_coeff_zero π₀ β hβ, LaurentModule.extendScalars_apply]
  rw [LaurentModule.applyMultilinear_single]
  simp

/-- The nullary t coefficient is exactly the already used positive-h base image. -/
theorem fullEvaluation_constantCoeff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    PowerSeriesModule.coeffV 0 (fullEvaluation C π₀ β hβ) =
      MiddleExactPerturbation.toLaurent (baseMCImage C π₀) := by
  apply LaurentModule.ext
  intro H
  rw [coeff_fullEvaluation, coefficientSum]
  simp only [arityTerm_constantCoeff C π₀ β hβ, LaurentModule.coeff_single]
  by_cases hH : 0 ≤ H
  · lift H to ℕ using hH
    rw [MiddleExactPerturbation.coeff_toLaurent_nat]
    simp only [Int.natCast_inj]
    rw [finsum_eq_single _ H]
    · simp [baseMCImage]
    · intro m hm
      exact if_neg (Ne.symm hm)
  · rw [MiddleExactPerturbation.coeff_toLaurent_neg _ _ (lt_of_not_ge hH)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro m
    exact if_neg (by omega)

end EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphEvaluation
