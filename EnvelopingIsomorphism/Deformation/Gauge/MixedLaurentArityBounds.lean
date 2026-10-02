import EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphSummation

/-! Actual all-arity bounds for a curried graph family and an independent positive-t Laurent direction. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentArityBounds
open EnvelopingIsomorphism.FormalSeries LaurentTaylorArityBounds
open scoped BigOperators Classical
universe u v
variable {k : Type u} [Field k] {V Y W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]

abbrev CurriedFamily := GraphTaylorFamily (k := k) (V := V) (W := Y →ₗ[k] W)

/-- The genuine fixed-arity Laurent/t convolution with an independent direction. -/
def mixedTerm (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y)) (m : ℕ) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id) (arityTerm C α m) X

/-- A single nonpositive slope controls both inputs on the requested finite t jet. -/
theorem exists_common_jet_slope (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) :
    ∃ K : ℤ, K ≤ 0 ∧
      (∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * K)
        (PowerSeriesModule.coeffV j (fullInput π₀ β))) ∧
      (∀ j ≤ D, LaurentModule.BoundedBelow ((j : ℤ) * K) (PowerSeriesModule.coeffV j X)) := by
  obtain ⟨Lβ, _, hβL⟩ := exists_jet_bound β D
  obtain ⟨LX, _, hXL⟩ := exists_jet_bound X D
  let K := min (Lβ - 1) (min LX 0)
  have hK0 : K ≤ 0 := by dsimp [K]; omega
  have hKβ : K + 1 ≤ Lβ := by dsimp [K]; omega
  have hKX : K ≤ LX := by dsimp [K]; omega
  refine ⟨K, hK0, ?_, ?_⟩
  · have hb := fullInput_affine_bound π₀ β hβ D (K + 1) (by omega)
      (fun j hj ↦ boundedBelow_mono (hβL j hj) hKβ)
    simpa only [add_sub_cancel_right] using hb
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      rw [hX]
      intro H hH
      simp
    · have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      have hm := mul_le_mul_of_nonpos_right hj1 hK0
      apply boundedBelow_mono (hXL j hj)
      nlinarith

/-- The actual mixed coefficient starts at h degree m + D*K. -/
theorem mixedTerm_bound (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y)) (D m : ℕ) (K : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * K) (PowerSeriesModule.coeffV j α))
    (hX : ∀ j ≤ D, LaurentModule.BoundedBelow ((j : ℤ) * K) (PowerSeriesModule.coeffV j X)) :
    LaurentModule.BoundedBelow ((m : ℤ) + (D : ℤ) * K) (PowerSeriesModule.coeffV D (mixedTerm C α X m)) := by
  have h := LaurentAritySummation.bilinear_bound
    (LinearMap.id : (Y →ₗ[k] W) →ₗ[k] Y →ₗ[k] W) (arityTerm C α m) X D (m : ℤ) 0 K
    (fun j hj ↦ by
      simpa only [add_sub_cancel_right] using arityTerm_bound C α j m (K + 1)
        (fun e he ↦ by simpa only [add_sub_cancel_right] using hα e (he.trans hj)))
    (fun j hj ↦ by simpa only [zero_add] using hX j hj)
  simpa only [add_zero, mixedTerm, LaurentAritySummation.bilinear, PowerSeriesModule.extendBilinear_apply] using h

/-- A concrete finite arity cutoff for the chosen joint t/h coefficient. -/
def mixedCutoff (D : ℕ) (H K : ℤ) : ℕ := (H - (D : ℤ) * K).toNat + 1

/-- Every arity beyond the computed joint cutoff has zero coefficient. -/
theorem mixedTerm_coeff_zero_of_cutoff
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y)) (D m : ℕ) (H K : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * K) (PowerSeriesModule.coeffV j α))
    (hX : ∀ j ≤ D, LaurentModule.BoundedBelow ((j : ℤ) * K) (PowerSeriesModule.coeffV j X))
    (hm : mixedCutoff D H K ≤ m) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (mixedTerm C α X m)) H = 0 := by
  apply mixedTerm_bound C α X D m K hα hX
  unfold mixedCutoff at hm
  omega

/-- One finite-jet slope works for every arity and every split t degree. -/
theorem mixedTerm_local_bounds (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) :
    ∃ K : ℤ, K ≤ 0 ∧ ∀ e ≤ D, ∀ m : ℕ,
      LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
        (PowerSeriesModule.coeffV e (mixedTerm C (fullInput π₀ β) X m)) := by
  obtain ⟨K, hK, hα, hY⟩ := exists_common_jet_slope π₀ β hβ X hX D
  exact ⟨K, hK, fun e he m ↦ mixedTerm_bound C _ X e m K
    (fun j hj ↦ hα j (hj.trans he)) (fun j hj ↦ hY j (hj.trans he))⟩

/-- The real mixed arity family satisfies the established all-arity summation predicate. -/
theorem mixedTerm_summable (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) :
    LaurentAritySummation.Summable (mixedTerm C (fullInput π₀ β) X) := by
  intro D
  obtain ⟨K, _, hK⟩ := mixedTerm_local_bounds C π₀ β hβ X hX D
  exact ⟨(D : ℤ) * K, hK D le_rfl⟩

/-- Every fixed joint coefficient sees only finitely many actual mixed arities. -/
theorem mixedTerm_coeff_finite
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) (H : ℤ) :
    Function.HasFiniteSupport (fun m ↦ LaurentModule.coeff
      (PowerSeriesModule.coeffV D (mixedTerm C (fullInput π₀ β) X m)) H) := by
  obtain ⟨K, _, hα, hY⟩ := exists_common_jet_slope π₀ β hβ X hX D
  apply (Finset.finite_toSet (Finset.range (mixedCutoff D H K))).subset
  intro m hm
  by_contra hn
  exact hm (mixedTerm_coeff_zero_of_cutoff C _ X D m H K hα hY (by simpa using hn))

/-- The actual all-arity mixed sum in outer-t series with bounded Laurent coefficients. -/
def fullMixedEvaluation (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  LaurentAritySummation.sumSeries (mixedTerm C (fullInput π₀ β) X) (mixedTerm_summable C π₀ β hβ X hX)

@[simp] theorem coeff_fullMixedEvaluation
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) (H : ℤ) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (fullMixedEvaluation C π₀ β hβ X hX)) H =
      ∑ᶠ m : ℕ, LaurentModule.coeff (PowerSeriesModule.coeffV D (mixedTerm C (fullInput π₀ β) X m)) H := rfl

/-- The constructed joint coefficient is the literal finite arity sum below the cutoff. -/
theorem fullMixedEvaluation_coeff_cutoff
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) (H K : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * K)
      (PowerSeriesModule.coeffV j (fullInput π₀ β)))
    (hY : ∀ j ≤ D, LaurentModule.BoundedBelow ((j : ℤ) * K) (PowerSeriesModule.coeffV j X)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (fullMixedEvaluation C π₀ β hβ X hX)) H =
      ∑ m ∈ Finset.range (mixedCutoff D H K),
        LaurentModule.coeff (PowerSeriesModule.coeffV D (mixedTerm C (fullInput π₀ β) X m)) H := by
  apply LaurentAritySummation.jointSum_eq_truncate _ D ((D : ℤ) * K)
    (fun m ↦ mixedTerm_bound C _ X D m K hα hY)
  unfold mixedCutoff
  omega


theorem mixedTerm_constantCoeff
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (m : ℕ) :
    PowerSeriesModule.coeffV 0 (mixedTerm C α X m) = 0 := by
  simp [mixedTerm, PowerSeriesModule.coeffV_applyBilinear, hX]

theorem fullMixedEvaluation_constantCoeff
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) :
    PowerSeriesModule.coeffV 0 (fullMixedEvaluation C π₀ β hβ X hX) = 0 := by
  apply LaurentModule.ext
  intro H
  simp only [coeff_fullMixedEvaluation, mixedTerm_constantCoeff C _ X hX,
    LaurentModule.coeff_zero, finsum_zero]

/-- The all-arity sum retains the proved finite-jet Laurent lower bound. -/
theorem fullMixedEvaluation_bound
    (C : CurriedFamily (k := k) (V := V) (Y := Y) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y))
    (hX : PowerSeriesModule.coeffV 0 X = 0) (D : ℕ) (K : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * K)
      (PowerSeriesModule.coeffV j (fullInput π₀ β)))
    (hY : ∀ j ≤ D, LaurentModule.BoundedBelow ((j : ℤ) * K) (PowerSeriesModule.coeffV j X)) :
    LaurentModule.BoundedBelow ((D : ℤ) * K)
      (PowerSeriesModule.coeffV D (fullMixedEvaluation C π₀ β hβ X hX)) :=
  LaurentAritySummation.sumSeries_bound _ _ D _ (fun m ↦ mixedTerm_bound C _ X D m K hα hY)

end EnvelopingIsomorphism.Deformation.Gauge.MixedLaurentArityBounds
