import EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalPlacements

/-! Actual t/h truncation of the ordered placement directional derivative.
Only the finite jets of beta and delta are bounded; arbitrary negative h
orders remain allowed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalTruncation

open EnvelopingIsomorphism.FormalSeries LaurentDirectionalPlacements LaurentTaylorArityBounds
open LaurentPlacementRecombination
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem exists_common_jet_bound (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D : ℕ) :
    ∃ L : ℤ, L ≤ 1 ∧ (∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β)) ∧
      (∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ)) := by
  obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
  obtain ⟨M, hM, hδM⟩ := exists_jet_bound δ D
  exact ⟨min L M, (min_le_left _ _).trans hL,
    fun a ha => boundedBelow_mono (hβL a ha) (min_le_left _ _),
    fun a ha => boundedBelow_mono (hδM a ha) (min_le_right _ _)⟩

theorem updatedJet_bound (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D : ℕ) (L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ))
    {r : ℕ} (i : Fin r) : ∀ a ≤ D, ∀ l : Fin r,
      LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a ((Function.update (fun _ => β) i δ) l)) := by
  intro a ha l
  by_cases hl : l = i
  · subst l
    simpa using hδL a ha
  · simpa only [Function.update_of_ne hl] using hβL a ha

theorem applyMultilinear_jet_bound {r : ℕ} (F : MultilinearMap k (fun _ : Fin r => V) W)
    (z : Fin r → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D : ℕ) (L : ℤ)
    (hz : ∀ a ≤ D, ∀ i, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a (z i))) :
    LaurentModule.BoundedBelow ((r : ℤ) * L)
      (PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F) z)) := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  rw [PowerSeriesModule.coeffV_applyMultilinear]
  apply boundedBelow_sum
  intro a ha
  have hsum := (Finset.mem_piAntidiag.mp ha).1
  have hb := LaurentModule.boundedBelow_applyMultilinear F (fun i => PowerSeriesModule.coeffV (a i) (z i))
    (b := fun _ => L) (fun i => hz (a i) (by
      calc
        a i ≤ ∑ v, a v := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = D := hsum) i)
  simpa using hb

theorem coeff_multilinear_zero_of_positive_inputs {E A B : Type*} [CommRing E]
    [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B] {r : ℕ}
    (F : MultilinearMap E (fun _ : Fin r => A) B) (z : Fin r → PowerSeriesModule E A)
    (hz : ∀ i, PowerSeriesModule.coeffV 0 (z i) = 0) (D : ℕ) (hr : D < r) :
    PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear F z) = 0 := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  rw [PowerSeriesModule.coeffV_applyMultilinear]
  apply Finset.sum_eq_zero
  intro a ha
  have hsum := (Finset.mem_piAntidiag.mp ha).1
  by_cases hzero : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hzero
    exact F.map_coord_zero i (by simpa only [hi] using hz i)
  · exfalso
    have hmin : r ≤ ∑ i : Fin r, a i := by
      calc
        r = ∑ _i : Fin r, (1 : ℕ) := by simp
        _ ≤ ∑ i : Fin r, a i := Finset.sum_le_sum fun i _ => by
          have hi : a i ≠ 0 := fun h => hzero ⟨i, h⟩
          omega
    exact (Nat.not_le_of_lt hr) (hmin.trans_eq hsum)

def componentTerm (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (r j : ℕ) :=
  directionalTerm (LaurentModule.extendScalars (placementComponent C π₀ r (r + j))) β δ

def componentCoefficient (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H : ℤ) : W :=
  LaurentModule.coeff (PowerSeriesModule.coeffV D (componentTerm C π₀ β δ r j)) (H - j)

theorem componentTerm_bound (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ)) :
    LaurentModule.BoundedBelow ((r : ℤ) * L) (PowerSeriesModule.coeffV D (componentTerm C π₀ β δ r j)) := by
  rw [componentTerm, directionalTerm, PowerSeriesModule.coeffV_sum]
  apply boundedBelow_sum
  intro i hi
  exact applyMultilinear_jet_bound _ _ D L (updatedJet_bound β δ D L hβL hδL i)

theorem componentCoefficient_zero_of_large_shift
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ))
    (hj : (H - (r : ℤ) * L).toNat + 1 ≤ j) : componentCoefficient C π₀ β δ D r j H = 0 := by
  apply componentTerm_bound C π₀ β δ D r j L hβL hδL
  omega

theorem componentCoefficient_zero_of_large_arity
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0)
    (D r j : ℕ) (H : ℤ) (hr : D < r) : componentCoefficient C π₀ β δ D r j H = 0 := by
  unfold componentCoefficient componentTerm directionalTerm
  rw [PowerSeriesModule.coeffV_sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_multilinear_zero_of_positive_inputs _ _ (fun l => by
    by_cases hl : l = i
    · subst l; simpa using hδ
    · simpa only [Function.update_of_ne hl] using hβ) D hr, LaurentModule.coeff_zero]

theorem componentCoefficient_zero_of_total_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0)
    (D r j : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ))
    (hm : arityCutoff D H L ≤ r + j) : componentCoefficient C π₀ β δ D r j H = 0 := by
  by_cases hr : D < r
  · exact componentCoefficient_zero_of_large_arity C π₀ β δ hβ hδ D r j H hr
  · apply componentTerm_bound C π₀ β δ D r j L hβL hδL
    have hrD : (r : ℤ) ≤ D := by exact_mod_cast Nat.le_of_not_gt hr
    have hmul := mul_le_mul_of_nonneg_right hrD (show 0 ≤ 1 - L by omega)
    unfold arityCutoff at hm
    have hcut : H - (D : ℤ) * (L - 1) < (r : ℤ) + j := by omega
    nlinarith

theorem coeff_completed_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n D : ℕ)
    (z : Fin (n + 1) → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (H L : ℤ)
    (hz : ∀ a ≤ D, ∀ i, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a (z i))) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (PowerSeriesModule.applyMultilinear (laurentPlacementTaylorFamily C π₀ n) z)) H =
      ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
        LaurentModule.coeff (PowerSeriesModule.coeffV D (PowerSeriesModule.applyMultilinear
          (LaurentModule.extendScalars (placementComponent C π₀ (n + 1) (n + 1 + j))) z)) (H - j) := by
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  rw [PowerSeriesModule.coeffV_applyMultilinear, coeff_sum]
  calc
    _ = ∑ a ∈ Finset.piAntidiag Finset.univ D,
        ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
          LaurentModule.coeff (LaurentModule.applyMultilinear
            (placementComponent C π₀ (n + 1) (n + 1 + j))
            (fun i => PowerSeriesModule.coeffV (a i) (z i))) (H - j) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hb (i : Fin (n + 1)) := hz (a i) (by
        calc
          a i ≤ ∑ v, a v := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = D := (Finset.mem_piAntidiag.mp ha).1) i
      simpa using coeff_laurentPlacementTaylorFamily_finite C π₀ n _ (fun _ => L) hb H
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [PowerSeriesModule.coeffV_applyMultilinear, coeff_sum]
      rfl

theorem coeff_taylorDerivative_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D : ℕ) (H L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (taylorDerivativeApply (laurentPlacementTaylorFamily C π₀) β δ)) H =
      ∑ n ∈ Finset.range D, ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
        componentCoefficient C π₀ β δ D (n + 1) j H := by
  rw [coeff_taylorDerivativeApply, coeff_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coeff_sum]
  simp_rw [coeff_completed_finite C π₀ n D _ H L (updatedJet_bound β δ D L hβL hδL _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [componentCoefficient, componentTerm, directionalTerm, PowerSeriesModule.coeffV_sum, coeff_sum]

theorem coeff_taylorDerivative_common_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β δ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (hδ : PowerSeriesModule.coeffV 0 δ = 0)
    (D : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hδL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a δ)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (taylorDerivativeApply (laurentPlacementTaylorFamily C π₀) β δ)) H =
      ∑ n ∈ Finset.range D, ∑ j ∈ Finset.range (arityCutoff D H L),
        componentCoefficient C π₀ β δ D (n + 1) j H := by
  rw [coeff_taylorDerivative_finite C π₀ β δ D H L hβL hδL]
  apply Finset.sum_congr rfl
  intro n hn
  let J := (H - (n + 1 : ℕ) * L).toNat + 1
  by_cases hJM : J ≤ arityCutoff D H L
  · apply Finset.sum_subset (Finset.range_mono hJM)
    intro j hj hjJ
    exact componentCoefficient_zero_of_large_shift C π₀ β δ D (n + 1) j H L hβL hδL
      (by simpa [J] using hjJ)
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt (Nat.lt_of_not_ge hJM)))
    intro j hj hjM
    apply componentCoefficient_zero_of_total_cutoff C π₀ β δ hβ hδ D (n + 1) j H L hL hβL hδL
    have hj' : arityCutoff D H L ≤ j := by simpa using hjM
    omega

end EnvelopingIsomorphism.Deformation.Gauge.LaurentDirectionalTruncation
