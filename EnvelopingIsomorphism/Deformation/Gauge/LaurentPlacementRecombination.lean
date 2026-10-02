import EnvelopingIsomorphism.Deformation.Gauge.PlacementLaurentTruncation
import EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphEvaluation

/-! Coefficientwise recombination of the actual Laurent placement Taylor map. -/

noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentPlacementRecombination
open EnvelopingIsomorphism.FormalSeries
open LaurentTaylorArityBounds LaurentFullGraphEvaluation
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def laurentCoefficient (H : ℤ) : LaurentModule k W →ₗ[k] W where
  toFun F := LaurentModule.coeff F H
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_sum {ι : Type*} (s : Finset ι) (F : ι → LaurentModule k W) (H : ℤ) :
    LaurentModule.coeff (∑ i ∈ s, F i) H = ∑ i ∈ s, LaurentModule.coeff (F i) H :=
  map_sum (laurentCoefficient (k := k) (W := W) H) F s

/-- One actual placement component completed in t, before its h-base shift. -/
def componentTerm (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (r j : ℕ) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  PowerSeriesModule.applyMultilinear
    (LaurentModule.extendScalars (placementComponent C π₀ r (r + j))) (fun _ ↦ β)

def componentCoefficient (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H : ℤ) : W :=
  LaurentModule.coeff (PowerSeriesModule.coeffV D (componentTerm C π₀ β r j)) (H - j)

theorem componentTerm_bound
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β)) :
    LaurentModule.BoundedBelow ((r : ℤ) * L)
      (PowerSeriesModule.coeffV D (componentTerm C π₀ β r j)) := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  rw [componentTerm, PowerSeriesModule.coeffV_applyMultilinear]
  apply boundedBelow_sum
  intro a ha
  have hsum := (Finset.mem_piAntidiag.mp ha).1
  have hbound := LaurentModule.boundedBelow_applyMultilinear
    (placementComponent C π₀ r (r + j))
    (fun i ↦ PowerSeriesModule.coeffV (a i) β)
    (b := fun _ ↦ L) (fun i ↦ hβL (a i) (by
      calc
        a i ≤ ∑ v, a v := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        _ = D := hsum))
  simpa using hbound

theorem componentCoefficient_zero_of_large_shift
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D r j : ℕ) (H L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hj : (H - (r : ℤ) * L).toNat + 1 ≤ j) :
    componentCoefficient C π₀ β D r j H = 0 := by
  apply componentTerm_bound C π₀ β D r j L hβL
  omega

theorem componentCoefficient_zero_of_large_arity
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D r j : ℕ) (H : ℤ) (hr : D < r) :
    componentCoefficient C π₀ β D r j H = 0 := by
  cases r with
  | zero => omega
  | succ r =>
    unfold componentCoefficient componentTerm
    rw [multilinear_coeff_zero_of_lt r D _ β hβ hr, LaurentModule.coeff_zero]

/-- All nonzero placement terms fit inside the same total-arity cutoff as
the original full graph expansion. -/
theorem componentCoefficient_zero_of_total_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D r j : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β))
    (hm : arityCutoff D H L ≤ r + j) :
    componentCoefficient C π₀ β D r j H = 0 := by
  by_cases hr : D < r
  · exact componentCoefficient_zero_of_large_arity C π₀ β hβ D r j H hr
  · apply componentTerm_bound C π₀ β D r j L hβL
    have hrD : (r : ℤ) ≤ D := by exact_mod_cast Nat.le_of_not_gt hr
    have hmul := mul_le_mul_of_nonneg_right hrD (show 0 ≤ 1 - L by omega)
    unfold arityCutoff at hm
    have hcut : H - (D : ℤ) * (L - 1) < (r : ℤ) + j := by omega
    nlinarith

/-- Both completions are actual finite coefficient sums. The h cutoff uses
the true common lower bound of the finite t jet, not positivity in h of β. -/
theorem coeff_completed_placementTaylor_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D n : ℕ) (H L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (PowerSeriesModule.applyMultilinear (laurentPlacementTaylorFamily C π₀ n) (fun _ ↦ β))) H =
      ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
        componentCoefficient C π₀ β D (n + 1) j H := by
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  rw [PowerSeriesModule.coeffV_applyMultilinear, coeff_sum]
  have hx (a : Fin (n + 1) → ℕ) (ha : a ∈ Finset.piAntidiag Finset.univ D) :
      ∀ i, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV (a i) β) := by
    intro i
    apply hβL
    calc
      a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      _ = D := (Finset.mem_piAntidiag.mp ha).1
  calc
    _ = ∑ a ∈ Finset.piAntidiag Finset.univ D,
        ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
          LaurentModule.coeff (LaurentModule.applyMultilinear
            (placementComponent C π₀ (n + 1) (n + 1 + j))
            (fun i ↦ PowerSeriesModule.coeffV (a i) β)) (H - j) := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa using coeff_laurentPlacementTaylorFamily_finite C π₀ n
        (fun i ↦ PowerSeriesModule.coeffV (a i) β) (fun _ ↦ L) (hx a ha) H
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [componentCoefficient, componentTerm, PowerSeriesModule.coeffV_applyMultilinear, coeff_sum]
      rfl

/-- The finite positive-t Taylor arity sum, with its actual independent h cutoff. -/
theorem coeff_taylorApply_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (D : ℕ) (H L : ℤ)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (taylorApply (laurentPlacementTaylorFamily C π₀) β)) H =
      ∑ n ∈ Finset.range D, ∑ j ∈ Finset.range ((H - (n + 1 : ℕ) * L).toNat + 1),
        componentCoefficient C π₀ β D (n + 1) j H := by
  rw [coeffV_taylorApply, coeff_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact coeff_completed_placementTaylor_finite C π₀ β D n H L hβL

/-- The actual Taylor evaluation may use the very same finite total-arity
rectangle as the full graph expansion; both discarded tails are proved zero. -/
theorem coeff_taylorApply_common_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (H L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ a ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV a β)) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D
      (taylorApply (laurentPlacementTaylorFamily C π₀) β)) H =
      ∑ n ∈ Finset.range D, ∑ j ∈ Finset.range (arityCutoff D H L),
        componentCoefficient C π₀ β D (n + 1) j H := by
  rw [coeff_taylorApply_finite C π₀ β D H L hβL]
  apply Finset.sum_congr rfl
  intro n hn
  let J := (H - (n + 1 : ℕ) * L).toNat + 1
  by_cases hJM : J ≤ arityCutoff D H L
  · apply Finset.sum_subset (Finset.range_mono hJM)
    intro j hj hjJ
    exact componentCoefficient_zero_of_large_shift C π₀ β D (n + 1) j H L hβL
      (by simpa [J] using hjJ)
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt (Nat.lt_of_not_ge hJM)))
    intro j hj hjM
    apply componentCoefficient_zero_of_total_cutoff C π₀ β hβ D (n + 1) j H L hL hβL
    have hj' : arityCutoff D H L ≤ j := by simpa using hjM
    omega

end EnvelopingIsomorphism.Deformation.Gauge.LaurentPlacementRecombination
