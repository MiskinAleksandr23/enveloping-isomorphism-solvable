import EnvelopingIsomorphism.Deformation.Gauge.Taylor
import EnvelopingIsomorphism.Deformation.Gauge.TaylorIndexReindex
import EnvelopingIsomorphism.FormalSeries.MultilinearPartialEvaluation
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Positive-h Taylor evaluation at the original MC inputs h π₀ and h η(t).
Twisted coefficients are sums over all actual placements, without assuming
symmetry or replacing the placements by binomial factors. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open PowerSeriesModule
open scoped BigOperators Classical

variable {k V W : Type*} [CommRing k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Effective MC/Taylor coefficients C_m, including the nullary base operation.
For conventional raw Taylor maps U_m, these entries already contain 1/m!.
No additional factorial is inserted anywhere in this file. -/
abbrev GraphTaylorFamily := (m : ℕ) → MultilinearMap k (fun _ : Fin m ↦ V) W

/-- The positive-arity part has the established `TaylorFamily` interface. -/
def graphTaylorPositive (C : GraphTaylorFamily (k := k) (V := V) (W := W)) :
    TaylorFamily (k := k) (V := V) (W := W) := fun n ↦ C (n + 1)

/-- Multiplication of a vector-series input by the separate positive parameter h.
The result has outer t and inner h coefficients. -/
def hScaledInput (η : PowerSeriesModule k V) : PowerSeriesModule k (PowerSeriesModule k V) :=
  mk fun d ↦ single 1 (coeffV d η)

@[simp] theorem coeff_hScaledInput (η : PowerSeriesModule k V) (d m : ℕ) :
    coeffV m (coeffV d (hScaledInput η)) = if m = 1 then coeffV d η else 0 :=
  coeffV_single 1 m _

theorem hScaledInput_add (p q : PowerSeriesModule k V) :
    hScaledInput (p + q) = hScaledInput p + hScaledInput q := by
  apply PowerSeriesModule.ext
  intro d
  apply PowerSeriesModule.ext
  intro m
  simp only [coeff_hScaledInput, coeffV_add]
  split <;> simp

/-- Actual full Taylor evaluation on h ζ(t). At h-degree m the only operation
is C_m, applied by finite t-convolution to all m inputs. -/
def scaledMCEvaluation (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (ζ : PowerSeriesModule k V) : PowerSeriesModule k (PowerSeriesModule k W) :=
  mk fun d ↦ mk fun m ↦ coeffV d (applyMultilinear (C m) (fun _ ↦ ζ))

@[simp] theorem coeff_scaledMCEvaluation
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (ζ : PowerSeriesModule k V) (d m : ℕ) :
    coeffV m (coeffV d (scaledMCEvaluation C ζ)) =
      coeffV d (applyMultilinear (C m) (fun _ ↦ ζ)) := rfl

/-- The positions occupied by perturbations; the other positions contain the base point. -/
def nonemptyPlacements (m : ℕ) : Finset (Finset (Fin m)) := Finset.univ.erase ∅

/-- A placement records both the number of perturbation and base inputs. -/
def placementCounts {m : ℕ} (s : Finset (Fin m)) : ℕ × ℕ := (s.card, m - s.card)

theorem placementCounts_mem_antidiagonal {m : ℕ} (s : Finset (Fin m)) :
    placementCounts s ∈ Finset.HasAntidiagonal.antidiagonal m := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal]
  have hs : s.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ s)
  change s.card + (m - s.card) = m
  omega

/-- One actual ordered placement of η among the constant π₀ inputs. -/
def placementSeries (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (m : ℕ) (s : Finset (Fin m)) : PowerSeriesModule k W :=
  applyMultilinear (C m) (s.piecewise (fun _ ↦ η) (fun _ ↦ single 0 π₀))

/-- The twisted coefficient: a finite sum over n+j=m and every placement with
n perturbation slots and j base slots. The n=0 placement is excluded. -/
def twistedMCCoefficient (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (m d : ℕ) : W :=
  ∑ nj ∈ Finset.HasAntidiagonal.antidiagonal m,
    ∑ s ∈ (nonemptyPlacements m).filter (fun s ↦ placementCounts s = nj),
      coeffV d (placementSeries C π₀ η m s)

theorem twistedMCCoefficient_eq_sum_placements
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (m d : ℕ) :
    twistedMCCoefficient C π₀ η m d =
      ∑ s ∈ nonemptyPlacements m, coeffV d (placementSeries C π₀ η m s) := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun s _ ↦ placementCounts_mem_antidiagonal s) _

/-- Multilinearity expands a translation as a sum over all nonempty placements.
No permutation invariance or normalization identity is used. -/
theorem multilinear_translation_placements {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : MultilinearMap k (fun _ : ι ↦ V) W) (a b : V) :
    (∑ s ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
      F (s.piecewise (fun _ ↦ b) (fun _ ↦ a))) =
        F (fun _ ↦ a + b) - F (fun _ ↦ a) := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Finset ι))
    (fun s ↦ F (s.piecewise (fun _ ↦ b) (fun _ ↦ a))) (Finset.mem_univ ∅)
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = ∑ s : Finset ι, F (s.piecewise (fun _ ↦ b) (fun _ ↦ a)) := by
      simpa only [Finset.piecewise_empty] using hs
    _ = F ((fun _ ↦ b) + (fun _ ↦ a)) := (F.map_add_univ _ _).symm
    _ = F (fun _ ↦ a + b) := by congr 1; funext i; simp [add_comm]

theorem twistedMCCoefficient_translation
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (m d : ℕ) :
    twistedMCCoefficient C π₀ η m d =
      coeffV d (applyMultilinear (C m) (fun _ ↦ single 0 π₀ + η)) -
        coeffV d (applyMultilinear (C m) (fun _ ↦ single 0 π₀)) := by
  rw [twistedMCCoefficient_eq_sum_placements]
  have h := congrArg (coeffV d)
    (multilinear_translation_placements (extendMultilinear (C m)) (single 0 π₀) η)
  simpa only [coeffV_sum, coeffV_sub, extendMultilinear_apply,
    nonemptyPlacements, placementSeries] using h

/-- The complete positive-h twisted evaluation, with outer t and inner h. -/
def twistedMC (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) : PowerSeriesModule k (PowerSeriesModule k W) :=
  mk fun d ↦ mk fun m ↦ twistedMCCoefficient C π₀ η m d

@[simp] theorem coeff_twistedMC (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (d m : ℕ) :
    coeffV m (coeffV d (twistedMC C π₀ η)) = twistedMCCoefficient C π₀ η m d := rfl

/-- Exact full translation identity for the original MC input h(π₀+η(t)). -/
theorem twistedMC_eq_full_sub_base (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) :
    twistedMC C π₀ η = scaledMCEvaluation C (single 0 π₀ + η) -
      scaledMCEvaluation C (single 0 π₀) := by
  apply PowerSeriesModule.ext
  intro d
  apply PowerSeriesModule.ext
  intro m
  simp only [coeff_twistedMC, coeffV_sub, coeff_scaledMCEvaluation,
    twistedMCCoefficient_translation]

theorem twistedMC_h_zero (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (d : ℕ) : coeffV 0 (coeffV d (twistedMC C π₀ η)) = 0 := by
  rw [coeff_twistedMC, twistedMCCoefficient_eq_sum_placements]
  apply Finset.sum_eq_zero
  intro s hs
  exact False.elim ((Finset.mem_erase.mp hs).1 (Subsingleton.elim s ∅))

theorem multilinear_constant_coefficient {ι : Type*} [Fintype ι]
    (F : MultilinearMap k (fun _ : ι ↦ V) W) (p : ι → PowerSeriesModule k V) :
    coeffV 0 (applyMultilinear F p) = F (fun i ↦ coeffV 0 (p i)) := by
  simp only [coeffV_applyMultilinear, Finset.piAntidiag_zero, Finset.sum_singleton, Pi.zero_apply]

/-- Positivity in t of the perturbation gives positivity in t of the actual twisted image. -/
theorem twistedMC_t_zero (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (hη : coeffV 0 η = 0) :
    coeffV 0 (twistedMC C π₀ η) = 0 := by
  apply PowerSeriesModule.ext
  intro m
  simp only [coeff_twistedMC, coeffV_zero, twistedMCCoefficient_translation,
    multilinear_constant_coefficient, coeffV_add, coeffV_single, hη, add_zero, sub_self]

/-- An actual multilinear placement map: selected slots are variable, every
complementary slot is fixed at π₀. Native finite-set currying fixes the ordering. -/
def placementMap (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    {m n : ℕ} (s : Finset (Fin m)) (hs : s.card = n) :
    MultilinearMap k (fun _ : Fin n ↦ V) W :=
  partialFinset hs (by simp [Finset.card_compl, hs] : sᶜ.card = m - n) (C m)
    (fun _ ↦ π₀)

@[simp] theorem placementMap_diagonal (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ x : V) {m n : ℕ} (s : Finset (Fin m)) (hs : s.card = n) :
    placementMap C π₀ s hs (fun _ ↦ x) = C m (s.piecewise (fun _ ↦ x) (fun _ ↦ π₀)) := by
  exact MultilinearMap.curryFinFinset_apply_const hs _ (C m) x π₀

/-- The sum of all genuinely n-linear placements inside the operation C_m. -/
def placementComponent (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (n m : ℕ) : MultilinearMap k (fun _ : Fin n ↦ V) W :=
  ∑ s : {s : Finset (Fin m) // s.card = n}, placementMap C π₀ s.val s.property

theorem placementComponent_diagonal (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ x : V) (n m : ℕ) :
    placementComponent C π₀ n m (fun _ ↦ x) =
      ∑ s : {s : Finset (Fin m) // s.card = n}, C m (s.val.piecewise (fun _ ↦ x) (fun _ ↦ π₀)) := by
  simp only [placementComponent, sum_apply, placementMap_diagonal]

theorem placementComponent_eq_zero_of_lt
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) {n m : ℕ} (h : m < n) :
    placementComponent C π₀ n m = 0 := by
  haveI : IsEmpty {s : Finset (Fin m) // s.card = n} := ⟨fun s ↦ by
    have hs : s.val.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ s.val)
    have hn := s.property
    omega⟩
  simp [placementComponent]

private def seriesOfMultilinearCoefficients {A : Type*} [AddCommGroup A] [Module k A] {r : ℕ}
    (F : ℕ → MultilinearMap k (fun _ : Fin r ↦ A) W) :
    MultilinearMap k (fun _ : Fin r ↦ A) (PowerSeriesModule k W) where
  toFun v := mk fun m ↦ F m v
  map_update_add' v i a b := by apply PowerSeriesModule.ext; intro m; exact (F m).map_update_add v i a b
  map_update_smul' v i a b := by apply PowerSeriesModule.ext; intro m; exact (F m).map_update_smul v i a b

/-- The actual positive-h twisted family of effective MC coefficients. A coefficient h^m
contains only j≤m base insertions, multiplied by h^j via the coefficient shift.
Every ordered placement is retained; symmetry and binomial normalization are not assumed. -/
def placementTaylorFamily (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) :
    TaylorFamily (k := k) (V := PowerSeriesModule k V) (W := PowerSeriesModule k W) :=
  fun n ↦ seriesOfMultilinearCoefficients fun m ↦
    ∑ j ∈ Finset.range (m + 1),
      (coefficient (m - j)).compMultilinearMap
        ((extendMultilinear (placementComponent C π₀ (n + 1) (n + 1 + j))).restrictScalars k)

theorem coeff_placementTaylorFamily
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n m : ℕ)
    (v : Fin (n + 1) → PowerSeriesModule k V) :
    coeffV m (placementTaylorFamily C π₀ n v) =
      ∑ j ∈ Finset.range (m + 1),
        coeffV (m - j) (applyMultilinear (placementComponent C π₀ (n + 1) (n + 1 + j)) v) := by
  change (∑ j ∈ Finset.range (m + 1),
    (coefficient (m - j)).compMultilinearMap
      ((extendMultilinear (placementComponent C π₀ (n + 1) (n + 1 + j))).restrictScalars k)) v = _
  simp only [sum_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.coe_restrictScalars, extendMultilinear_apply]
  rfl

/-- Insert exactly one factor h as an actual linear map on coefficient vectors. -/
def hSingle : V →ₗ[k] PowerSeriesModule k V where
  toFun v := single 1 v
  map_add' x y := by ext m; simp only [coeffV_single, coeffV_add]; split <;> simp
  map_smul' a x := by ext m; simp only [coeffV_single, coeffV_smul]; split <;> simp

@[simp] theorem hSingle_apply (v : V) : hSingle (k := k) v = single 1 v := rfl

theorem hScaledInput_eq_map (η : PowerSeriesModule k V) : hScaledInput η = PowerSeriesModule.map hSingle η := rfl

theorem hScaledInput_positive (η : PowerSeriesModule k V) (hη : coeffV 0 η = 0) :
    coeffV 0 (hScaledInput η) = 0 := by
  apply PowerSeriesModule.ext
  intro m
  simp only [coeff_hScaledInput, hη, ite_self, coeffV_zero]

theorem coeff_applyMultilinear_hSingle {r : ℕ}
    (F : MultilinearMap k (fun _ : Fin r ↦ V) W) (v : Fin r → V) (m : ℕ) :
    coeffV m (applyMultilinear F (fun i ↦ single 1 (v i))) = if m = r then F v else 0 := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  rw [coeffV_applyMultilinear]
  by_cases hm : m = r
  · subst m
    rw [if_pos rfl]
    rw [Finset.sum_eq_single_of_mem (fun _ : Fin r ↦ 1) (by simp)]
    · simp
    · intro a _ hne
      obtain ⟨i, hi⟩ := not_forall.mp (fun h ↦ hne (funext h))
      exact F.map_coord_zero i (by simp only [coeffV_single, if_neg hi])
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : a ≠ (fun _ : Fin r ↦ 1) := by
      intro h
      have hs := (Finset.mem_piAntidiag.mp ha).1
      have haone : (∑ i, a i) = r := by rw [h]; simp
      exact hm (hs.symm.trans haone)
    obtain ⟨i, hi⟩ := not_forall.mp (fun h ↦ hne (funext h))
    exact F.map_coord_zero i (by simp only [coeffV_single, if_neg hi])

theorem coeff_placementTaylorFamily_hSingle
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n m : ℕ)
    (v : Fin (n + 1) → V) :
    coeffV m (placementTaylorFamily C π₀ n (fun i ↦ hSingle (v i))) =
      ∑ j ∈ Finset.range (m + 1),
        if n + 1 + j = m then placementComponent C π₀ (n + 1) (n + 1 + j) v else 0 := by
  rw [coeff_placementTaylorFamily]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (fun i ↦ hSingle (v i)) = (fun i ↦ single 1 (v i)) from rfl,
    coeff_applyMultilinear_hSingle]
  have hj' := Finset.mem_range.mp hj
  by_cases h : n + 1 + j = m
  · have hmj : m - j = n + 1 := by omega
    rw [if_pos h, if_pos hmj]
  · have hmj : m - j ≠ n + 1 := by omega
    rw [if_neg h, if_neg hmj]

private def evaluateCompletedMultilinear {r : ℕ} (v : Fin r → PowerSeriesModule k V) :
    MultilinearMap k (fun _ : Fin r ↦ V) W →ₗ[k] PowerSeriesModule k W where
  toFun F := applyMultilinear F v
  map_add' F G := by
    apply PowerSeriesModule.ext
    intro d
    simp [coeffV_applyMultilinear, Finset.sum_add_distrib]
  map_smul' a F := by
    apply PowerSeriesModule.ext
    intro d
    simp [coeffV_applyMultilinear, Finset.smul_sum]

theorem placementMap_completed_diagonal
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    {m n : ℕ} (s : Finset (Fin m)) (hs : s.card = n) :
    applyMultilinear (placementMap C π₀ s hs) (fun _ ↦ η) = placementSeries C π₀ η m s :=
  applyMultilinear_partialFinset_diagonal hs _ (C m) π₀ η

theorem coeff_placementComponent (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (η : PowerSeriesModule k V) (n m d : ℕ) :
    coeffV d (applyMultilinear (placementComponent C π₀ n m) (fun _ ↦ η)) =
      ∑ s : {s : Finset (Fin m) // s.card = n}, coeffV d (placementSeries C π₀ η m s.val) := by
  change coeffV d (evaluateCompletedMultilinear (fun _ : Fin n ↦ η)
    (∑ s : {s : Finset (Fin m) // s.card = n}, placementMap C π₀ s.val s.property)) = _
  rw [map_sum, coeffV_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (coeffV d) (placementMap_completed_diagonal C π₀ η s.val s.property)

private theorem mem_placement_filter_iff {n j : ℕ} (hn : n ≠ 0) (s : Finset (Fin (n + j))) :
    s ∈ (nonemptyPlacements (n + j)).filter (fun s ↦ placementCounts s = (n, j)) ↔ s.card = n := by
  constructor
  · intro hs
    exact congrArg Prod.fst (Finset.mem_filter.mp hs).2
  · intro hs
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_erase.mpr
      exact ⟨fun hz ↦ hn (by simpa only [hz, Finset.card_empty] using hs.symm), Finset.mem_univ _⟩
    · apply Prod.ext <;> simp [placementCounts, hs]

theorem twistedMCCoefficient_eq_components
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (m d : ℕ) :
    twistedMCCoefficient C π₀ η m d =
      ∑ nj ∈ Finset.HasAntidiagonal.antidiagonal m,
        if nj.1 = 0 then 0 else
          coeffV d (applyMultilinear (placementComponent C π₀ nj.1 (nj.1 + nj.2)) (fun _ ↦ η)) := by
  apply Finset.sum_congr rfl
  rintro ⟨n, j⟩ hnj
  have hm := Finset.HasAntidiagonal.mem_antidiagonal.mp hnj
  change n + j = m at hm
  subst m
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro s hs
    have hc : s.card = 0 := congrArg Prod.fst (Finset.mem_filter.mp hs).2
    have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hs).1).1
    exact False.elim (hne (Finset.card_eq_zero.mp hc))
  · rw [if_neg hn, coeff_placementComponent]
    exact Finset.sum_subtype _ (mem_placement_filter_iff hn) _

private theorem placementTaylor_coefficient_map
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n m : ℕ) :
    ((coefficient m).compMultilinearMap (placementTaylorFamily C π₀ n)).compLinearMap
      (fun _ : Fin (n + 1) ↦ hSingle) =
      ∑ j ∈ Finset.range (m + 1),
        if n + 1 + j = m then placementComponent C π₀ (n + 1) (n + 1 + j) else 0 := by
  apply MultilinearMap.ext
  intro v
  change coeffV m (placementTaylorFamily C π₀ n (fun i ↦ hSingle (v i))) = _
  rw [coeff_placementTaylorFamily_hSingle, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem coeff_completed_placementTaylor
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (n m d : ℕ) :
    coeffV m (coeffV d (applyMultilinear (placementTaylorFamily C π₀ n) (fun _ ↦ hScaledInput η))) =
      ∑ j ∈ Finset.range (m + 1), if n + 1 + j = m then
        coeffV d (applyMultilinear (placementComponent C π₀ (n + 1) (n + 1 + j)) (fun _ ↦ η)) else 0 := by
  have hp := congrArg (coeffV d) (applyMultilinear_postcomp
    (placementTaylorFamily C π₀ n) (coefficient m) (fun _ ↦ hScaledInput η))
  change coeffV m (coeffV d (applyMultilinear (placementTaylorFamily C π₀ n)
    (fun _ ↦ hScaledInput η))) =
      coeffV d (applyMultilinear ((coefficient m).compMultilinearMap
        (placementTaylorFamily C π₀ n)) (fun _ ↦ hScaledInput η)) at hp
  rw [hp]
  have hpre := applyMultilinear_precomp
    ((coefficient m).compMultilinearMap (placementTaylorFamily C π₀ n))
    (fun _ : Fin (n + 1) ↦ hSingle) (fun _ ↦ η)
  rw [hScaledInput_eq_map, hpre, placementTaylor_coefficient_map]
  change coeffV d (evaluateCompletedMultilinear (fun _ : Fin (n + 1) ↦ η)
    (∑ j ∈ Finset.range (m + 1), if n + 1 + j = m then
      placementComponent C π₀ (n + 1) (n + 1 + j) else 0)) = _
  rw [map_sum, coeffV_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rfl
  · simp

/-- The actual bundled twisted Taylor family evaluates to the placement sum
on β=h η(t). Positivity of η supplies the outer t-arity cutoff. -/
theorem taylorApply_placement_eq_twistedMC
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    taylorApply (placementTaylorFamily C π₀) (hScaledInput η) = twistedMC C π₀ η := by
  apply PowerSeriesModule.ext
  intro d
  apply PowerSeriesModule.ext
  intro m
  rw [coeffV_taylorApply, coeffV_sum, coeff_twistedMC, twistedMCCoefficient_eq_components]
  simp_rw [coeff_completed_placementTaylor]
  refine taylor_range_antidiagonal_reindex
    (fun n j ↦ coeffV d (applyMultilinear (placementComponent C π₀ n (n + j)) (fun _ ↦ η))) d m ?_
  intro n j hn
  cases n with
  | zero => omega
  | succ n =>
    exact multilinear_coeff_zero_of_lt n d
      (placementComponent C π₀ (n + 1) (n + 1 + j)) η hη hn

/-- The complete MC-image translation identity for the genuine twisted Taylor map. -/
theorem taylorApply_placement_eq_full_sub_base
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    taylorApply (placementTaylorFamily C π₀) (hScaledInput η) =
      scaledMCEvaluation C (single 0 π₀ + η) - scaledMCEvaluation C (single 0 π₀) := by
  rw [taylorApply_placement_eq_twistedMC C π₀ η hη, twistedMC_eq_full_sub_base]

/-- The full MC image is the base image plus the actual twisted Taylor evaluation. -/
theorem fullMC_eq_base_add_twistedTaylor
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    scaledMCEvaluation C (single 0 π₀ + η) = scaledMCEvaluation C (single 0 π₀) +
      taylorApply (placementTaylorFamily C π₀) (hScaledInput η) := by
  rw [taylorApply_placement_eq_full_sub_base C π₀ η hη]
  abel

theorem taylorApply_placement_h_zero
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) (d : ℕ) :
    coeffV 0 (coeffV d (taylorApply (placementTaylorFamily C π₀) (hScaledInput η))) = 0 := by
  rw [taylorApply_placement_eq_twistedMC C π₀ η hη, twistedMC_h_zero]

private theorem multilinear_constant_input_coeff {r : ℕ}
    (F : MultilinearMap k (fun _ : Fin r ↦ V) W) (π₀ : V) (d : ℕ) :
    coeffV d (applyMultilinear F (fun _ ↦ single 0 π₀)) =
      if d = 0 then F (fun _ ↦ π₀) else 0 := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  by_cases hd : d = 0
  · subst d
    simp only [multilinear_constant_coefficient, coeffV_single, ite_true]
  · rw [if_neg hd, coeffV_applyMultilinear]
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : ¬ ∀ i, a i = 0 := by
      intro hz
      have hs := (Finset.mem_piAntidiag.mp ha).1
      exact hd (by simpa [hz] using hs.symm)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact F.map_coord_zero i (by simp only [coeffV_single, if_neg hi])

/-- The complete positive-h base MC image, including its nullary coefficient. -/
def baseMCImage (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) :
    PowerSeriesModule k W := mk fun m ↦ C m (fun _ ↦ π₀)

theorem scaledMCEvaluation_base (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) :
    scaledMCEvaluation C (single 0 π₀) = single 0 (baseMCImage C π₀) := by
  apply PowerSeriesModule.ext
  intro d
  apply PowerSeriesModule.ext
  intro m
  rw [coeff_scaledMCEvaluation, multilinear_constant_input_coeff, coeffV_single]
  by_cases hd : d = 0 <;> simp [hd, baseMCImage]

theorem scaledMCEvaluation_constantCoeff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    coeffV 0 (scaledMCEvaluation C (single 0 π₀ + η)) = baseMCImage C π₀ := by
  apply PowerSeriesModule.ext
  intro m
  simp only [coeff_scaledMCEvaluation, multilinear_constant_coefficient,
    coeffV_add, coeffV_single, hη, ite_true, add_zero, baseMCImage, coeffV_mk]

/-- Direct interface for the deformation image B(t)-B(0) used by gauge comparison. -/
theorem taylorApply_placement_eq_full_sub_constant
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    taylorApply (placementTaylorFamily C π₀) (hScaledInput η) =
      scaledMCEvaluation C (single 0 π₀ + η) -
        single 0 (coeffV 0 (scaledMCEvaluation C (single 0 π₀ + η))) := by
  rw [taylorApply_placement_eq_full_sub_base C π₀ η hη, scaledMCEvaluation_base,
    scaledMCEvaluation_constantCoeff C π₀ η hη]

end EnvelopingIsomorphism.Deformation.Gauge
