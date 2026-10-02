import EnvelopingIsomorphism.Deformation.Gauge.TaylorTwistEvaluation
import EnvelopingIsomorphism.FormalSeries.PositiveLaurentMultilinear

/-! Actual transfer of the effective placement Taylor family from positive h
series to the genuine Laurent cochain modules, retaining outer t completion.

`C m` is the effective MC coefficient (conventionally raw `U m / m!`),
so neither the placement construction nor `taylorApply` inserts another factorial.
No symmetry of the input slots is assumed. Identifying a concrete geometric
family with these effective coefficients is a separate obligation.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open EnvelopingIsomorphism.FormalSeries.PositiveLaurent
open EnvelopingIsomorphism.Deformation.MiddleExactPerturbation
open PowerSeriesModule
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k]
variable {V W : Type v} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem sum_piAntidiag_head {A : Type*} [AddCommMonoid A]
    (r d : ℕ) [DecidableEq (Fin (r + 1))] [DecidableEq (Fin r)]
    (g : ℕ → (Fin r → ℕ) → A) :
    (∑ a ∈ Finset.piAntidiag Finset.univ d, g (a 0) (Fin.tail a)) =
      ∑ j ∈ Finset.range (d + 1), ∑ b ∈ Finset.piAntidiag Finset.univ (d - j), g j b := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun a : Fin (r + 1) → ℕ ↦ ⟨a 0, Fin.tail a⟩)
    (fun ⟨j, b⟩ ↦ Fin.cons j b)
  · intro a ha
    have hs := (Finset.mem_piAntidiag.mp ha).1
    simp only [Fin.sum_univ_succ] at hs
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true]
    constructor
    · omega
    · exact Nat.eq_sub_of_add_eq (by simpa [Fin.tail, add_comm] using hs)
  · rintro ⟨j, b⟩ hb
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true] at hb ⊢
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hsum := hb.2
    change ∑ i, b i = d - j at hsum
    rw [hsum]
    omega
  · intro a _
    exact Fin.cons_self_tail a
  · rintro ⟨j, b⟩ _
    simp
  · intro a _
    rfl

/-- Cochain-valued positive series evaluate by the actual finite head/tail convolution. -/
theorem positive_cochainEvaluation_coeff (r : ℕ)
    (F : PowerSeriesModule k (LaurentModule.Cochain k V W r))
    (x : Fin r → PowerSeriesModule k V) (d : ℕ) :
    coeffV d (applyMultilinear (LaurentModule.cochainEvaluation (k := k) (X := V) (Y := W) r)
      (Fin.cons F x)) =
      ∑ j ∈ Finset.range (d + 1), coeffV (d - j) (applyMultilinear (coeffV j F) x) := by
  letI : DecidableEq (Fin (r + 1)) := Classical.decEq _
  letI : DecidableEq (Fin r) := Classical.decEq _
  simp only [coeffV_applyMultilinear]
  change (∑ a ∈ Finset.piAntidiag Finset.univ d,
    (coeffV (a 0) F) (fun i ↦ coeffV (a i.succ) (x i))) = _
  exact sum_piAntidiag_head r d (fun j b ↦ (coeffV j F) (fun i ↦ coeffV (b i) (x i)))

/-- The h-series of actual effective placement coefficients, before F4 extension. -/
def placementOperatorCoefficients
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n : ℕ) :
    PowerSeriesModule k (LaurentModule.Cochain k V W (n + 1)) :=
  mk fun j ↦ placementComponent C π₀ (n + 1) (n + 1 + j)

/-- The genuine Laurent-linear placement Taylor family, defined using F4 extendCochain. -/
def laurentPlacementTaylorFamily
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) :
    TaylorFamily (k := LaurentSeries k) (V := LaurentModule k V) (W := LaurentModule k W) :=
  fun n ↦ LaurentModule.extendCochain (n + 1) (toLaurent (placementOperatorCoefficients C π₀ n))

theorem positive_placement_cochain_evaluation
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n : ℕ)
    (x : Fin (n + 1) → PowerSeriesModule k V) :
    applyMultilinear (LaurentModule.cochainEvaluation (k := k) (X := V) (Y := W) (n + 1))
      (Fin.cons (placementOperatorCoefficients C π₀ n) x :
        ∀ i, PowerSeriesModule k (LaurentModule.CochainInput (k := k) (X := V) (Y := W) (n + 1) i)) = placementTaylorFamily C π₀ n x := by
  apply PowerSeriesModule.ext
  intro m
  rw [positive_cochainEvaluation_coeff, coeff_placementTaylorFamily]
  rfl

/-- Equality of the actual positive placement map and the actual Laurent map on positive inputs. -/
theorem toLaurent_placementTaylorFamily
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n : ℕ)
    (x : Fin (n + 1) → PowerSeriesModule k V) :
    toLaurent (placementTaylorFamily C π₀ n x) =
      laurentPlacementTaylorFamily C π₀ n (fun i ↦ toLaurent (x i)) := by
  rw [← positive_placement_cochain_evaluation, toLaurent_applyMultilinear]
  change LaurentModule.applyMultilinear
    (LaurentModule.cochainEvaluation (k := k) (X := V) (Y := W) (n + 1))
      (fun i ↦ toLaurent ((Fin.cons (placementOperatorCoefficients C π₀ n) x :
        ∀ i, PowerSeriesModule k (LaurentModule.CochainInput (k := k) (X := V) (Y := W) (n + 1) i)) i)) =
    LaurentModule.applyMultilinear
      (LaurentModule.cochainEvaluation (k := k) (X := V) (Y := W) (n + 1))
        (Fin.cons (toLaurent (placementOperatorCoefficients C π₀ n)) (fun i ↦ toLaurent (x i)) :
          ∀ i, LaurentModule k (LaurentModule.CochainInput (k := k) (X := V) (Y := W) (n + 1) i))
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

/-- Inject each positive inner h-series into its true Laurent module, coefficientwise in t.
This is only claimed additive; the positive domain is not an E-module. -/
def positiveOuterEmbedding : PowerSeriesModule k (PowerSeriesModule k V) →+
    PowerSeriesModule (LaurentSeries k) (LaurentModule k V) where
  toFun p := mk fun d ↦ toLaurent (coeffV d p)
  map_zero' := by apply PowerSeriesModule.ext; intro d; exact toLaurent_zero
  map_add' p q := by
    apply PowerSeriesModule.ext
    intro d
    exact (toLaurentLinear (k := k)).map_add (coeffV d p) (coeffV d q)

@[simp] theorem coeff_positiveOuterEmbedding (p : PowerSeriesModule k (PowerSeriesModule k V)) (d : ℕ) :
    coeffV d (positiveOuterEmbedding p) = toLaurent (coeffV d p) := rfl

theorem positiveOuterEmbedding_injective : Function.Injective (positiveOuterEmbedding (k := k) (V := V)) := by
  intro p q h
  apply PowerSeriesModule.ext
  intro d
  exact toLaurent_injective (congrArg (coeffV d) h)

theorem positiveOuterEmbedding_single (d : ℕ) (p : PowerSeriesModule k V) :
    positiveOuterEmbedding (single d p) = single d (toLaurent p) := by
  apply PowerSeriesModule.ext
  intro e
  simp only [coeff_positiveOuterEmbedding, coeffV_single]
  split <;> simp_all

theorem positiveOuterEmbedding_applyMultilinear {r : ℕ}
    (f : MultilinearMap k (fun _ : Fin r ↦ PowerSeriesModule k V) (PowerSeriesModule k W))
    (g : MultilinearMap (LaurentSeries k) (fun _ : Fin r ↦ LaurentModule k V) (LaurentModule k W))
    (hfg : ∀ x, toLaurent (f x) = g (fun i ↦ toLaurent (x i)))
    (x : Fin r → PowerSeriesModule k (PowerSeriesModule k V)) :
    positiveOuterEmbedding (applyMultilinear f x) =
      applyMultilinear g (fun i ↦ positiveOuterEmbedding (x i)) := by
  apply PowerSeriesModule.ext
  intro d
  rw [coeff_positiveOuterEmbedding, coeffV_applyMultilinear, coeffV_applyMultilinear]
  letI : DecidableEq (Fin r) := Classical.decEq _
  change toLaurentLinear (k := k) (∑ a ∈ Finset.piAntidiag Finset.univ d, f (fun i ↦ coeffV (a i) (x i))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact hfg (fun i ↦ coeffV (a i) (x i))

theorem positiveOuterEmbedding_taylorApply
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule k (PowerSeriesModule k V)) :
    positiveOuterEmbedding (taylorApply (placementTaylorFamily C π₀) β) =
      taylorApply (laurentPlacementTaylorFamily C π₀) (positiveOuterEmbedding β) := by
  apply PowerSeriesModule.ext
  intro d
  rw [coeff_positiveOuterEmbedding, coeffV_taylorApply, coeffV_taylorApply]
  change toLaurentLinear (∑ n ∈ Finset.range d,
    coeffV d (applyMultilinear (placementTaylorFamily C π₀ n) (fun _ ↦ β))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (coeffV d) (positiveOuterEmbedding_applyMultilinear
    (placementTaylorFamily C π₀ n) (laurentPlacementTaylorFamily C π₀ n)
    (toLaurent_placementTaylorFamily C π₀ n) (fun _ ↦ β))

/-- The actual original β=hη(t) in the true outer-t / inner-Laurent model. -/
def laurentScaledInput (η : PowerSeriesModule k V) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k V) := positiveOuterEmbedding (hScaledInput η)

@[simp] theorem coeff_laurentScaledInput (η : PowerSeriesModule k V) (d : ℕ) :
    coeffV d (laurentScaledInput η) = LaurentModule.single (k := k) 1 (coeffV d η) :=
  toLaurent_single 1 _

def laurentScaledMCEvaluation (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (ζ : PowerSeriesModule k V) : PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  positiveOuterEmbedding (scaledMCEvaluation C ζ)

@[simp] theorem coeff_laurentScaledMCEvaluation_nat
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (ζ : PowerSeriesModule k V) (d m : ℕ) :
    LaurentModule.coeff (coeffV d (laurentScaledMCEvaluation C ζ)) (m : ℤ) =
      coeffV d (applyMultilinear (C m) (fun _ ↦ ζ)) := coeff_toLaurent_nat _ m

theorem coeff_laurentScaledMCEvaluation_neg
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (ζ : PowerSeriesModule k V)
    (d : ℕ) (m : ℤ) (hm : m < 0) :
    LaurentModule.coeff (coeffV d (laurentScaledMCEvaluation C ζ)) m = 0 := coeff_toLaurent_neg _ m hm

/-- The full MC-image identity in the actual Laurent cochain modules, with no assumed
agreement between positive and Laurent Taylor maps. -/
theorem laurent_taylorApply_eq_full_sub_constant
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (η : PowerSeriesModule k V)
    (hη : coeffV 0 η = 0) :
    taylorApply (laurentPlacementTaylorFamily C π₀) (laurentScaledInput η) =
      laurentScaledMCEvaluation C (single 0 π₀ + η) -
        single 0 (coeffV 0 (laurentScaledMCEvaluation C (single 0 π₀ + η))) := by
  change taylorApply (laurentPlacementTaylorFamily C π₀) (positiveOuterEmbedding (hScaledInput η)) = _
  rw [← positiveOuterEmbedding_taylorApply, taylorApply_placement_eq_full_sub_constant C π₀ η hη,
    map_sub, positiveOuterEmbedding_single]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge
