import EnvelopingIsomorphism.Deformation.Gauge.TaylorLaurentEvaluation

/-! Actual joint t/h bounds for all-arity graph evaluation at hπ₀+β(t).
The perturbation coefficients are arbitrary bounded Laurent vectors. A finite
t cutoff supplies a common lower bound; positive h order at the base then
makes each fixed joint coefficient see only finitely many graph arities. -/

noncomputable section
set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorArityBounds
open EnvelopingIsomorphism.FormalSeries
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem boundedBelow_mono {L M : ℤ} {x : LaurentModule k V}
    (hx : LaurentModule.BoundedBelow L x) (h : M ≤ L) :
    LaurentModule.BoundedBelow M x := fun j hj ↦ hx j (lt_of_lt_of_le hj h)

theorem boundedBelow_sum {ι : Type*} (s : Finset ι) (x : ι → LaurentModule k V) (L : ℤ)
    (hx : ∀ i ∈ s, LaurentModule.BoundedBelow L (x i)) :
    LaurentModule.BoundedBelow L (∑ i ∈ s, x i) := by
  induction s using Finset.induction with
  | empty => simp [LaurentModule.BoundedBelow]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact LaurentModule.boundedBelow_add (hx i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)))

/-- Only a finite t-jet is bounded uniformly; no global bound on β is assumed. -/
theorem exists_jet_bound (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D : ℕ) : ∃ L : ℤ, L ≤ 1 ∧
      ∀ j ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV j β) := by
  induction D with
  | zero =>
    obtain ⟨L, hL⟩ := LaurentModule.exists_bound (PowerSeriesModule.coeffV 0 β)
    refine ⟨min L 1, min_le_right _ _, ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact boundedBelow_mono hL (min_le_left _ _)
  | succ D ih =>
    obtain ⟨L, hL1, hL⟩ := ih
    obtain ⟨M, hM⟩ := LaurentModule.exists_bound (PowerSeriesModule.coeffV (D + 1) β)
    refine ⟨min L M, (min_le_left _ _).trans hL1, ?_⟩
    intro j hj
    by_cases hjD : j ≤ D
    · exact boundedBelow_mono (hL j hjD) (min_le_left _ _)
    · have hjs : j = D + 1 := by omega
      subst j
      exact boundedBelow_mono hM (min_le_right _ _)

/-- The honest translated source, with the original hπ₀ coefficient. -/
def fullInput (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :=
  PowerSeriesModule.single 0 (LaurentModule.single (k := k) 1 π₀) + β

theorem fullInput_coeff_zero (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    PowerSeriesModule.coeffV 0 (fullInput π₀ β) = LaurentModule.single 1 π₀ := by
  simp [fullInput, hβ]

theorem fullInput_coeff_positive (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (j : ℕ) (hj : 0 < j) :
    PowerSeriesModule.coeffV j (fullInput π₀ β) = PowerSeriesModule.coeffV j β := by
  simp [fullInput, Nat.ne_of_gt hj]

/-- A finite perturbation bound becomes an affine bound on the actual full
input's t coefficients, preserving the sharper h-order one at degree zero. -/
theorem fullInput_affine_bound (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (L : ℤ) (hL : L ≤ 1)
    (hβL : ∀ j ≤ D, LaurentModule.BoundedBelow L (PowerSeriesModule.coeffV j β)) :
    ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV j (fullInput π₀ β)) := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [fullInput_coeff_zero π₀ β hβ]
    simpa using LaurentModule.boundedBelow_single (k := k) 1 π₀
  · rw [fullInput_coeff_positive π₀ β j (Nat.pos_of_ne_zero hj0)]
    apply boundedBelow_mono (hβL j hj)
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hm := mul_le_mul_of_nonpos_right hj1 (show L - 1 ≤ 0 by omega)
    nlinarith

/-- An actual fixed-arity operation, extended first in h and then in t. -/
def arityTerm (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (m : ℕ) :
    PowerSeriesModule (LaurentSeries k) (LaurentModule k W) :=
  PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars (C m)) (fun _ ↦ α)

/-- The key joint estimate: arity m contributes only at h-degree at least
m+D(L−1) in t-degree D. It holds for every independent coefficient tuple. -/
theorem arityTerm_bound
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D m : ℕ) (L : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV j α)) :
    LaurentModule.BoundedBelow ((m : ℤ) + (D : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV D (arityTerm C α m)) := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  rw [arityTerm, PowerSeriesModule.coeffV_applyMultilinear]
  apply boundedBelow_sum
  intro a ha
  have hsum := (Finset.mem_piAntidiag.mp ha).1
  have hbound := LaurentModule.boundedBelow_applyMultilinear (C m)
    (fun i ↦ PowerSeriesModule.coeffV (a i) α)
    (b := fun i ↦ 1 + (a i : ℤ) * (L - 1)) (fun i ↦ hα (a i) (by
      calc
        a i ≤ ∑ j, a j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        _ = D := hsum))
  have hs : (∑ i : Fin m, (1 + (a i : ℤ) * (L - 1))) = (m : ℤ) + (D : ℤ) * (L - 1) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Nat.cast_sum, hsum]
  rw [hs] at hbound
  exact hbound

/-- A concrete finite graph-arity cutoff for the requested joint coefficient. -/
def arityCutoff (D : ℕ) (H L : ℤ) : ℕ := (H - (D : ℤ) * (L - 1)).toNat + 1

theorem arityTerm_coeff_zero_of_cutoff
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (D m : ℕ) (H L : ℤ)
    (hα : ∀ j ≤ D, LaurentModule.BoundedBelow (1 + (j : ℤ) * (L - 1))
      (PowerSeriesModule.coeffV j α)) (hm : arityCutoff D H L ≤ m) :
    LaurentModule.coeff (PowerSeriesModule.coeffV D (arityTerm C α m)) H = 0 := by
  apply arityTerm_bound C α D m L hα
  unfold arityCutoff at hm
  have hm' : ((H - (D : ℤ) * (L - 1)).toNat : ℤ) < m := by omega
  omega

/-- The full graph-arity coefficient sum has proved finite support, even for
arbitrary Laurent perturbation coefficients. -/
theorem arityTerm_coeff_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W))
    (π₀ : V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) (H : ℤ) :
    Function.HasFiniteSupport (fun m ↦ LaurentModule.coeff
      (PowerSeriesModule.coeffV D (arityTerm C (fullInput π₀ β) m)) H) := by
  obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
  apply (Finset.finite_toSet (Finset.range (arityCutoff D H L))).subset
  intro m hm
  by_contra hn
  have hcut : arityCutoff D H L ≤ m := by simpa using hn
  exact hm (arityTerm_coeff_zero_of_cutoff C _ D m H L
    (fullInput_affine_bound π₀ β hβ D L hL hβL) hcut)

end EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorArityBounds
