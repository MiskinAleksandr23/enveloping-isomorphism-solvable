import EnvelopingIsomorphism.Deformation.Gauge.LaurentTaylorFullIdentity
import EnvelopingIsomorphism.FormalSeries.LaurentAritySummation

/-! The actual all-placement graph evaluation satisfies the verified
all-arity summation hypotheses on every finite t jet. -/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphSummation
open EnvelopingIsomorphism.FormalSeries
open LaurentTaylorArityBounds LaurentFullGraphEvaluation
open scoped BigOperators

universe u v
variable {k : Type u} [Field k] {V W : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem arityTerm_summable
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    LaurentAritySummation.Summable (arityTerm C (fullInput π₀ β)) := by
  intro D
  obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
  refine ⟨(D : ℤ) * (L - 1), ?_⟩
  intro m
  exact arityTerm_bound C _ D m L (fullInput_affine_bound π₀ β hβ D L hL hβL)

/-- A single finite-jet bound works for every split t degree in the bilinear
coefficient convolution. The slope is allowed to depend on the requested jet. -/
theorem arityTerm_local_bounds
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) (D : ℕ) :
    ∃ K : ℤ, ∀ e ≤ D, ∀ m : ℕ,
      LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
        (PowerSeriesModule.coeffV e (arityTerm C (fullInput π₀ β) m)) := by
  obtain ⟨L, hL, hβL⟩ := exists_jet_bound β D
  refine ⟨L - 1, ?_⟩
  intro e he m
  exact arityTerm_bound C _ e m L
    (fullInput_affine_bound π₀ β hβ e L hL (fun j hj ↦ hβL j (hj.trans he)))

/-- The generic coefficientwise arity sum is exactly the graph evaluation
already proved equal to the actual base plus Laurent placement Taylor map. -/
theorem sumSeries_eq_fullEvaluation
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0) :
    LaurentAritySummation.sumSeries (arityTerm C (fullInput π₀ β))
      (arityTerm_summable C π₀ β hβ) = fullEvaluation C π₀ β hβ := by
  apply PowerSeriesModule.ext
  intro D
  apply LaurentModule.ext
  intro H
  rfl

variable {Z : Type v} [AddCommGroup Z] [Module k Z]

/-- Actual homogeneous graph identities sum to the full bilinear identity,
using the proved finite-jet bounds of hπ₀+β and the genuine coefficient sum. -/
theorem fullEvaluation_square_zero_of_homogeneous
    (B : W →ₗ[k] W →ₗ[k] Z)
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (hβ : PowerSeriesModule.coeffV 0 β = 0)
    (hhom : ∀ N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear B)
        (arityTerm C (fullInput π₀ β) p.1) (arityTerm C (fullInput π₀ β) p.2) = 0) :
    PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear B)
      (fullEvaluation C π₀ β hβ) (fullEvaluation C π₀ β hβ) = 0 := by
  have hs := LaurentAritySummation.bilinear_self_eq_zero_of_homogeneous B
    (arityTerm C (fullInput π₀ β)) (arityTerm_summable C π₀ β hβ)
    (arityTerm_local_bounds C π₀ β hβ) hhom
  rw [sumSeries_eq_fullEvaluation] at hs
  exact hs

end EnvelopingIsomorphism.Deformation.Gauge.LaurentFullGraphSummation
