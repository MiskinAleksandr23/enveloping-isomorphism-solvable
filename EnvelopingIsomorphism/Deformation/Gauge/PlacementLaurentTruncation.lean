import EnvelopingIsomorphism.Deformation.Gauge.TaylorLaurentEvaluation
import EnvelopingIsomorphism.FormalSeries.LaurentCochainTruncation

/-! Finite h-coefficient expansion of the actual Laurent placement Taylor family. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open EnvelopingIsomorphism.Deformation.MiddleExactPerturbation
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k]
variable {V W : Type v} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Genuine Laurent placement evaluation truncates at H minus the sum of the
input lower bounds. The coefficient maps are the actual placement components. -/
theorem coeff_laurentPlacementTaylorFamily_finite
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (n : ℕ)
    (x : Fin (n + 1) → LaurentModule k V) (L : Fin (n + 1) → ℤ)
    (hx : ∀ i, LaurentModule.BoundedBelow (L i) (x i)) (H : ℤ) :
    LaurentModule.coeff (laurentPlacementTaylorFamily C π₀ n x) H =
      ∑ j ∈ Finset.range ((H - ∑ i, L i).toNat + 1),
        LaurentModule.coeff
          (LaurentModule.applyMultilinear (placementComponent C π₀ (n + 1) (n + 1 + j)) x)
          (H - j) := by
  change LaurentModule.coeff (LaurentModule.extendCochain (n + 1)
    (toLaurent (placementOperatorCoefficients C π₀ n)) x) H = _
  rw [LaurentModule.coeff_extendCochain_nonnegative (n + 1) _
    (toLaurent_boundedBelow _) x L hx H]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_toLaurent_nat]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge
