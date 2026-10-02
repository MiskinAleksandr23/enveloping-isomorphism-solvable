import EnvelopingIsomorphism.Deformation.Gauge.TaylorTwistEvaluation
import EnvelopingIsomorphism.FormalSeries.LaurentPartialEvaluation

/-! Actual Laurent placement maps and the exact h-power from their fixed complement slots. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries
open scoped BigOperators Classical

universe u v
variable {k : Type u} [Field k]
variable {V W : Type v} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Every fixed complementary slot contributes one actual h monomial. Selected
Laurent inputs remain independent and retain the native finite-subset ordering. -/
theorem applyMultilinear_placementMap_single_one
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    {m r : ℕ} (s : Finset (Fin m)) (hs : s.card = r)
    (x : Fin r → LaurentModule k V) :
    LaurentModule.applyMultilinear (C m)
      (fun i => Sum.elim x (fun _ => LaurentModule.single 1 π₀)
        ((finSumEquivOfFinset hs (by simp [Finset.card_compl, hs] : sᶜ.card = m - r)).symm i)) =
      (HahnSeries.single ((m - r : ℕ) : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.applyMultilinear (placementMap C π₀ s hs) x := by
  have h := LaurentModule.applyMultilinear_partialFinset_single hs
    (by simp [Finset.card_compl, hs] : sᶜ.card = m - r) (C m)
    (fun _ => π₀) (fun _ => (1 : ℤ)) x
  simpa [placementMap] using h

/-- The same identity for the actual Laurent-linear extended cochain maps. -/
theorem extendScalars_placementMap_single_one
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    {m r : ℕ} (s : Finset (Fin m)) (hs : s.card = r)
    (x : Fin r → LaurentModule k V) :
    LaurentModule.extendScalars (C m)
      (fun i => Sum.elim x (fun _ => LaurentModule.single 1 π₀)
        ((finSumEquivOfFinset hs (by simp [Finset.card_compl, hs] : sᶜ.card = m - r)).symm i)) =
      (HahnSeries.single ((m - r : ℕ) : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.extendScalars (placementMap C π₀ s hs) x :=
  applyMultilinear_placementMap_single_one C π₀ s hs x

/-- Whole-map identity for the actual selected-slot Laurent placement operation. -/
theorem placementMap_extendScalars_single_one
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V)
    {m r : ℕ} (s : Finset (Fin m)) (hs : s.card = r) :
    placementMap (fun m => LaurentModule.extendScalars (C m))
        (LaurentModule.single 1 π₀) s hs =
      (HahnSeries.single ((m - r : ℕ) : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.extendScalars (placementMap C π₀ s hs) := by
  apply MultilinearMap.ext
  intro x
  exact extendScalars_placementMap_single_one C π₀ s hs x

/-- Every selected subset has the same complement size, so its exact h-shift
factors out of the actual finite placement-component sum. -/
theorem placementComponent_extendScalars_single_one
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (r m : ℕ) :
    placementComponent (fun m => LaurentModule.extendScalars (C m))
        (LaurentModule.single 1 π₀) r m =
      (HahnSeries.single ((m - r : ℕ) : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.extendScalars (placementComponent C π₀ r m) := by
  simp only [placementComponent, placementMap_extendScalars_single_one,
    LaurentModule.extendScalars_finset_sum, Finset.smul_sum]

/-- The fixed-arity component with j complementary slots contributes precisely h^j. -/
theorem placementComponent_extendScalars_add_single_one
    (C : GraphTaylorFamily (k := k) (V := V) (W := W)) (π₀ : V) (r j : ℕ) :
    placementComponent (fun m => LaurentModule.extendScalars (C m))
        (LaurentModule.single 1 π₀) r (r + j) =
      (HahnSeries.single (j : ℤ) (1 : k) : LaurentSeries k) •
        LaurentModule.extendScalars (placementComponent C π₀ r (r + j)) := by
  simpa only [Nat.add_sub_cancel_left] using
    placementComponent_extendScalars_single_one C π₀ r (r + j)

end EnvelopingIsomorphism.Deformation.Gauge
