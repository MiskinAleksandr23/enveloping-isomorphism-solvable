import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates

/-! Original direction/ratio formulas require only positivity of their own
common scale. Other, disjoint forest radii may vanish. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPartialPositiveDR
open ForestDirectionRatioCoordinates ForestInsertionDifference AncestorScaleRatios
open scoped Classical
variable (T : RootedTree) [Fintype T] {I : Type*} (leaf : I → T)
  (p : ForestDirectionRatioCoordinates.Parameters T)

theorem scale_nonneg (h : ∀ v, 0 ≤ p.1 v) (v : T) : 0 ≤ scale p.1 v :=
  Finset.prod_nonneg (fun u _ => h u)

theorem direction_eq_actual (e : Pair I) (h : 0 < scale p.1 (pairNode T leaf e)) :
    direction T leaf p e = complexPhase (pairDifference T leaf p e) := by
  rw [pairDifference_factor, complexPhase_pos_real_smul h]
  rfl

theorem norm_pairDifference (h : ∀ v, 0 ≤ p.1 v) (e : Pair I) :
    ‖pairDifference T leaf p e‖ = scale p.1 (pairNode T leaf e) * ‖pairUnit T leaf p e‖ := by
  rw [pairDifference_factor, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (scale_nonneg T p h _)]

theorem ratio_eq_resolvedRatio (v w : T) (U V : ℝ) (h : scale p.1 (v ⊓ w) ≠ 0) :
    scale p.1 v * U / (scale p.1 v * U + scale p.1 w * V) = resolvedRatio p.1 v w U V := by
  rw [scale_factor p.1 (inf_le_left : v ⊓ w ≤ v), scale_factor p.1 (inf_le_right : v ⊓ w ≤ w)]
  simp only [resolvedRatio, resolvedDenominator, mul_assoc, ← mul_add]
  exact mul_div_mul_left _ _ h

theorem ratioValue_eq_actual (h : ∀ v, 0 ≤ p.1 v) (q : Triple I)
    (hc : scale p.1 (pairNode T leaf (firstPair q) ⊓ pairNode T leaf (secondPair q)) ≠ 0) :
    ratioValue T leaf p q =
      (normalizedNormRatio (pairDifference T leaf p (firstPair q))
        (pairDifference T leaf p (secondPair q)) : ℝ) := by
  change _ = ‖pairDifference T leaf p (firstPair q)‖ /
    (‖pairDifference T leaf p (firstPair q)‖ + ‖pairDifference T leaf p (secondPair q)‖)
  rw [norm_pairDifference T leaf p h, norm_pairDifference T leaf p h]
  exact (ratio_eq_resolvedRatio T p _ _ _ _ hc).symm
end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPartialPositiveDR
