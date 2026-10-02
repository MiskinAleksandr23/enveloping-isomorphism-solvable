import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates

/-! Zero and positive triple-ratio detectors for the actual resolved forest
encoder. Common zero ancestors are already factored out by residual products;
no nonzero absolute-scale premise is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestResolvedRatioZero
open AncestorScaleRatios ForestDirectionRatioCoordinates
open scoped Classical

variable (t : RootedTree) [Fintype t] {Label : Type*} (lab : Label → t)

/-- The residual product vanishes exactly when one remaining ancestor radius
vanishes; radii at and above the factored ancestor are absent. -/
theorem residualScale_eq_zero_iff (ρ : t → ℝ) (v w : t) :
    residualScale ρ v w = 0 ↔ ∃ u : t, u ≤ w ∧ ¬u ≤ v ∧ ρ u = 0 := by
  simp only [residualScale, Finset.prod_eq_zero_iff, Finset.mem_sdiff, mem_ancestors]
  constructor
  · rintro ⟨u, ⟨huw, huv⟩, hzero⟩; exact ⟨u, huw, huv, hzero⟩
  · rintro ⟨u, huw, huv, hzero⟩; exact ⟨u, ⟨huw, huv⟩, hzero⟩

/-- Positivity of the regular pair units makes the denominator strictly
positive even at corners of arbitrary depth. -/
theorem ratioValue_eq_zero_iff_exists_residual_zero
    (x : Domain t lab) (q : Triple Label) :
    ratioValue t lab x.val q = 0 ↔ ∃ u : t,
      u ≤ pairNode t lab (firstPair q) ∧
      ¬u ≤ pairNode t lab (secondPair q) ∧ x.val.1 u = 0 := by
  have hU := norm_pos_iff.mpr (x.property.2 (firstPair q))
  have hV := norm_pos_iff.mpr (x.property.2 (secondPair q))
  have hd := resolvedDenominator_pos x.val.1 x.property.1 (tripleNodes_comparable t lab q) hU hV
  unfold ratioValue resolvedRatio
  rw [div_eq_zero_iff, or_iff_left hd.ne', mul_eq_zero, or_iff_left hU.ne', residualScale_eq_zero_iff]
  constructor
  · rintro ⟨u, hu, hn, hz⟩
    exact ⟨u, hu, fun hw ↦ hn (le_inf hu hw), hz⟩
  · rintro ⟨u, hu, hn, hz⟩
    exact ⟨u, hu, fun hw ↦ hn (hw.trans inf_le_right), hz⟩

/-- Exact inverse detector: a zero encoded ratio exhibits a zero radius
strictly after the denominator LCA and at/before the numerator LCA. -/
theorem ratioValue_eq_zero_iff_exists_zero_between
    (x : Domain t lab) (q : Triple Label) :
    ratioValue t lab x.val q = 0 ↔ ∃ u : t,
      pairNode t lab (secondPair q) < u ∧
      u ≤ pairNode t lab (firstPair q) ∧ x.val.1 u = 0 := by
  rw [ratioValue_eq_zero_iff_exists_residual_zero]
  constructor
  · rintro ⟨u, hu, hn, hz⟩
    have hvw : pairNode t lab (secondPair q) ≤ pairNode t lab (firstPair q) :=
      (tripleNodes_comparable t lab q).resolve_left (fun h ↦ hn (hu.trans h))
    have hwu : pairNode t lab (secondPair q) ≤ u :=
      (le_total_of_directed hu hvw).resolve_right hn
    exact ⟨u, lt_of_le_not_ge hwu hn, hu, hz⟩
  · rintro ⟨u, hwu, hu, hz⟩
    exact ⟨u, hu, not_le_of_gt hwu, hz⟩

/-- Direct zero-node detector for arbitrary label positions in the tree.
The zero node may itself have zero ancestors; no division by their scales occurs. -/
theorem ratioValue_eq_zero_of_zero_ancestor
    (x : Domain t lab) (v : t) (hv : x.val.1 v = 0)
    (a b c : Label) (hab : a ≠ b) (hac : a ≠ c)
    (hva : v ≤ lab a) (hvb : v ≤ lab b) (hvc : ¬v ≤ lab c) :
    ratioValue t lab x.val ⟨(a,b,c), hab, hac⟩ = 0 := by
  apply (ratioValue_eq_zero_iff_exists_residual_zero t lab x _).mpr
  exact ⟨v, le_inf hva hvb, fun h ↦ hvc (h.trans inf_le_right), hv⟩

/-- Literal projection of the full direction-ratio encoder. -/
theorem resolvedCoordinates_ratio_eq_zero_of_zero_ancestor
    (x : Domain t lab) (v : t) (hv : x.val.1 v = 0)
    (a b c : Label) (hab : a ≠ b) (hac : a ≠ c)
    (hva : v ≤ lab a) (hvb : v ≤ lab b) (hvc : ¬v ≤ lab c) :
    ((resolvedCoordinates t lab x).2 ⟨(a,b,c), hab, hac⟩ : ℝ) = 0 :=
  ratioValue_eq_zero_of_zero_ancestor t lab x v hv a b c hab hac hva hvb hvc

/-- If the numerator LCA is above the denominator LCA, its residual scale is
one. The actual encoded ratio is therefore strictly positive at all corners. -/
theorem ratioValue_pos_of_pairNode_le (x : Domain t lab) (q : Triple Label)
    (h : pairNode t lab (firstPair q) ≤ pairNode t lab (secondPair q)) :
    0 < ratioValue t lab x.val q := by
  unfold ratioValue
  rw [resolvedRatio_of_le x.val.1 h]
  apply div_pos (norm_pos_iff.mpr (x.property.2 (firstPair q)))
  exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (x.property.2 (firstPair q)))
    (mul_nonneg (residualScale_nonneg x.val.1 x.property.1 _ _) (norm_nonneg _))

/-- When both pairs have one LCA, all ancestor radii cancel literally. -/
theorem ratioValue_eq_unit_ratio_of_pairNode_eq (x : Domain t lab) (q : Triple Label)
    (h : pairNode t lab (firstPair q) = pairNode t lab (secondPair q)) :
    ratioValue t lab x.val q = ‖pairUnit t lab x.val (firstPair q)‖ /
      (‖pairUnit t lab x.val (firstPair q)‖ + ‖pairUnit t lab x.val (secondPair q)‖) := by
  unfold ratioValue
  rw [resolvedRatio_of_le x.val.1 h.le, h, residualScale_self, one_mul]

theorem ratioValue_pos_of_pairNode_eq (x : Domain t lab) (q : Triple Label)
    (h : pairNode t lab (firstPair q) = pairNode t lab (secondPair q)) :
    0 < ratioValue t lab x.val q := ratioValue_pos_of_pairNode_le t lab x q h.le


/-- Positivity detects exactly the absence of a vanishing residual radius. -/
theorem ratioValue_pos_iff_all_between_pos (x : Domain t lab) (q : Triple Label) :
    0 < ratioValue t lab x.val q ↔ ∀ u : t,
      pairNode t lab (secondPair q) < u → u ≤ pairNode t lab (firstPair q) → 0 < x.val.1 u := by
  constructor
  · intro h u hwu huv
    apply lt_of_le_of_ne (x.property.1 u)
    intro hz
    exact h.ne' ((ratioValue_eq_zero_iff_exists_zero_between t lab x q).mpr ⟨u, hwu, huv, hz.symm⟩)
  · intro h
    by_contra hn
    have hz : ratioValue t lab x.val q = 0 :=
      le_antisymm (le_of_not_gt hn) (ratioValue_mem_Icc t lab x.val x.property q).1
    obtain ⟨u, hwu, huv, hu⟩ := (ratioValue_eq_zero_iff_exists_zero_between t lab x q).mp hz
    exact (h u hwu huv).ne' hu

/-- The inverse zero detector stated directly for the full native encoder. -/
theorem resolvedCoordinates_ratio_eq_zero_iff_exists_zero_between
    (x : Domain t lab) (q : Triple Label) :
    ((resolvedCoordinates t lab x).2 q : ℝ) = 0 ↔ ∃ u : t,
      pairNode t lab (secondPair q) < u ∧
      u ≤ pairNode t lab (firstPair q) ∧ x.val.1 u = 0 :=
  ratioValue_eq_zero_iff_exists_zero_between t lab x q

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestResolvedRatioZero
