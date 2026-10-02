import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates

/-! Leaf radii do not parameterize the configuration. They may be fixed, so a
forest chart varies only radii of nonroot internal nodes. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii

open AncestorScaleRatios ForestInsertionDifference
open scoped BigOperators Classical

variable (T : RootedTree) [Fintype T]
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem scale_eq_of_nonleaf (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (v : T) (hv : ¬ IsMax v) : scale r v = scale s v := by
  apply Finset.prod_congr rfl
  intro u hu
  apply h u
  intro hmax
  exact hv ((hmax ((mem_ancestors u v).mp hu)).antisymm ((mem_ancestors u v).mp hu) ▸ hmax)

theorem scale_pred_eq (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (u : T) (hu : u ≠ ⊥) : scale r (Order.pred u) = scale s (Order.pred u) :=
  scale_eq_of_nonleaf T r s h _ (not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hu))

theorem residual_pred_eq (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (c u : T) (hu : u ≠ ⊥) :
    residualScale r c (Order.pred u) = residualScale s c (Order.pred u) := by
  unfold residualScale
  apply Finset.prod_congr rfl
  intro v hv
  exact h v (not_isMax_of_lt (lt_of_le_of_lt
    ((mem_ancestors v (Order.pred u)).mp (Finset.mem_sdiff.mp hv).1)
    (Order.pred_lt_iff_ne_bot.mpr hu)))

theorem position_eq (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (a : T → M) (v : T) : position T r a v = position T s a v := by
  unfold position
  apply Finset.sum_congr rfl
  intro u hu
  rw [scale_pred_eq T r s h u (Finset.mem_erase.mp hu).1]

theorem branchUnit_eq (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (a : T → M) (c v : T) : branchUnit T r a c v = branchUnit T s a c v := by
  unfold branchUnit
  apply Finset.sum_congr rfl
  intro u hu
  rw [residual_pred_eq T r s h c u (branch_ne_root T hu)]

theorem unitDifference_eq (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (a : T → M) (v w : T) : unitDifference T r a v w = unitDifference T s a v w := by
  rw [unitDifference, unitDifference, branchUnit_eq T r s h, branchUnit_eq T r s h]

theorem residual_eq_of_nonleaf (r s : T → R) (h : ∀ u, ¬ IsMax u → r u = s u)
    (c v : T) (hv : ¬ IsMax v) : residualScale r c v = residualScale s c v := by
  unfold residualScale
  apply Finset.prod_congr rfl
  intro u hu
  apply h u
  intro hmax
  have huv := (mem_ancestors u v).mp (Finset.mem_sdiff.mp hu).1
  have heq : u = v := le_antisymm huv (hmax huv)
  exact hv (heq ▸ hmax)

section Coordinates

open ForestDirectionRatioCoordinates

variable {Label : Type*} (lab : Label → T)

omit [Fintype T] in
theorem pairNode_nonleaf (hinj : Function.Injective lab) (hleaf : ∀ i, IsMax (lab i))
    (p : Pair Label) : ¬ IsMax (pairNode T lab p) :=
  not_isMax_of_lt (inf_lt_left_of_leaf T (hleaf p.val.1) (hinj.ne p.property))

theorem direction_eq (r s : T → ℝ) (h : ∀ u, ¬ IsMax u → r u = s u)
    (a : T → ℂ) (p : Pair Label) : direction T lab (r, a) p = direction T lab (s, a) p := by
  unfold direction pairUnit
  rw [unitDifference_eq T r s h]

theorem ratioValue_eq (hinj : Function.Injective lab) (hleaf : ∀ i, IsMax (lab i))
    (r s : T → ℝ) (h : ∀ u, ¬ IsMax u → r u = s u)
    (a : T → ℂ) (q : Triple Label) : ratioValue T lab (r, a) q = ratioValue T lab (s, a) q := by
  unfold ratioValue pairUnit
  rw [unitDifference_eq T r s h, unitDifference_eq T r s h]
  unfold resolvedRatio resolvedDenominator
  rw [residual_eq_of_nonleaf T r s h _ _ (pairNode_nonleaf T lab hinj hleaf (firstPair q)),
    residual_eq_of_nonleaf T r s h _ _ (pairNode_nonleaf T lab hinj hleaf (secondPair q))]

/-- Every stored direction and ratio is unchanged when unused leaf radii are fixed. -/
theorem resolvedCoordinates_eq (hinj : Function.Injective lab) (hleaf : ∀ i, IsMax (lab i))
    (r s : T → ℝ) (h : ∀ u, ¬ IsMax u → r u = s u) (a : T → ℂ)
    (hr : Admissible T lab (r, a)) (hs : Admissible T lab (s, a)) :
    resolvedCoordinates T lab ⟨(r, a), hr⟩ = resolvedCoordinates T lab ⟨(s, a), hs⟩ := by
  apply Prod.ext
  · funext p
    exact direction_eq T lab r s h a p
  · funext q
    apply Subtype.ext
    exact ratioValue_eq T lab hinj hleaf r s h a q

def fixLeaves (r : T → ℝ) : T → ℝ := fun u => if IsMax u then 1 else r u

omit [Fintype T] in
theorem fixLeaves_agree (r : T → ℝ) : ∀ u, ¬ IsMax u → r u = fixLeaves T r u := by
  intro u hu
  simp [fixLeaves, hu]

theorem admissible_fixLeaves (r : T → ℝ) (a : T → ℂ) (hr : Admissible T lab (r, a)) :
    Admissible T lab (fixLeaves T r, a) := by
  constructor
  · intro u
    by_cases hu : IsMax u <;> simp [fixLeaves, hu, hr.1 u]
  · intro p
    change unitDifference T (fixLeaves T r) a (lab p.val.2) (lab p.val.1) ≠ 0
    rw [← unitDifference_eq T r (fixLeaves T r) (fixLeaves_agree T r)]
    exact hr.2 p

theorem resolvedCoordinates_fixLeaves (hinj : Function.Injective lab)
    (hleaf : ∀ i, IsMax (lab i)) (r : T → ℝ) (a : T → ℂ) (hr : Admissible T lab (r, a)) :
    resolvedCoordinates T lab ⟨(r, a), hr⟩ =
      resolvedCoordinates T lab ⟨(fixLeaves T r, a), admissible_fixLeaves T lab r a hr⟩ :=
  resolvedCoordinates_eq T lab hinj hleaf r (fixLeaves T r) (fixLeaves_agree T r) a hr _

/-- Positivity is required only for actual internal-node scales. Leaf radii
may already be zero: they have no effect on the original configuration. -/
theorem resolvedCoordinates_eq_raw_of_positive_internal (hinj : Function.Injective lab)
    (hleaf : ∀ i, IsMax (lab i)) (r : T → ℝ) (a : T → ℂ)
    (hr : Admissible T lab (r, a)) (hpos : ∀ u, ¬ IsMax u → 0 < r u) :
    resolvedCoordinates T lab ⟨(r, a), hr⟩ = rawCoordinates T lab (r, a) := by
  rw [resolvedCoordinates_fixLeaves T lab hinj hleaf r a hr]
  have hfixed : ∀ u, 0 < fixLeaves T r u := by
    intro u
    by_cases hu : IsMax u <;> simp [fixLeaves, hu, hpos u]
  rw [ForestDirectionRatioCoordinates.resolvedCoordinates_eq_raw _ _ _ hfixed]
  have hpositions : ∀ v, position T (fixLeaves T r) a v = position T r a v :=
    fun v => (position_eq T r (fixLeaves T r) (fixLeaves_agree T r) a v).symm
  simp only [rawCoordinates, pairDifference, hpositions]

end Coordinates

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii
