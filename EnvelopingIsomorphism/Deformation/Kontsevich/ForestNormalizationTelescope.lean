import EnvelopingIsomorphism.Deformation.Kontsevich.ForestInsertionDifference

/-! Literal product and path-sum telescoping for actual centers and radii on a
finite native rooted tree. These are forward insertion parameters only; no free
frame or geometric admissibility condition is assumed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope

open AncestorScaleRatios ForestInsertionDifference
open scoped BigOperators Classical

variable (t : RootedTree) [Fintype t]

@[simp] theorem ancestors_root : ancestors (⊥ : t) = {⊥} := by
  ext u
  simp only [mem_ancestors, Finset.mem_singleton, le_bot_iff]

/-- The actual finite ancestor set splits into the node and its parent's ancestors. -/
theorem ancestors_eq_insert_pred (v : t) : ancestors v = insert v (ancestors (Order.pred v)) := by
  ext u
  simp only [mem_ancestors, Finset.mem_insert]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inr (Order.le_pred_of_lt h)
    · exact Or.inl h
  · rintro (rfl | h)
    · exact le_rfl
    · exact h.trans (Order.pred_le v)

theorem not_mem_ancestors_pred (v : t) (hv : v ≠ ⊥) : v ∉ ancestors (Order.pred v) := by
  rw [mem_ancestors]
  exact (Order.pred_lt_iff_ne_bot.mpr hv).not_ge

section Products

variable {K : Type*} [CommMonoid K]

@[simp] theorem scale_root (ρ : t → K) : scale ρ (⊥ : t) = ρ ⊥ := by
  simp [scale, ancestors_root]

/-- The literal finite ancestor product has this actual one-edge recurrence. -/
theorem scale_step (ρ : t → K) (v : t) (hv : v ≠ ⊥) :
    scale ρ v = ρ v * scale ρ (Order.pred v) := by
  rw [scale, ancestors_eq_insert_pred, Finset.prod_insert (not_mem_ancestors_pred t v hv)]
  rfl

end Products

section Sums

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

@[simp] theorem position_root (ρ : t → K) (a : t → M) : position t ρ a (⊥ : t) = 0 := by
  simp [position, ancestors_root]

/-- The literal insertion sum adds precisely the displacement at the scale of the parent. -/
theorem position_step (ρ : t → K) (a : t → M) (v : t) (hv : v ≠ ⊥) :
    position t ρ a v = scale ρ (Order.pred v) • a v + position t ρ a (Order.pred v) := by
  have hn : v ∉ (ancestors (Order.pred v)).erase ⊥ :=
    fun h ↦ not_mem_ancestors_pred t v hv (Finset.mem_of_mem_erase h)
  rw [position, ancestors_eq_insert_pred, Finset.erase_insert_of_ne hv, Finset.sum_insert hn]
  rfl

/-- The root increment is actually absent from every insertion sum. -/
theorem position_congr_nonroot (ρ : t → K) (a b : t → M)
    (hab : ∀ u, u ≠ ⊥ → a u = b u) (v : t) : position t ρ a v = position t ρ b v := by
  unfold position
  apply Finset.sum_congr rfl
  intro u hu
  rw [hab u (Finset.mem_erase.mp hu).1]

end Sums

/-- Adjacent-radius ratios. At the root this is Rroot/Rroot, hence exactly one
under the genuine positivity hypothesis below. -/
def localRadius (R : t → ℝ) (v : t) : ℝ := R v / R (Order.pred v)

omit [Fintype t] in
@[simp] theorem localRadius_root (R : t → ℝ) (hR : ∀ v, 0 < R v) : localRadius t R ⊥ = 1 := by
  simp [localRadius, ne_of_gt (hR ⊥)]

omit [Fintype t] in
theorem localRadius_pos (R : t → ℝ) (hR : ∀ v, 0 < R v) (v : t) : 0 < localRadius t R v :=
  div_pos (hR v) (hR (Order.pred v))

/-- The actual ancestor product telescopes to absolute radius divided by root radius. -/
theorem scale_localRadius (R : t → ℝ) (hR : ∀ v, 0 < R v) (v : t) :
    scale (localRadius t R) v = R v / R ⊥ := by
  letI : WellFoundedLT t := Finite.to_wellFoundedLT
  induction v using WellFoundedLT.induction
  rename_i v ih
  by_cases hv : v = ⊥
  · subst v
    rw [scale_root, localRadius_root t R hR, div_self (ne_of_gt (hR ⊥))]
  · rw [scale_step t _ v hv, ih (Order.pred v) (Order.pred_lt_iff_ne_bot.mpr hv)]
    exact div_mul_div_cancel₀ (ne_of_gt (hR (Order.pred v)))

section Centers

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Actual parent-normalized center displacement, with the target-minus-parent sign. -/
def localIncrement (R : t → ℝ) (C : t → M) (v : t) : M :=
  (R (Order.pred v))⁻¹ • (C v - C (Order.pred v))

omit [Fintype t] in
@[simp] theorem localIncrement_root (R : t → ℝ) (C : t → M) : localIncrement t R C ⊥ = 0 := by
  simp [localIncrement]

/-- Multiplication by the actual parent scale cancels the local denominator. -/
theorem scaled_localIncrement (R : t → ℝ) (hR : ∀ v, 0 < R v) (C : t → M) (v : t) :
    scale (localRadius t R) (Order.pred v) • localIncrement t R C v =
      (R ⊥)⁻¹ • (C v - C (Order.pred v)) := by
  rw [scale_localRadius t R hR, localIncrement, smul_smul]
  have he : R (Order.pred v) / R ⊥ * (R (Order.pred v))⁻¹ = (R ⊥)⁻¹ := by
    simpa only [one_div] using div_mul_div_cancel₀' (ne_of_gt (hR (Order.pred v))) (R ⊥) 1
  rw [he]

/-- The literal ancestor-path sum telescopes to the actual root-normalized center. -/
theorem position_localRadius_increment (R : t → ℝ) (hR : ∀ v, 0 < R v)
    (C : t → M) (v : t) :
    position t (localRadius t R) (localIncrement t R C) v = (R ⊥)⁻¹ • (C v - C ⊥) := by
  letI : WellFoundedLT t := Finite.to_wellFoundedLT
  induction v using WellFoundedLT.induction
  rename_i v ih
  by_cases hv : v = ⊥
  · subst v
    simp
  · rw [position_step t _ _ v hv, scaled_localIncrement t R hR C v,
      ih (Order.pred v) (Order.pred_lt_iff_ne_bot.mpr hv), ← smul_add, sub_add_sub_cancel]

/-- Any selected value of the ignored root increment gives the same actual telescope. -/
theorem position_localRadius_increment_update_root (R : t → ℝ) (hR : ∀ v, 0 < R v)
    (C : t → M) (rootValue : M) (v : t) :
    position t (localRadius t R) (Function.update (localIncrement t R C) ⊥ rootValue) v =
      (R ⊥)⁻¹ • (C v - C ⊥) := by
  rw [position_congr_nonroot t (localRadius t R) _ (localIncrement t R C)
    (fun u hu ↦ Function.update_of_ne hu _ _) v]
  exact position_localRadius_increment t R hR C v

/-- Actual centers are reconstructed by translating and multiplying the insertion by Rroot. -/
theorem reconstruct_center (R : t → ℝ) (hR : ∀ v, 0 < R v) (C : t → M) (v : t) :
    C ⊥ + R ⊥ • position t (localRadius t R) (localIncrement t R C) v = C v := by
  rw [position_localRadius_increment t R hR C v, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (hR ⊥)), one_smul, add_sub_cancel]

/-- Differences telescope with the same target-minus-source convention as the native insertion. -/
theorem position_difference (R : t → ℝ) (hR : ∀ v, 0 < R v) (C : t → M) (v w : t) :
    position t (localRadius t R) (localIncrement t R C) v -
      position t (localRadius t R) (localIncrement t R C) w =
        (R ⊥)⁻¹ • (C v - C w) := by
  rw [position_localRadius_increment t R hR C v, position_localRadius_increment t R hR C w,
    ← smul_sub]
  congr 1
  abel

end Centers

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestNormalizationTelescope
