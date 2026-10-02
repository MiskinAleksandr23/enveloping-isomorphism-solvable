import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrames
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii

/-! The genuine positive-locus inverse of marked forest insertion. All identification
equations are proved from explicit normalized increment constraints. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameInverse

open ForestMarkedFrames ForestInsertionDifference ForestNormalizationTelescope AncestorScaleRatios
open scoped Classical

variable (T : RootedTree) [Fintype T]

/-- Actual frame equations on increments, including reality of cumulative
positions at stable nodes. No center/radius identification equation is a premise. -/
def Normalized (F : Frames T) (r : T → ℝ) (a : T → ℂ) : Prop :=
  ∀ v (hv : ¬ IsMax v), match F v hv with
    | .complex b c _ _ _ => a b = 0 ∧ ‖a c‖ = 1
    | .stableHeight b _ => a b = Complex.I ∧ (position T r a v).im = 0
    | .stableRealPair b c _ _ _ => a b = 0 ∧ a c = 1 ∧ (position T r a v).im = 0

def PositiveInternal (r : T → ℝ) : Prop := ∀ v, ¬ IsMax v → 0 < r v

theorem scale_pos_internal (r : T → ℝ) (hr : PositiveInternal T r)
    (v : T) (hv : ¬ IsMax v) : 0 < scale r v := by
  apply Finset.prod_pos
  intro u hu
  apply hr u
  intro hmax
  have huv := (mem_ancestors u v).mp hu
  exact hv ((le_antisymm huv (hmax huv)) ▸ hmax)

theorem position_child (r : T → ℝ) (a : T → ℂ) (v w : T) (hw : v ⋖ w) :
    position T r a w = scale r v • a w + position T r a v := by
  rw [position_step T r a w (ne_bot_of_gt hw.lt), hw.pred_eq]

/-- The leaf-evaluation recursion recovers every actual cumulative node position.
This part is algebraic and remains valid when internal radii vanish. -/
theorem center_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (ha : Normalized T F r a) (v : T) :
    center T F v (position T r a) = position T r a v := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hv : IsMax v
    · exact center_leaf T F v hv _
    · have hn := ha v hv
      cases hf : F v hv with
      | complex b c hb hc hne =>
        rw [hf] at hn
        rw [center_complex T F v b c hv hb hc hne hf, ih b hb.lt,
          position_child T r a v b hb, hn.1, smul_zero, zero_add]
      | stableHeight b hb =>
        rw [hf] at hn
        rw [center_stableHeight T F v b hv hb hf, ih b hb.lt,
          position_child T r a v b hb, hn.1]
        apply Complex.ext <;> simp [Complex.add_re, hn.2]
      | stableRealPair b c hb hc hne =>
        rw [hf] at hn
        rw [center_stableRealPair T F v b c hv hb hc hne hf, ih b hb.lt,
          position_child T r a v b hb, hn.1, smul_zero, zero_add]
        apply Complex.ext <;> simp [hn.2.2]

theorem centers_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (ha : Normalized T F r a) : centers T F (position T r a) = position T r a := by
  funext v
  exact center_position T F r a ha v

/-- The same result uses only inserted LEAF values; internal input positions may
be extended arbitrarily. -/
theorem center_of_leaf_positions (F : Frames T) (r : T → ℝ) (a p : T → ℂ)
    (ha : Normalized T F r a) (hp : ∀ v, IsMax v → p v = position T r a v) (v : T) :
    center T F v p = position T r a v := by
  rw [center_congr_leaves T F p (position T r a) hp, center_position T F r a ha]

/-- Only internal marked radii are geometric: the factory's absolute leaf radii
are fixed dummy values. -/
theorem radius_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (v : T) (hv : ¬ IsMax v) :
    radius T F (position T r a) v = scale r v := by
  rw [radius_nonleaf T F _ v hv, centers_position T F r a ha]
  have hn := ha v hv
  cases hf : F v hv with
  | complex b c hb hc hne =>
    rw [hf] at hn
    change ‖position T r a c - position T r a b‖ = scale r v
    rw [position_child T r a v b hb, position_child T r a v c hc, hn.1,
      smul_zero, zero_add, add_sub_cancel_right, norm_smul, hn.2, mul_one,
      Real.norm_of_nonneg (scale_pos_internal T r hr v hv).le]
  | stableHeight b hb =>
    rw [hf] at hn
    change (position T r a b).im = scale r v
    rw [position_child T r a v b hb, hn.1]
    simp [Complex.add_im, hn.2]
  | stableRealPair b c hb hc hne =>
    rw [hf] at hn
    change (position T r a c).re - (position T r a b).re = scale r v
    rw [position_child T r a v b hb, position_child T r a v c hc, hn.1, hn.2.1]
    simp [Complex.add_re]

theorem positiveGaps_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) :
    position T r a ∈ PositiveGaps T F := by
  intro v
  by_cases hv : IsMax v
  · simp [radius, hv]
  · rw [radius_position T F r a hr ha v hv]
    exact scale_pos_internal T r hr v hv

theorem localRadii_position_internal (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (hroot : r ⊥ = 1)
    (v : T) (hv : ¬ IsMax v) : localRadii T F (position T r a) v = r v := by
  by_cases hv0 : v = ⊥
  · subst v
    rw [localRadii_root T F _ (positiveGaps_position T F r a hr ha), hroot]
  · have hpred : ¬ IsMax (Order.pred v) :=
      not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hv0)
    change radius T F (position T r a) v / radius T F (position T r a) (Order.pred v) = r v
    rw [radius_position T F r a hr ha v hv,
      radius_position T F r a hr ha (Order.pred v) hpred, scale_step T r v hv0,
      mul_div_cancel_right₀ _ (scale_pos_internal T r hr _ hpred).ne']

/-- Fixing the unused recovered leaf ratios gives exactly the original full
radius vector, with root and leaf radii fixed to one. -/
theorem fixLeaves_localRadii_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (hroot : r ⊥ = 1)
    (hleaf : ∀ v, IsMax v → r v = 1) :
    ForestLeafRadii.fixLeaves T (localRadii T F (position T r a)) = r := by
  funext v
  by_cases hv : IsMax v
  · simp [ForestLeafRadii.fixLeaves, hv, hleaf v hv]
  · simpa [ForestLeafRadii.fixLeaves, hv] using
      localRadii_position_internal T F r a hr ha hroot v hv

theorem increments_position_nonroot (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (v : T) (hv : v ≠ ⊥) :
    increments T F (position T r a) v = a v := by
  have hpred : ¬ IsMax (Order.pred v) :=
    not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hv)
  change (radius T F (position T r a) (Order.pred v))⁻¹ •
    (centers T F (position T r a) v - centers T F (position T r a) (Order.pred v)) = a v
  rw [centers_position T F r a ha, radius_position T F r a hr ha _ hpred,
    position_step T r a v hv, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ (scale_pos_internal T r hr _ hpred).ne', one_smul]

theorem increments_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (hroot : a ⊥ = 0) :
    increments T F (position T r a) = a := by
  funext v
  by_cases hv : v = ⊥
  · subst v
    simpa [increments] using hroot.symm
  · exact increments_position_nonroot T F r a hr ha v hv

theorem normalized_child_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a) (v w : T) (hw : v ⋖ w) :
    normalized T F (position T r a) v w = a w := by
  rw [← increments_child T F _ v w hw]
  exact increments_position_nonroot T F r a hr ha w (ne_bot_of_gt hw.lt)

/-- The concrete left inverse: actual insertion followed by the recursively
constructed marked-frame factory recovers normalized parameters. -/
theorem inverse_position (F : Frames T) (r : T → ℝ) (a : T → ℂ)
    (hr : PositiveInternal T r) (ha : Normalized T F r a)
    (hr0 : r ⊥ = 1) (ha0 : a ⊥ = 0) (hleaf : ∀ v, IsMax v → r v = 1) :
    (ForestLeafRadii.fixLeaves T (localRadii T F (position T r a)),
      increments T F (position T r a)) = (r, a) := by
  rw [fixLeaves_localRadii_position T F r a hr ha hr0 hleaf,
    increments_position T F r a hr ha ha0]

/-- Equal inserted leaf positions imply equal normalized parameters. No center
identification equation is assumed in this injectivity theorem. -/
theorem parameters_eq_of_leaf_positions (F : Frames T) (r s : T → ℝ) (a b : T → ℂ)
    (hr : PositiveInternal T r) (hs : PositiveInternal T s)
    (ha : Normalized T F r a) (hb : Normalized T F s b)
    (hr0 : r ⊥ = 1) (hs0 : s ⊥ = 1) (ha0 : a ⊥ = 0) (hb0 : b ⊥ = 0)
    (hrleaf : ∀ v, IsMax v → r v = 1) (hsleaf : ∀ v, IsMax v → s v = 1)
    (hpos : ∀ v, IsMax v → position T r a v = position T s b v) : (r, a) = (s, b) := by
  have hc : centers T F (position T r a) = centers T F (position T s b) := by
    funext v
    exact center_congr_leaves T F _ _ hpos v
  have hR : radius T F (position T r a) = radius T F (position T s b) := by
    funext v
    simp only [radius, hc]
  rw [← inverse_position T F r a hr ha hr0 ha0 hrleaf,
    ← inverse_position T F s b hs hb hs0 hb0 hsleaf]
  simp only [localRadii, increments, hc, hR]

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameInverse
