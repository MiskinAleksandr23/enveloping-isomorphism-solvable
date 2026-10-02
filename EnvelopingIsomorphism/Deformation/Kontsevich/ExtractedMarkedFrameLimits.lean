import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestFrames

/-! The actual recursively marked centers follow the extracted child limits.
Consequently their marked gaps are eventually positive, without adding a
positivity premise to the actual compactification point. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameLimits

open Configuration Filter Topology ForestMarkedFrames
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

/-- Internal inputs are immaterial to the recursive factory; its leaf inputs
are the actual original doubled point positions. -/
def markedCenter (k : ℕ) (v : tree i x) : ℂ :=
  ForestMarkedFrames.center (tree i x) (frames i x) v (ExtractedForestParameters.center i x k)

def markedRadius (k : ℕ) (v : tree i x) : ℝ :=
  ForestMarkedFrames.radius (tree i x) (frames i x) (ExtractedForestParameters.center i x k) v

def normalizedCenter (k : ℕ) (v w : tree i x) : ℂ :=
  (positiveRadius i x k v)⁻¹ • (markedCenter i x k w - ExtractedForestParameters.center i x k v)

def centerShift (v : tree i x) : ℂ :=
  if hv : IsMax v then 0 else (frames i x v hv).base (canonicalIncrement i x)

def leadingRadius (v : tree i x) : ℝ :=
  if hv : IsMax v then 1 else (frames i x v hv).radius (canonicalIncrement i x)

theorem leadingRadius_pos (v : tree i x) : 0 < leadingRadius i x v := by
  unfold leadingRadius
  split_ifs with hv
  · exact zero_lt_one
  · exact ExtractedForestFrames.leadingRadius_pos i x v hv

theorem center_real_of_stable (k : ℕ) (v : tree i x) (hv : ¬IsMax v)
    (hs : reflection i x v = v) :
    ForestMarkedFrames.realPart (ExtractedForestParameters.center i x k v) = ExtractedForestParameters.center i x k v := by
  have hl := ExtractedForestIdentification.nonleaf_large i x v hv
  have hs' : ReflectedSubsetNormalization.IsStable doubledReflection ⟨v.val, hl⟩ := by
    unfold ReflectedSubsetNormalization.IsStable
    dsimp only
    simpa only [Finset.ext_iff, Finset.mem_image] using
      (show (reflection i x v).val = v.val.image doubledReflection from rfl).symm.trans
        (congrArg Subtype.val hs)
  simp only [ExtractedForestParameters.center, dif_pos hl,
    ReflectedSubsetNormalization.centerOn, if_pos hs', realPart_apply, Complex.ofReal_re]

theorem normalizedCenter_leaf (k : ℕ) (v : tree i x) (hv : IsMax v) :
    normalizedCenter i x k v v = 0 := by
  simp [normalizedCenter, markedCenter, ForestMarkedFrames.center_leaf _ _ v hv]

theorem limitingRadius_smul_centerShift (v : tree i x) (hv : v ≠ ⊥) :
    limitingRadii i x v • centerShift i x v = 0 := by
  by_cases hm : IsMax v
  · simp [centerShift, hm]
  · simp [limitingRadii, hv, ExtractedForestIdentification.nonleaf_large i x v hm]

/-- Exact transfer of a recursively chosen child center into its parent's old frame. -/
theorem normalizedCenter_child_eq (k : ℕ) (v w : tree i x) (hw : v ⋖ w) :
    normalizedCenter i x k v w =
      localRadii i x k w • normalizedCenter i x k w w + localIncrements i x k w := by
  have hr : positiveRadius i x k w ≠ 0 := (positiveRadius_pos i x k w).ne'
  simp only [normalizedCenter, ExtractedForestParameters.localRadii,
    ForestNormalizationTelescope.localRadius, localIncrements,
    ForestNormalizationTelescope.localIncrement, hw.pred_eq, smul_smul]
  have he : positiveRadius i x k w / positiveRadius i x k v * (positiveRadius i x k w)⁻¹ =
      (positiveRadius i x k v)⁻¹ := by
    field_simp
  rw [he, ← smul_add, sub_add_sub_cancel]

theorem tendsto_child_of_tendsto_self (v w : tree i x) (hw : v ⋖ w)
    (hlim : Tendsto (fun k => normalizedCenter i x k w w) atTop (𝓝 (centerShift i x w))) :
    Tendsto (fun k => normalizedCenter i x k v w) atTop (𝓝 (canonicalIncrement i x w)) := by
  have h := ((tendsto_localRadii i x w).smul hlim).add (tendsto_localIncrements i x w)
  simpa only [← normalizedCenter_child_eq i x _ v w hw,
    limitingRadius_smul_centerShift i x w (ne_of_gt (lt_of_le_of_lt bot_le hw.lt)), zero_add] using h

/-- Upward finite recursion proves the actual new center offsets converge.
Each child's error disappears at the old child/parent radius ratio. -/
theorem tendsto_normalizedCenter_self (v : tree i x) :
    Tendsto (fun k => normalizedCenter i x k v v) atTop (𝓝 (centerShift i x v)) := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hv : IsMax v
    · simpa only [normalizedCenter_leaf i x _ v hv, centerShift, dif_pos hv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · have hc (w : tree i x) (hw : v ⋖ w) :=
        tendsto_child_of_tendsto_self i x v w hw (ih w hw.lt)
      have ht := frames_typeCorrect i x v hv
      cases hf : frames i x v hv with
      | complex a b ha hb hne =>
        have he (k : ℕ) : normalizedCenter i x k v v = normalizedCenter i x k v a := by
          simp only [normalizedCenter, markedCenter,
            ForestMarkedFrames.center_complex _ _ v a b hv ha hb hne hf]
        simpa only [he, centerShift, dif_neg hv, hf, Frame.base] using hc a ha
      | stableHeight a ha =>
        have hs : reflection i x v = v := by
          rw [hf] at ht
          exact ht.1
        have he (k : ℕ) : normalizedCenter i x k v v = ForestMarkedFrames.realPart (normalizedCenter i x k v a) := by
          simp only [normalizedCenter, markedCenter,
            ForestMarkedFrames.center_stableHeight _ _ v a hv ha hf,
            map_smul, map_sub, center_real_of_stable i x k v hv hs, realPart_apply]
        simpa only [Function.comp_def, ← he, centerShift, dif_neg hv, hf, Frame.base, realPart_apply] using
          ForestMarkedFrames.realPart.continuous.continuousAt.tendsto.comp (hc a ha)
      | stableRealPair a b ha hb hne =>
        have hs : reflection i x v = v := by
          rw [hf] at ht
          exact ht.1
        have he (k : ℕ) : normalizedCenter i x k v v = ForestMarkedFrames.realPart (normalizedCenter i x k v a) := by
          simp only [normalizedCenter, markedCenter,
            ForestMarkedFrames.center_stableRealPair _ _ v a b hv ha hb hne hf,
            map_smul, map_sub, center_real_of_stable i x k v hv hs, realPart_apply]
        simpa only [Function.comp_def, ← he, centerShift, dif_neg hv, hf, Frame.base, realPart_apply] using
          ForestMarkedFrames.realPart.continuous.continuousAt.tendsto.comp (hc a ha)

theorem tendsto_normalizedCenter_child (v w : tree i x) (hw : v ⋖ w) :
    Tendsto (fun k => normalizedCenter i x k v w) atTop (𝓝 (canonicalIncrement i x w)) :=
  tendsto_child_of_tendsto_self i x v w hw (tendsto_normalizedCenter_self i x w)

theorem normalizedCenter_sub (k : ℕ) (v a b : tree i x) :
    normalizedCenter i x k v b - normalizedCenter i x k v a =
      (positiveRadius i x k v)⁻¹ • (markedCenter i x k b - markedCenter i x k a) := by
  simp only [normalizedCenter, ← smul_sub]
  congr 1
  abel

/-- The new marked radius is the old radius times an actual leading gap. -/
theorem frameRadius_normalizedCenter (k : ℕ) (v : tree i x) (hv : ¬IsMax v) :
    (frames i x v hv).radius (normalizedCenter i x k v) =
      markedRadius i x k v / positiveRadius i x k v := by
  rw [markedRadius, ForestMarkedFrames.radius_nonleaf _ _ _ v hv]
  have ht := frames_typeCorrect i x v hv
  have hr := inv_pos.mpr (positiveRadius_pos i x k v)
  cases hf : frames i x v hv with
  | complex a b ha hb hne =>
    simp only [Frame.radius, MarkedClusterRescaling.pairRadius, normalizedCenter_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr, div_eq_inv_mul,
      markedCenter, ForestMarkedFrames.centers_apply]
  | stableHeight a ha =>
    rw [hf] at ht
    have hC := congrArg Complex.im (center_real_of_stable i x k v hv ht.1)
    have hz : (ExtractedForestParameters.center i x k v).im = 0 := by
      simpa only [realPart_apply, Complex.ofReal_im] using hC.symm
    simp only [Frame.radius, MarkedClusterRescaling.heightRadius, normalizedCenter,
      Complex.smul_im, Complex.sub_im, hz, sub_zero, smul_eq_mul, div_eq_inv_mul,
      markedCenter, ForestMarkedFrames.centers_apply]
  | stableRealPair a b ha hb hne =>
    simp only [Frame.radius, MarkedClusterRescaling.orderedRealRadius,
      ← Complex.sub_re, normalizedCenter_sub, Complex.smul_re, smul_eq_mul,
      div_eq_inv_mul, markedCenter, ForestMarkedFrames.centers_apply]

/-- Strictly positive limiting units relate every internal marked radius to
the actual extraction radius. -/
theorem tendsto_markedRadius_ratio (v : tree i x) (hv : ¬IsMax v) :
    Tendsto (fun k => markedRadius i x k v / positiveRadius i x k v) atTop
      (𝓝 (leadingRadius i x v)) := by
  simp only [← frameRadius_normalizedCenter i x _ v hv, leadingRadius, dif_neg hv]
  cases hf : frames i x v hv with
  | complex a b ha hb hne =>
    exact ((tendsto_normalizedCenter_child i x v b hb).sub
      (tendsto_normalizedCenter_child i x v a ha)).norm
  | stableHeight a ha =>
    exact Complex.continuous_im.continuousAt.tendsto.comp (tendsto_normalizedCenter_child i x v a ha)
  | stableRealPair a b ha hb hne =>
    exact (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedCenter_child i x v b hb)).sub
      (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedCenter_child i x v a ha))

theorem eventually_markedRadius_pos (v : tree i x) :
    ∀ᶠ k in atTop, 0 < markedRadius i x k v := by
  by_cases hv : IsMax v
  · exact Filter.Eventually.of_forall (fun k => by simp [markedRadius, ForestMarkedFrames.radius, hv])
  · filter_upwards [(tendsto_markedRadius_ratio i x v hv).eventually
      (eventually_gt_nhds (leadingRadius_pos i x v))] with k hk
    exact (div_pos_iff_of_pos_right (positiveRadius_pos i x k v)).mp hk

/-- The actual recursive marked-frame factory has positive gaps along the
original subsequence, eventually and simultaneously at every node. -/
theorem eventually_positiveGaps :
    ∀ᶠ k in atTop, ExtractedForestParameters.center i x k ∈
      ForestMarkedFrames.PositiveGaps (tree i x) (frames i x) :=
  eventually_all.mpr (eventually_markedRadius_pos i x)

private theorem rescale_smul_div (r s : ℝ) (hr : r ≠ 0) (z : ℂ) :
    (r⁻¹ • z) / ((s / r : ℝ) : ℂ) = z / (s : ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
  · have hr' := Complex.ofReal_ne_zero.mpr hr
    have hs' := Complex.ofReal_ne_zero.mpr hs
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div]
    field_simp

def markedNormalized (k : ℕ) (v w : tree i x) : ℂ :=
  ForestMarkedFrames.normalized (tree i x) (frames i x) (ExtractedForestParameters.center i x k) v w

theorem markedNormalized_eq (k : ℕ) (v w : tree i x) :
    markedNormalized i x k v w =
      (normalizedCenter i x k v w - normalizedCenter i x k v v) /
        ((markedRadius i x k v / positiveRadius i x k v : ℝ) : ℂ) := by
  rw [normalizedCenter_sub, rescale_smul_div _ _ (positiveRadius_pos i x k v).ne']
  rfl

/-- The actual normalized marked child coordinates converge to the genuinely
marked-normalized extracted child shape. -/
theorem tendsto_markedNormalized_child (v w : tree i x) (hw : v ⋖ w) :
    Tendsto (fun k => markedNormalized i x k v w) atTop
      (𝓝 ((canonicalIncrement i x w - centerShift i x v) / (leadingRadius i x v : ℂ))) := by
  have hv : ¬IsMax v := not_isMax_of_lt hw.lt
  have h := ((tendsto_normalizedCenter_child i x v w hw).sub
    (tendsto_normalizedCenter_self i x v)).div
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_markedRadius_ratio i x v hv))
        (Complex.ofReal_ne_zero.mpr (leadingRadius_pos i x v).ne')
  simpa only [markedNormalized_eq, Function.comp_def, Pi.div_def] using h

def markedIncrements (k : ℕ) : tree i x → ℂ :=
  ForestMarkedFrames.increments (tree i x) (frames i x) (ExtractedForestParameters.center i x k)

def limitingIncrements (v : tree i x) : ℂ :=
  if v = ⊥ then 0 else
    (canonicalIncrement i x v - centerShift i x (Order.pred v)) / (leadingRadius i x (Order.pred v) : ℂ)

theorem limitingIncrements_child (v w : tree i x) (hw : v ⋖ w) :
    limitingIncrements i x w =
      (frames i x v (not_isMax_of_lt hw.lt)).normalized (canonicalIncrement i x) w := by
  have hwroot : w ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hw.lt)
  have hp := hw.pred_eq
  subst v
  simp only [limitingIncrements, if_neg hwroot, centerShift, leadingRadius,
    dif_neg (not_isMax_of_lt hw.lt), Frame.normalized]

theorem tendsto_markedIncrements (v : tree i x) :
    Tendsto (fun k => markedIncrements i x k v) atTop (𝓝 (limitingIncrements i x v)) := by
  by_cases hv : v = ⊥
  · subst v
    simp [markedIncrements, ForestMarkedFrames.increments, ForestNormalizationTelescope.localIncrement,
      limitingIncrements]
  · have hc := parent_cover i x v hv
    simpa only [markedIncrements, ForestMarkedFrames.increments_child _ _ _ _ v hc,
      limitingIncrements, if_neg hv, markedNormalized] using
        tendsto_markedNormalized_child i x (Order.pred v) v hc

private theorem radius_ratio_rescale (s u r t : ℝ) (hr : r ≠ 0) (ht : t ≠ 0) :
    s / u = ((s / r) / (u / t)) * (r / t) := by
  by_cases hu : u = 0
  · simp [hu]
  · field_simp

/-- Replacing both internal radii by the proved positive limiting units
preserves the original child/parent scale separation. -/
theorem tendsto_internal_markedRadius_ratio (v : tree i x) (hv : v ≠ ⊥) (hm : ¬IsMax v) :
    Tendsto (fun k => markedRadius i x k v / markedRadius i x k (Order.pred v)) atTop (𝓝 0) := by
  have hp : ¬IsMax (Order.pred v) := not_isMax_of_lt (Order.pred_lt_iff_ne_bot.mpr hv)
  have h := ((tendsto_markedRadius_ratio i x v hm).div
    (tendsto_markedRadius_ratio i x (Order.pred v) hp) (leadingRadius_pos i x (Order.pred v)).ne').mul
      (tendsto_localRadii i x v)
  have hz : limitingRadii i x v = 0 := by
    simp [limitingRadii, hv, ExtractedForestIdentification.nonleaf_large i x v hm]
  have he (k : ℕ) := radius_ratio_rescale (markedRadius i x k v) (markedRadius i x k (Order.pred v))
    (positiveRadius i x k v) (positiveRadius i x k (Order.pred v))
      (positiveRadius_pos i x k v).ne' (positiveRadius_pos i x k (Order.pred v)).ne'
  simpa only [hz, mul_zero, ExtractedForestParameters.localRadii,
    ForestNormalizationTelescope.localRadius, Pi.div_apply, ← he] using h

/-- Unused local leaf radii are fixed to one, matching the genuine chart convention. -/
def markedLocalRadii (k : ℕ) : tree i x → ℝ :=
  ForestLeafRadii.fixLeaves (tree i x)
    (ForestMarkedFrames.localRadii (tree i x) (frames i x) (ExtractedForestParameters.center i x k))

theorem tendsto_markedLocalRadii (v : tree i x) :
    Tendsto (fun k => markedLocalRadii i x k v) atTop (𝓝 (limitingRadii i x v)) := by
  by_cases hm : IsMax v
  · have hc := (ClusterPartitionTree.isMax_iff_card_eq_one
      (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v).mp hm
    simp [markedLocalRadii, ForestLeafRadii.fixLeaves, hm, limitingRadii, hc]
  · by_cases hv : v = ⊥
    · subst v
      have he : (fun k => markedLocalRadii i x k ⊥) =ᶠ[atTop] fun _ => (1 : ℝ) := by
        filter_upwards [eventually_positiveGaps i x] with k hk
        simp only [markedLocalRadii, ForestLeafRadii.fixLeaves, if_neg hm]
        exact ForestMarkedFrames.localRadii_root _ _ _ hk
      have hl : limitingRadii i x (⊥ : tree i x) = 1 := by simp [limitingRadii]
      rw [hl]
      exact tendsto_const_nhds.congr' he.symm
    · have hl : limitingRadii i x v = 0 := by
        simp [limitingRadii, hv, ExtractedForestIdentification.nonleaf_large i x v hm]
      simpa only [markedLocalRadii, ForestLeafRadii.fixLeaves, if_neg hm, hl,
        ForestMarkedFrames.localRadii, ForestNormalizationTelescope.localRadius,
        markedRadius] using tendsto_internal_markedRadius_ratio i x v hv hm

/-- The whole finite frame parameter sequence converges, with zero internal
corner radii and the actual normalized child-shape increments. -/
theorem tendsto_markedParameters :
    Tendsto (fun k => (markedLocalRadii i x k, markedIncrements i x k)) atTop
      (𝓝 (limitingRadii i x, limitingIncrements i x)) :=
  (tendsto_pi_nhds.mpr (tendsto_markedLocalRadii i x)).prodMk_nhds
    (tendsto_pi_nhds.mpr (tendsto_markedIncrements i x))

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameLimits
