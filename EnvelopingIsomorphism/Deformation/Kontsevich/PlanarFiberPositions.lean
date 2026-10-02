import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterFrames
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOpenImage

/-! The planar collision equation in genuine normalized forest parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarFiberPositions

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterRoot PlanarClusterFrames ForestInsertionDifference ForestNormalizationTelescope AncestorScaleRatios
open Filter Topology
open scoped Classical

variable {q : ℕ} (a : Fin q) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

abbrev Parameters := ForestChartOpenImage.ParameterSpace a x

def pos (p : Parameters a x) (v : tree a x) : ℂ := position (tree a x) p.val.1 p.val.2 v

theorem upper_scale (p : Parameters a x) :
    scale p.val.1 (upperNode a x hx) = p.val.1 (upperNode a x hx) := by
  rw [scale_step (tree a x) _ _ (ne_of_gt (root_covBy_upper a x hx).lt),
    (root_covBy_upper a x hx).pred_eq, scale_root, p.property.1.1, mul_one]

theorem upper_increment (p : Parameters a x) : p.val.2 (upperNode a x hx) = Complex.I := by
  have hn := p.property.2.1 ⊥ (not_isMax_of_lt (root_covBy_upper a x hx).lt)
  rw [frames_root a x hx] at hn
  exact hn.1

theorem upper_position (p : Parameters a x) : pos a x p (upperNode a x hx) = Complex.I := by
  rw [pos, ForestMarkedFrameInverse.position_child _ _ _ _ _ (root_covBy_upper a x hx),
    scale_root, p.property.1.1, upper_increment a x hx p, one_smul, position_root, add_zero]

theorem leaf_position_of_radius_zero (p : Parameters a x)
    (hp : p.val.1 (upperNode a x hx) = 0) (j : Fin q) :
    pos a x p (canonicalLeaf a x (Sum.inl (Sum.inl j))) = Complex.I := by
  change position (tree a x) p.val.1 p.val.2 _ = _
  rw [position_factor_from_ancestor (tree a x) _ _ (upper_le_leaf a x hx j),
    upper_scale a x hx p, hp, zero_smul, add_zero]
  exact upper_position a x hx p

/-- A complex normalized subtree always retains a leaf at its own cumulative center,
even when any of its radial parameters vanish. -/
theorem position_eq_leaf (p : Parameters a x) (v : tree a x) (hv : upperNode a x hx ≤ v) :
    ∃ j : Fin q, pos a x p v = pos a x p (canonicalLeaf a x (Sum.inl (Sum.inl j))) := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hn : IsMax v
    · obtain ⟨j, _, hj⟩ := ((extraction a x).tree_leaf_iff_singleton Finset.univ
        ⟨Sum.inr a, Finset.mem_univ _⟩ v).mp hn
      have he : v = canonicalLeaf a x j := Subtype.ext hj
      have hm : j ∈ upperLabels := hv (hj ▸ Finset.mem_singleton_self j)
      rcases j with (j | j) | j
      · exact ⟨j, congrArg (pos a x p) he⟩
      · exact Fin.elim0 j
      · simp at hm
    · have hv0 : v ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans_le hv)
      have hf := frames_nonroot a x hx v hv0 hn
      have hnorm := p.property.2.1 v hn
      rw [hf] at hnorm
      obtain ⟨j, hj⟩ := ih (markedPair a x v hn).1 (markedPair_spec a x v hn).1.lt
        (hv.trans (markedPair_spec a x v hn).1.le)
      refine ⟨j, ?_⟩
      have he : pos a x p (markedPair a x v hn).1 = pos a x p v := by
        rw [pos, ForestMarkedFrameInverse.position_child _ _ _ _ _ (markedPair_spec a x v hn).1,
          hnorm.1, smul_zero, zero_add]
        rfl
      exact he.symm.trans hj

theorem radius_zero_of_leaf_positions_eq (b : Fin q) (hab : a ≠ b) (p : Parameters a x)
    (z : ℂ) (hp : ∀ j : Fin q, pos a x p (canonicalLeaf a x (Sum.inl (Sum.inl j))) = z) :
    p.val.1 (upperNode a x hx) = 0 := by
  let u := upperNode a x hx
  have hn : ¬IsMax u := upper_nonleaf a x hx b hab
  have hu0 : u ≠ ⊥ := ne_of_gt (root_covBy_upper a x hx).lt
  have hnorm := p.property.2.1 u hn
  rw [frames_nonroot a x hx u hu0 hn] at hnorm
  have hpos (v : tree a x) (hv : u ≤ v) : pos a x p v = z := by
    obtain ⟨j, hj⟩ := position_eq_leaf a x hx p v hv
    exact hj.trans (hp j)
  have he := ForestMarkedFrameInverse.position_child (tree a x) p.val.1 p.val.2 u
    (markedPair a x u hn).2 (markedPair_spec a x u hn).2.1
  change pos a x p (markedPair a x u hn).2 = scale p.val.1 u • p.val.2 (markedPair a x u hn).2 +
    pos a x p u at he
  rw [hpos _ (markedPair_spec a x u hn).2.1.le, hpos _ le_rfl] at he
  have hz : scale p.val.1 u • p.val.2 (markedPair a x u hn).2 = 0 := by
    exact add_right_cancel (he.symm.trans (zero_add z).symm)
  have hh := congrArg norm hz
  rw [norm_smul, hnorm.2, mul_one, norm_zero, norm_eq_zero] at hh
  exact (upper_scale a x hx p).symm.trans hh

/-- The collision condition is exactly one native radial equation; all deeper
parameters remain unrestricted. -/
theorem all_upper_positions_iff (b : Fin q) (hab : a ≠ b) (p : Parameters a x) :
    (∀ j : Fin q, pos a x p (canonicalLeaf a x (Sum.inl (Sum.inl j))) = Complex.I) ↔
      p.val.1 (upperNode a x hx) = 0 :=
  ⟨radius_zero_of_leaf_positions_eq a x hx b hab p Complex.I,
    fun h => leaf_position_of_radius_zero a x hx p h⟩

include hx

theorem cross_inf_root (j : Fin q) :
    canonicalLeaf a x (Sum.inl (Sum.inl j)) ⊓ canonicalLeaf a x (Sum.inr j) = ⊥ := by
  by_contra h
  rcases nonroot_below_branch a x hx _ h with hu | hl
  · have he := hu.trans inf_le_right
    rw [le_canonicalLeaf_iff] at he
    simp at he
  · have he := hl.trans inf_le_left
    rw [le_canonicalLeaf_iff] at he
    simp at he

theorem upper_position_im_pos (p : ForestChartOpenImage.Source a x) (j : Fin q) :
    0 < (pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl j)))).im := by
  have he := position_sub_position (tree a x) p.val.val.1 p.val.val.2
    (canonicalLeaf a x (Sum.inl (Sum.inl j))) (canonicalLeaf a x (Sum.inr j))
  rw [cross_inf_root a x hx j, scale_root, p.val.property.1.1, one_smul] at he
  have hr := ReflectedForestInsertion.position_reflect (tree a x) (reflection a x) p.val.val.1
    p.val.property.1.2.2.1 p.val.val.2 p.val.property.2.2.1
    (canonicalLeaf a x (Sum.inl (Sum.inl j)))
  rw [canonicalLeaf_reflect] at hr
  change position (tree a x) p.val.val.1 p.val.val.2 (canonicalLeaf a x (Sum.inr j)) = _ at hr
  rw [hr] at he
  have hi := congrArg Complex.im he
  have hp := p.property.2.1 j
  change 0 < (unitDifference (tree a x) p.val.val.1 p.val.val.2
    (canonicalLeaf a x (Sum.inl (Sum.inl j))) (canonicalLeaf a x (Sum.inr j))).im at hp
  change 0 < (position (tree a x) p.val.val.1 p.val.val.2 _).im
  simp only [Complex.sub_im, Complex.conj_im] at hi
  linarith

def affineNormalize (z w : ℂ) : ℂ := (z.im⁻¹ : ℂ) * w + (-z.re / z.im : ℝ)

omit hx in
theorem continuousAt_affineNormalize (z w : ℂ) (hz : z.im ≠ 0) :
    ContinuousAt (fun v : ℂ × ℂ => affineNormalize v.1 v.2) (z, w) := by
  have hi : ContinuousAt (fun v : ℂ × ℂ => (v.1.im : ℂ)) (z, w) := by fun_prop
  have hr : ContinuousAt (fun v : ℂ × ℂ => (-v.1.re / v.1.im : ℝ)) (z, w) :=
    ((Complex.continuous_re.continuousAt.comp continuous_fst.continuousAt).neg).div
      (Complex.continuous_im.continuousAt.comp continuous_fst.continuousAt) hz
  exact ((hi.inv₀ (Complex.ofReal_ne_zero.mpr hz)).mul continuous_snd.continuousAt).add
    (Complex.continuous_ofReal.continuousAt.comp hr)

omit hx in
theorem normalized_interior_formula (c : Configuration q 0) (j : Fin q) :
    ((Configuration.normalized a c).val.interior j : ℂ) =
      affineNormalize (c.interior a : ℂ) (c.interior j : ℂ) := by
  change ((normalizer a c).onUpper (c.interior j) : ℂ) = _
  rw [PositiveAffine.coe_onUpper]
  simp only [normalizer, affineNormalize, Complex.ofReal_inv]
  rfl

/-- The finite-position formula is obtained from the genuine positive approximants
of this corner, not postulated as an extra encoder law. -/
theorem forward_position (p : ForestChartOpenImage.Source a x) (j : Fin q) :
    (ForestChartOpenImage.forward a x p).val.1 (Sum.inl j) =
      (affineNormalize (pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl a))))
        (pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl j)))) : OnePoint ℂ) := by
  let D := shapeData a x
  let c := ForestChartOpenImage.toCorner a x p
  have hseq := ForestChartConfigurations.tendsto_normalized_approximatingConfiguration D a c
  have hstored := (((continuous_apply (Sum.inl j)).comp continuous_fst).comp
    continuous_subtype_val).continuousAt.tendsto.comp hseq
  have hpos (k : Fin q) : Tendsto
      (fun l => ((ForestChartConfigurations.approximatingConfiguration D c l).interior k : ℂ))
      atTop (𝓝 (pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl k))))) := by
    exact (contDiff_position (tree a x) (canonicalLeaf a x (Sum.inl (Sum.inl k)))).continuous.continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp
        (ForestChartConfigurations.tendsto_positiveApproximation D c))
  have hn := (continuousAt_affineNormalize _ _ (upper_position_im_pos a x hx p a).ne').tendsto.comp
    ((hpos a).prodMk_nhds (hpos j))
  have hc := OnePoint.continuous_coe.continuousAt.tendsto.comp hn
  apply tendsto_nhds_unique hstored
  convert hc using 1
  funext l
  change (((Configuration.normalized a (ForestChartConfigurations.approximatingConfiguration D c l)).val.interior j : ℂ) : OnePoint ℂ) = _
  rw [normalized_interior_formula]
  rfl

omit hx in
theorem affineNormalize_eq_iff (z w v : ℂ) (hz : z.im ≠ 0) :
    affineNormalize z w = affineNormalize z v ↔ w = v := by
  simp only [affineNormalize, add_left_inj]
  exact mul_right_inj' (inv_ne_zero (Complex.ofReal_ne_zero.mpr hz))

omit hx in
theorem affineNormalize_self (z : ℂ) (hz : z.im ≠ 0) : affineNormalize z z = Complex.I := by
  (apply Complex.ext <;> simp [affineNormalize, hz, div_eq_mul_inv]); ring

/-- Exact planar fiber predicate for the genuine forward chart, including its
boundary points and all of the stored compactified positions. -/
theorem forward_isFiber_iff (b : Fin q) (hab : a ≠ b) (p : ForestChartOpenImage.Source a x) :
    PlanarClusterFiber.IsFiber a (ForestChartOpenImage.forward a x p) ↔
      p.val.val.1 (upperNode a x hx) = 0 := by
  let za := pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl a)))
  have ha : za.im ≠ 0 := (upper_position_im_pos a x hx p a).ne'
  constructor
  · intro hf
    apply radius_zero_of_leaf_positions_eq a x hx b hab p.val za
    intro j
    have h := hf j
    rw [forward_position a x hx p j] at h
    have hj : affineNormalize za (pos a x p.val (canonicalLeaf a x (Sum.inl (Sum.inl j)))) = Complex.I :=
      OnePoint.coe_injective h
    apply (affineNormalize_eq_iff _ _ _ ha).mp
    exact hj.trans (affineNormalize_self za ha).symm
  · intro hr j
    rw [forward_position a x hx p j, leaf_position_of_radius_zero a x hx p.val hr a,
      leaf_position_of_radius_zero a x hx p.val hr j, affineNormalize_self _ (by simp)]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarFiberPositions
