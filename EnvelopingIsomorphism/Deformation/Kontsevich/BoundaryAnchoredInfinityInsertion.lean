import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityData
import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual insertion of boundary-anchored infinity data

Unnormalized positive configurations converge in their full doubled-direction
and ratio coordinates after the collapsing radial factors are removed. The
limit belongs to the actual direction/ratio closure. Position identification through
the existing homeomorphism supplies the compactification normalized at the
inner anchor, including the infinity points at zero radius.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Filter Topology

namespace BoundaryAnchoredInfinityData

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

def activeDifference (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ)
    (p : DoubledPair n m) : ℂ := D.pairBase p + (r : ℂ) * D.pairVelocity p

theorem activeDifference_ne_zero {D : BoundaryAnchoredInfinityData a m l u o} {r : ℝ}
    (hr : D.AdmissibleScale r) (p : DoubledPair n m) (hp : D.pairBase p ≠ 0) :
    D.activeDifference r p ≠ 0 := by
  by_cases hz : r = 0
  · simpa [activeDifference, hz] using hp
  · have hpos : 0 < r := lt_of_le_of_ne hr.nonneg (Ne.symm hz)
    rw [activeDifference, ← D.configuration_pairDifference (hr.isSafeScale hpos) hpos (le_refl r)]
    exact (D.configuration (hr.isSafeScale hpos) hpos (le_refl r)).pairDifference_ne_zero p

/-- Every full doubled pair and every full doubled triple is retained. -/
def resolvedDR (D : BoundaryAnchoredInfinityData a m l u o) (r : ℝ) : DRData n m :=
  ((fun p => if D.pairBase p = 0 then complexPhase (D.pairVelocity p)
      else complexPhase (D.activeDifference r p)),
    (fun t =>
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      if D.pairBase p = 0 ∧ D.pairBase q = 0 then
        normalizedNormRatio (D.pairVelocity p) (D.pairVelocity q)
      else normalizedNormRatio (D.activeDifference r p) (D.activeDifference r q)))

theorem resolvedDR_zero (D : BoundaryAnchoredInfinityData a m l u o) :
    D.resolvedDR 0 = projectDR (linearCollisionCoordinates D.doubledBase D.doubledVelocity) := by
  simp only [resolvedDR, activeDifference, Complex.ofReal_zero, zero_mul, add_zero,
    projectDR, linearCollisionCoordinates, linearPhaseLimit, linearRatioLimit, pairBase, pairVelocity]

theorem resolvedDR_pos (D : BoundaryAnchoredInfinityData a m l u o) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) :
    D.resolvedDR r = directionRatioCoordinates (D.configuration hε hr hrε) := by
  apply Prod.ext
  · funext p
    change (if D.pairBase p = 0 then _ else _) =
      complexPhase ((D.configuration hε hr hrε).pairDifference p)
    rw [D.configuration_pairDifference]
    split_ifs with hp
    · simpa only [hp, zero_add] using (complexPhase_pos_real_mul hr (D.pairVelocity p)).symm
    · rfl
  · funext t
    let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
    change (if D.pairBase p = 0 ∧ D.pairBase q = 0 then _ else _) =
      normalizedNormRatio ((D.configuration hε hr hrε).pairDifference p)
        ((D.configuration hε hr hrε).pairDifference q)
    rw [D.configuration_pairDifference, D.configuration_pairDifference]
    split_ifs with hpq
    · simpa only [hpq.1, hpq.2, zero_add] using
        (normalizedNormRatio_pos_real_mul r hr (D.pairVelocity p) (D.pairVelocity q)).symm
    · rfl

private def shrinkingScale (ε : ℝ) (k : ℕ) : ℝ := ε / ((k : ℝ) + 1)

private theorem shrinkingScale_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 < shrinkingScale ε k := by
  unfold shrinkingScale
  positivity

private theorem shrinkingScale_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) : shrinkingScale ε k ≤ ε := by
  unfold shrinkingScale
  apply div_le_self hε.le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

private theorem tendsto_shrinkingScale (ε : ℝ) : Tendsto (shrinkingScale ε) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => ε / ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_const_nhds (x := ε)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The full retained DR coordinate at zero is a limit of actual distinct configurations. -/
theorem zero_mem_directionRatioSet (D : BoundaryAnchoredInfinityData a m l u o) :
    D.resolvedDR 0 ∈ directionRatioSet n m := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  let c : ℕ → Configuration n m := fun k =>
    D.configuration hε (shrinkingScale_pos hε.pos k) (shrinkingScale_le hε.pos k)
  have ht : Tendsto (fun k => directionRatioCoordinates (c k)) atTop (𝓝 (D.resolvedDR 0)) := by
    rw [D.resolvedDR_zero]
    apply Tendsto.prodMk_nhds
    · apply tendsto_pi_nhds.mpr
      intro p
      change Tendsto (fun k => complexPhase ((c k).pairDifference p)) atTop
        (𝓝 (linearPhaseLimit (D.pairBase p) (D.pairVelocity p)))
      simp only [c, D.configuration_pairDifference]
      exact tendsto_linearPhaseLimit (tendsto_shrinkingScale ε)
        (Eventually.of_forall (shrinkingScale_pos hε.pos)) _ _
    · apply tendsto_pi_nhds.mpr
      intro t
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      change Tendsto (fun k => normalizedNormRatio ((c k).pairDifference p) ((c k).pairDifference q))
        atTop (𝓝 (linearRatioLimit (D.pairBase p) (D.pairBase q) (D.pairVelocity p) (D.pairVelocity q)))
      simp only [c, D.configuration_pairDifference]
      exact tendsto_linearRatioLimit (tendsto_shrinkingScale ε)
        (Eventually.of_forall (shrinkingScale_pos hε.pos)) _ _ _ _
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall fun k => subset_closure ⟨c k, rfl⟩

theorem resolvedDR_mem_directionRatioSet (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : D.AdmissibleScale r) : D.resolvedDR r ∈ directionRatioSet n m := by
  by_cases hz : r = 0
  · rw [hz]
    exact D.zero_mem_directionRatioSet
  · have hpos : 0 < r := lt_of_le_of_ne hr.nonneg (Ne.symm hz)
    rw [D.resolvedDR_pos (hr.isSafeScale hpos) hpos (le_refl r)]
    exact subset_closure ⟨_, rfl⟩

/-- Actual compactified insertion in the inner-anchor normalization, also at radius zero. -/
def compactInsertion (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : D.AdmissibleScale r) : Compactification a m :=
  (toDRHomeomorph a).symm ⟨D.resolvedDR r, D.resolvedDR_mem_directionRatioSet hr⟩

@[simp] theorem compactInsertion_projectDR (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : D.AdmissibleScale r) : projectDR (D.compactInsertion hr).val = D.resolvedDR r := by
  exact congrArg Subtype.val ((toDRHomeomorph a).apply_symm_apply
    (⟨D.resolvedDR r, D.resolvedDR_mem_directionRatioSet hr⟩ : DRSpace n m))

theorem compactInsertion_pos (D : BoundaryAnchoredInfinityData a m l u o) {r : ℝ}
    (hr : D.AdmissibleScale r) (hpos : 0 < r) :
    D.compactInsertion hr = compactificationEmbedding a
      (D.normalized (hr.isSafeScale hpos) hpos (le_refl r)) := by
  apply projectDR_injective_on_compactification a
  change projectDR (D.compactInsertion hr).val =
    projectDR (compactificationEmbedding a (D.normalized (hr.isSafeScale hpos) hpos (le_refl r))).val
  rw [D.compactInsertion_projectDR]
  change D.resolvedDR r = normalizedDirectionRatios (D.normalized (hr.isSafeScale hpos) hpos (le_refl r))
  rw [normalized, normalizedDirectionRatios_normalized]
  exact D.resolvedDR_pos (hr.isSafeScale hpos) hpos (le_refl r)

/-- The full radial DR family is continuous on its actual closed safe-scale interval. -/
theorem continuous_resolvedDR_ofSafeScale (D : BoundaryAnchoredInfinityData a m l u o)
    {ε : ℝ} (hε : D.IsSafeScale ε) :
    Continuous (fun r : Set.Icc (0 : ℝ) ε => D.resolvedDR r.val) := by
  have hactive (p : DoubledPair n m) :
      Continuous (fun r : Set.Icc (0 : ℝ) ε => D.activeDifference r.val p) := by
    unfold activeDifference
    fun_prop
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    by_cases hp : D.pairBase p = 0
    · simpa only [resolvedDR, if_pos hp] using
        (continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ) ε => complexPhase (D.pairVelocity p)))
    · change Continuous (fun r : Set.Icc (0 : ℝ) ε => if D.pairBase p = 0 then _ else _)
      simp only [if_neg hp]
      apply continuous_iff_continuousAt.mpr
      intro r
      exact (continuousAt_complexPhase
        (activeDifference_ne_zero (hε.admissibleScale r.property.1 r.property.2) p hp)).comp
          (f := fun y : Set.Icc (0 : ℝ) ε => D.activeDifference y.val p) (x := r)
          (hactive p).continuousAt
  · apply continuous_pi
    intro t
    let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
    let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
    change Continuous (fun r : Set.Icc (0 : ℝ) ε =>
      if D.pairBase p = 0 ∧ D.pairBase q = 0 then _ else _)
    by_cases hpq : D.pairBase p = 0 ∧ D.pairBase q = 0
    · simp only [if_pos hpq]
      exact continuous_const
    · simp only [if_neg hpq]
      apply continuous_iff_continuousAt.mpr
      intro r
      have hne : ¬ (D.activeDifference r.val p = 0 ∧ D.activeDifference r.val q = 0) := by
        intro h
        by_cases hp : D.pairBase p = 0
        · exact activeDifference_ne_zero (hε.admissibleScale r.property.1 r.property.2)
            q (fun hq => hpq ⟨hp, hq⟩) h.2
        · exact activeDifference_ne_zero (hε.admissibleScale r.property.1 r.property.2) p hp h.1
      exact (continuousAt_normalizedNormRatio _ _ hne).comp
        (f := fun y : Set.Icc (0 : ℝ) ε => (D.activeDifference y.val p, D.activeDifference y.val q)) (x := r)
        ((hactive p).prodMk (hactive q)).continuousAt

theorem continuous_compactInsertion_ofSafeScale (D : BoundaryAnchoredInfinityData a m l u o)
    {ε : ℝ} (hε : D.IsSafeScale ε) :
    Continuous (fun r : Set.Icc (0 : ℝ) ε =>
      D.compactInsertion (hε.admissibleScale r.property.1 r.property.2)) :=
  (toDRHomeomorph a).symm.continuous.comp
    ((D.continuous_resolvedDR_ofSafeScale hε).subtype_mk _)

/-- One genuine boundary label already supplies a coarse anchor together with the cluster node. -/
def singleBoundaryDatum (c : Configuration.Normalized a 0) :
    BoundaryAnchoredInfinityData a 1 (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) where
  shape := c.val.interior
  boundaryBase := fun _ => 1
  boundaryVelocity := fun _ => 0
  shape_injective := c.val.interior_injective
  shape_anchor := c.property
  block_order := le_rfl
  outside_not_mem := by simp
  boundaryBase_zero_on := by simp
  boundaryBase_neg_left := by intro j hj; simp at hj
  boundaryBase_pos_right := by intro j hj; norm_num
  boundaryBase_lt := by intro j k hjk; omega
  boundaryVelocity_zero_off := by simp
  boundaryVelocity_strictMono_on := by simp
  boundaryBase_anchor := by simp [referenceSign]

theorem singleBoundaryDatum_admissibleScale (c : Configuration.Normalized a 0)
    {r : ℝ} (hr : 0 ≤ r) : (singleBoundaryDatum c).AdmissibleScale r := by
  refine ⟨hr, ?_⟩
  intro j k hjk
  omega

end BoundaryAnchoredInfinityData

end EnvelopingIsomorphism.Deformation.Kontsevich
