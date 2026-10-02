import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterData
import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compact coordinate extension of finite real-boundary collision data

Every positive admissible scale gives a proved distinct-point configuration.
The radius-zero value is an actual limit in the compact closure. Pair directions
and triple ratios are extended explicitly after cancelling their radial factors.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Filter Topology
open scoped Topology

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- Primitive scale inequalities, retaining the collision face at scale zero. -/
structure AdmissibleScale (D : BoundaryClusterData i a m S l u) (r : ℝ) : Prop where
  nonneg : 0 ≤ r
  separation : ∀ j k, D.base j ≠ D.base k →
    r * ‖D.velocity j - D.velocity k‖ < ‖D.base j - D.base k‖
  boundary_separation : ∀ j k, j < k →
    ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) →
    r * |D.boundaryVelocity k - D.boundaryVelocity j| < D.boundaryBase k - D.boundaryBase j

theorem admissibleScale_zero (D : BoundaryClusterData i a m S l u) : D.AdmissibleScale 0 := by
  refine ⟨le_refl 0, fun j k hjk => ?_, fun j k hjk hblock => ?_⟩
  · simpa using norm_pos_iff.mpr (sub_ne_zero.mpr hjk)
  · simpa using sub_pos.mpr (D.boundaryBase_lt j k hjk hblock)

theorem IsSafeScale.admissibleScale {D : BoundaryClusterData i a m S l u} {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 ≤ r) (hrε : r ≤ ε) : D.AdmissibleScale r := by
  refine ⟨hr, fun j k hjk => ?_, fun j k hjk hblock => ?_⟩
  · exact (mul_le_mul_of_nonneg_right hrε (norm_nonneg _)).trans_lt (hε.separation j k hjk)
  · exact (mul_le_mul_of_nonneg_right hrε (abs_nonneg _)).trans_lt
      (hε.boundary_separation j k hjk hblock)

theorem AdmissibleScale.isSafeScale {D : BoundaryClusterData i a m S l u} {r : ℝ}
    (h : D.AdmissibleScale r) (hr : 0 < r) : D.IsSafeScale r :=
  ⟨hr, h.separation, h.boundary_separation⟩

def activeDifference (D : BoundaryClusterData i a m S l u) (r : ℝ) (p : DoubledPair n m) : ℂ :=
  D.pairBase p + (r : ℂ) * D.pairVelocity p

theorem activeDifference_ne_zero {D : BoundaryClusterData i a m S l u} {r : ℝ}
    (hr : D.AdmissibleScale r) (p : DoubledPair n m) (hp : D.pairBase p ≠ 0) :
    D.activeDifference r p ≠ 0 := by
  by_cases hz : r = 0
  · simpa [activeDifference, hz] using hp
  · have hpos : 0 < r := lt_of_le_of_ne hr.nonneg (Ne.symm hz)
    rw [activeDifference, ← D.normalized_pairDifference (hr.isSafeScale hpos) hpos (le_refl r)]
    exact (D.normalized (hr.isSafeScale hpos) hpos (le_refl r)).val.pairDifference_ne_zero p

/-- Compact coordinates with radial factors removed precisely from collapsing base pairs. -/
def resolvedCoordinates (D : BoundaryClusterData i a m S l u) (r : ℝ) : CompactCoordinateSpace n m :=
  ((fun v => ((D.doubledBase (Sum.inl v) + (r : ℂ) * D.doubledVelocity (Sum.inl v) : ℂ) : OnePoint ℂ)),
    (fun p => if D.pairBase p = 0 then complexPhase (D.pairVelocity p)
      else complexPhase (D.activeDifference r p)),
    (fun t =>
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      if D.pairBase p = 0 ∧ D.pairBase q = 0 then normalizedNormRatio (D.pairVelocity p) (D.pairVelocity q)
      else normalizedNormRatio (D.activeDifference r p) (D.activeDifference r q)))

theorem resolvedCoordinates_zero (D : BoundaryClusterData i a m S l u) :
    D.resolvedCoordinates 0 = linearCollisionCoordinates D.doubledBase D.doubledVelocity := by
  simp only [resolvedCoordinates, activeDifference, Complex.ofReal_zero, zero_mul, add_zero,
    linearCollisionCoordinates, linearPhaseLimit, linearRatioLimit, pairBase, pairVelocity]

theorem resolvedCoordinates_pos (D : BoundaryClusterData i a m S l u) {ε r : ℝ}
    (hε : D.IsSafeScale ε) (hr : 0 < r) (hrε : r ≤ ε) :
    D.resolvedCoordinates r = compactCoordinates (D.normalized hε hr hrε) := by
  apply Prod.ext
  · funext v
    exact congrArg ((↑) : ℂ → OnePoint ℂ) (D.normalized_doubledPoint hε hr hrε (Sum.inl v)).symm
  · apply Prod.ext
    · funext p
      change (if D.pairBase p = 0 then _ else _) =
        complexPhase ((D.normalized hε hr hrε).val.pairDifference p)
      rw [D.normalized_pairDifference]
      split_ifs with hp
      · simpa only [hp, zero_add] using (complexPhase_pos_real_mul hr (D.pairVelocity p)).symm
      · rfl
    · funext t
      let p : DoubledPair n m := ⟨(t.val.1, t.val.2.1), t.property.1⟩
      let q : DoubledPair n m := ⟨(t.val.1, t.val.2.2), t.property.2⟩
      change (if D.pairBase p = 0 ∧ D.pairBase q = 0 then _ else _) =
        normalizedNormRatio ((D.normalized hε hr hrε).val.pairDifference p)
          ((D.normalized hε hr hrε).val.pairDifference q)
      rw [D.normalized_pairDifference, D.normalized_pairDifference]
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

/-- The scale-zero coordinate is realized by an actual family in the compact closure. -/
theorem zero_mem_compactification (D : BoundaryClusterData i a m S l u) :
    D.resolvedCoordinates 0 ∈ compactificationSet i m := by
  obtain ⟨ε, hε⟩ := D.exists_safeScale
  rw [D.resolvedCoordinates_zero]
  let c : ℕ → Normalized i m := fun k =>
    D.normalized hε (shrinkingScale_pos hε.pos k) (shrinkingScale_le hε.pos k)
  apply linearCollisionCoordinates_mem_compactification c D.doubledBase D.doubledVelocity
    (tendsto_shrinkingScale ε) (Eventually.of_forall (shrinkingScale_pos hε.pos))
  intro k v
  exact D.normalized_doubledPoint _ _ _ v

theorem resolvedCoordinates_mem_compactification (D : BoundaryClusterData i a m S l u) {r : ℝ}
    (hr : D.AdmissibleScale r) : D.resolvedCoordinates r ∈ compactificationSet i m := by
  by_cases hz : r = 0
  · rw [hz]
    exact D.zero_mem_compactification
  · have hpos : 0 < r := lt_of_le_of_ne hr.nonneg (Ne.symm hz)
    rw [D.resolvedCoordinates_pos (hr.isSafeScale hpos) hpos (le_refl r)]
    exact subset_closure ⟨_, rfl⟩

def compactInsertion (D : BoundaryClusterData i a m S l u) {r : ℝ} (hr : D.AdmissibleScale r) :
    Compactification i m :=
  ⟨D.resolvedCoordinates r, D.resolvedCoordinates_mem_compactification hr⟩

theorem compactInsertion_pos (D : BoundaryClusterData i a m S l u) {r : ℝ}
    (hr : D.AdmissibleScale r) (hpos : 0 < r) :
    D.compactInsertion hr = compactificationEmbedding i
      (D.normalized (hr.isSafeScale hpos) hpos (le_refl r)) :=
  Subtype.ext (D.resolvedCoordinates_pos (hr.isSafeScale hpos) hpos (le_refl r))

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
