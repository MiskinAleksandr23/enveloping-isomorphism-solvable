import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartPoint

/-! Actual normalized chart coverage: the full forward encoder of the
extracted marked chart point is the SAME original compactification point.
The proof uses the original marked parameter sequence, not decoder injectivity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartCoverage

open Configuration Filter Topology ForestDirectionRatioCoordinates
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedMarkedFrameLimits ExtractedForestNormalizedPoint ExtractedForestChartPoint
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def sequenceParameters (k : ℕ) : Parameters (tree i x) := (markedLocalRadii i x k, markedIncrements i x k)

theorem sequence_radii_pos (k : ℕ)
    (hk : ExtractedForestParameters.center i x k ∈ ForestMarkedFrames.PositiveGaps (tree i x) (frames i x))
    (v : tree i x) : 0 < (sequenceParameters i x k).1 v := by
  change 0 < ForestLeafRadii.fixLeaves (tree i x) _ v
  by_cases hv : IsMax v
  · simp [ForestLeafRadii.fixLeaves, hv]
  · simp only [ForestLeafRadii.fixLeaves, if_neg hv]
    exact ForestMarkedFrames.localRadii_pos _ _ _ hk v

theorem sequence_leaf_position (k : ℕ)
    (hk : ExtractedForestParameters.center i x k ∈ ForestMarkedFrames.PositiveGaps (tree i x) (frames i x))
    (j : DoubledLabel n m) :
    ForestInsertionDifference.position (tree i x) (sequenceParameters i x k).1 (sequenceParameters i x k).2
      (canonicalLeaf i x j) =
      (markedRadius i x k ⊥)⁻¹ • (point i x k j - markedCenter i x k ⊥) := by
  change ForestInsertionDifference.position (tree i x)
    (ForestLeafRadii.fixLeaves (tree i x) (ForestMarkedFrames.localRadii (tree i x) (frames i x)
      (ExtractedForestParameters.center i x k))) _ _ = _
  rw [← ForestLeafRadii.position_eq (tree i x) _ _ (ForestLeafRadii.fixLeaves_agree (tree i x) _)]
  have h := ForestNormalizationTelescope.position_localRadius_increment (tree i x)
    (markedRadius i x k) hk (markedCenter i x k) (canonicalLeaf i x j)
  have he : markedCenter i x k (canonicalLeaf i x j) = point i x k j := by
    rw [markedCenter, ForestMarkedFrames.center_leaf _ _ _ (canonicalLeaf_isMax i x j),
      ExtractedForestParameters.center_leaf]
  rw [he] at h
  exact h

theorem sequence_pairDifference (k : ℕ)
    (hk : ExtractedForestParameters.center i x k ∈ ForestMarkedFrames.PositiveGaps (tree i x) (frames i x))
    (p : DoubledPair n m) :
    ForestDirectionRatioCoordinates.pairDifference (tree i x) (canonicalLeaf i x) (sequenceParameters i x k) p =
      (markedRadius i x k ⊥)⁻¹ • (normalizedSequence i x ((extraction i x).subsequence k)).val.pairDifference p := by
  rw [ForestDirectionRatioCoordinates.pairDifference, sequence_leaf_position i x k hk,
    sequence_leaf_position i x k hk, ← smul_sub]
  congr 1
  change (point i x k p.val.2 - markedCenter i x k ⊥) - (point i x k p.val.1 - markedCenter i x k ⊥) =
    point i x k p.val.2 - point i x k p.val.1
  abel

/-- Every full raw coordinate of the actual marked factory agrees with the
original approximating configuration, by genuine insertion telescoping. -/
theorem raw_sequence_eq_original (k : ℕ)
    (hk : ExtractedForestParameters.center i x k ∈ ForestMarkedFrames.PositiveGaps (tree i x) (frames i x)) :
    rawCoordinates (tree i x) (canonicalLeaf i x) (sequenceParameters i x k) =
      directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val := by
  have hr : 0 < (markedRadius i x k ⊥)⁻¹ := inv_pos.mpr (hk ⊥)
  apply Prod.ext
  · funext p
    change complexPhase (ForestDirectionRatioCoordinates.pairDifference _ _ (sequenceParameters i x k) p) = _
    rw [sequence_pairDifference i x k hk, complexPhase_pos_real_smul hr]
    rfl
  · funext q
    apply Subtype.ext
    change ‖ForestDirectionRatioCoordinates.pairDifference _ _ (sequenceParameters i x k) (firstPair q)‖ /
      (‖ForestDirectionRatioCoordinates.pairDifference _ _ (sequenceParameters i x k) (firstPair q)‖ +
        ‖ForestDirectionRatioCoordinates.pairDifference _ _ (sequenceParameters i x k) (secondPair q)‖) = _
    simp only [sequence_pairDifference i x k hk, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← mul_add, mul_div_mul_left _ _ hr.ne']
    rfl

theorem limiting_admissible : Admissible (tree i x) (canonicalLeaf i x) (parameters i x) :=
  ⟨(radii_admissible i x).2.2.2, regularUnits i x⟩

/-- Genuine forward right identity for the full DR encoder, obtained from
the actual marked sequence and joint resolved-coordinate continuity. -/
theorem fullDR_eq_original : ForestChartConfigurations.fullDR (shapeData i x) (chartPoint i x) = projectDR x.val := by
  have hseq : Tendsto (sequenceParameters i x) atTop (𝓝 (parameters i x)) := tendsto_markedParameters i x
  have hevent := eventually_positiveGaps i x
  apply Prod.ext
  · funext p
    have h := (continuousAt_direction (tree i x) (canonicalLeaf i x) (parameters i x) p
      (regularUnits i x p)).tendsto.comp hseq
    have he : (fun k => direction (tree i x) (canonicalLeaf i x) (sequenceParameters i x k) p) =ᶠ[atTop]
        fun k => (directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val).1 p := by
      filter_upwards [hevent] with k hk
      rw [direction_eq_actual _ _ _ (sequence_radii_pos i x k hk)]
      exact congrFun (congrArg Prod.fst (raw_sequence_eq_original i x k hk)) p
    exact tendsto_nhds_unique (h.congr' he)
      (ReflectedForestExtraction.compactificationExtraction_directions i x p)
  · funext q
    apply Subtype.ext
    have h := (contDiffAt_ratioValue (tree i x) (canonicalLeaf i x) (parameters i x)
      (limiting_admissible i x) q).continuousAt.tendsto.comp hseq
    have he : (fun k => ratioValue (tree i x) (canonicalLeaf i x) (sequenceParameters i x k) q) =ᶠ[atTop]
        fun k => ((directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val).2 q : ℝ) := by
      filter_upwards [hevent] with k hk
      rw [ratioValue_eq_actual _ _ _ (sequence_radii_pos i x k hk)]
      exact congrArg Subtype.val (congrFun (congrArg Prod.snd (raw_sequence_eq_original i x k hk)) q)
    exact tendsto_nhds_unique (h.congr' he)
      (continuous_subtype_val.continuousAt.tendsto.comp
        (ReflectedForestExtraction.compactificationExtraction_ratios i x q))

/-- Every actual compactification point is the image of its constructed
normalized reflected forest-chart parameter point. -/
theorem compactificationInsertion_eq_original :
    ForestChartConfigurations.compactificationInsertion (shapeData i x) i (chartPoint i x) = x := by
  apply projectDR_injective_on_compactification i
  change projectDR (ForestChartConfigurations.compactificationInsertion (shapeData i x) i (chartPoint i x)).val = _
  rw [ForestChartConfigurations.compactificationInsertion_projectDR, fullDR_eq_original]

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestChartCoverage
