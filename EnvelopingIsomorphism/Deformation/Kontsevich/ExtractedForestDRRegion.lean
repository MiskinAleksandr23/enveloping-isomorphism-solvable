import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRReferences
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRInverse

/-! Every actual compactification point lies in its extracted forest's finite
open decoder region. The references and positive recovered marked radii are
proved from actual extraction, without region-membership premises. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRRegion

open Configuration Filter Topology ComplexConjugate
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedMarkedFrameLimits ExtractedForestDRReferences
open ForestDRParameterIdentification MarkedDRIdentification
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

theorem nonstable_descendant (A v : tree i x) (hs : reflection i x A ≠ A) (hAv : A ≤ v) :
    reflection i x v ≠ v := by
  intro hv
  have hd := (extraction i x).reflected_pair_disjoint Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩
    (ReflectedPartitionTree.image_univ doubledReflection doubledReflection_involutive) A hs
  obtain ⟨j, hj⟩ := node_nonempty i x v
  have hA : j ∈ A.val := hAv hj
  have hR : j ∈ (reflection i x A).val := by
    have hm := (reflection i x).monotone hAv
    rw [hv] at hm
    exact hm hj
  exact Finset.disjoint_left.mp hd hA hR

theorem complexSubtree (A : tree i x) (hs : reflection i x A ≠ A) :
    ComplexSubtree (tree i x) (frames i x) A := by
  intro v hv hAv
  exact ⟨_, _, _, _, _, frames_nonstable i x v hv (nonstable_descendant i x A v hs hAv)⟩

theorem referenceModes : ForestDRInverse.ReferenceModes (tree i x) (frames i x) (reference i x) doubledReflection := by
  intro A hA
  by_cases hs : reflection i x A = A
  · simp only [reference, if_pos hs]
  · simpa only [reference, if_neg hs] using complexSubtree i x A hs

theorem lab_canonicalLeaf (j : DoubledLabel n m) : lab i x (canonicalLeaf i x j) = j :=
  selectedLabel_leaf i x j

theorem located : ForestDRInverse.Located (tree i x) (lab i x) (reference i x) := by
  intro A hA
  have hloc (j : DoubledLabel n m) (hj : j ∈ A.val) :
      ∃ v : tree i x, A ≤ v ∧ IsMax v ∧ lab i x v = j :=
    ⟨canonicalLeaf i x j, (le_canonicalLeaf_iff i x A j).mpr hj,
      canonicalLeaf_isMax i x j, lab_canonicalLeaf i x j⟩
  exact ⟨hloc _ (refA_mem i x A hA), hloc _ (refB_mem i x A hA),
    fun c hc => hloc c (correction_mem i x A hA c hc)⟩

theorem shift_compatible (k : ℕ) (A : tree i x) (hA : ¬IsMax A) :
    CompatibleShift (tree i x) (frames i x) A ((reference i x A hA).shift (point i x k)) :=
  ForestDRInverse.compatible_of_reflection (tree i x) (frames i x) (reference i x) doubledReflection
    (referenceModes i x) (point i x k)
      ((extraction i x).input_mirror ((extraction i x).subsequence k)) A hA

theorem point_lab_leaf (k : ℕ) (v : tree i x) (hv : IsMax v) :
    point i x k (lab i x v) = ExtractedForestParameters.center i x k v := by
  have hc := (ClusterPartitionTree.isMax_iff_card_eq_one
    (hR := ⟨Sum.inr i, Finset.mem_univ _⟩) v).mp hv
  simp only [ExtractedForestParameters.center, hc, lt_self_iff_false, dif_neg not_false, lab]

theorem norm_normalized_reference (A : tree i x) (hA : ¬IsMax A) (k : ℕ) :
    ‖normalizedArray i x A k (refB i x A hA) - normalizedArray i x A k (refA i x A hA)‖ =
      ‖point i x k (refB i x A hA) - point i x k (refA i x A hA)‖ / positiveRadius i x k A := by
  simp only [normalizedArray, ← smul_sub]
  have he : (point i x k (refB i x A hA) - ExtractedForestParameters.center i x k A) -
      (point i x k (refA i x A hA) - ExtractedForestParameters.center i x k A) =
        point i x k (refB i x A hA) - point i x k (refA i x A hA) := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (positiveRadius_pos i x k A))]
  exact (div_eq_inv_mul _ _).symm

theorem recoveredRadius_sequence (A : tree i x) (hA : ¬IsMax A) (k : ℕ) :
    ForestMarkedFrames.radius (tree i x) (frames i x)
      (recoveredArray (tree i x) (lab i x) A (reference i x A hA)
        (directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val)) A =
      (markedRadius i x k A / positiveRadius i x k A) /
        ‖normalizedArray i x A k (refB i x A hA) - normalizedArray i x A k (refA i x A hA)‖ := by
  change ForestMarkedFrames.radius (tree i x) (frames i x)
      (recoveredArray (tree i x) (lab i x) A (reference i x A hA) (ofPositions (point i x k))) A = _
  rw [radius_recovered_ofPositions (tree i x) (lab i x) (frames i x) A (reference i x A hA)
    (point i x k) (ExtractedForestParameters.center i x k)
    ((point_injective i x k).ne (reference_ne i x A hA))
    (fun v _ hv => point_lab_leaf i x k v hv) (shift_compatible i x k A hA) A le_rfl hA,
    norm_normalized_reference, div_div_div_cancel_right₀ (positiveRadius_pos i x k A).ne']
  rfl

/-- Exact positive value of the recursive marked radius on the array recovered
from x. This follows by actual sequence limits and continuity, not by assuming
that the original limiting full array is injective. -/
theorem recoveredRadius_eq (A : tree i x) (hA : ¬IsMax A) :
    ForestMarkedFrames.radius (tree i x) (frames i x)
      (recoveredArray (tree i x) (lab i x) A (reference i x A hA) (projectDR x.val)) A =
        leadingRadius i x A / referenceGap i x A hA := by
  have hq := (continuousAt_recoveredArray (tree i x) (lab i x) A (reference i x A hA)
    (projectDR x.val) (mem_finiteRegion i x A hA)).tendsto.comp
      (ExtractedForestIdentification.tendsto_original_DR i x)
  have hr := (ForestMarkedFrames.continuous_radius (tree i x) (frames i x) A).continuousAt.tendsto.comp hq
  have hgap := ((tendsto_normalizedArray i x A hA _ (refB_mem i x A hA)).sub
    (tendsto_normalizedArray i x A hA _ (refA_mem i x A hA))).norm
  have hlim := (tendsto_markedRadius_ratio i x A hA).div hgap (referenceGap_pos i x A hA).ne'
  apply tendsto_nhds_unique _ hlim
  simpa only [Function.comp_def, recoveredRadius_sequence, Pi.div_def] using hr

theorem recoveredRadius_pos (A : tree i x) (hA : ¬IsMax A) :
    0 < ForestMarkedFrames.radius (tree i x) (frames i x)
      (recoveredArray (tree i x) (lab i x) A (reference i x A hA) (projectDR x.val)) A := by
  rw [recoveredRadius_eq]
  exact div_pos (ExtractedMarkedFrameLimits.leadingRadius_pos i x A) (referenceGap_pos i x A hA)

theorem recoveredArray_eq_shape (A : tree i x) (hA : ¬IsMax A) :
    recoveredArray (tree i x) (lab i x) A (reference i x A hA) (projectDR x.val) =
      fun v => if A ≤ v ∧ IsMax v then
        (shape i x A hA (lab i x v) - (reference i x A hA).shift (shape i x A hA)) /
          (referenceGap i x A hA : ℂ) else 0 := by
  funext v
  by_cases hv : A ≤ v ∧ IsMax v
  · simp only [recoveredArray, if_pos hv]
    exact corrected_eq_shape i x A hA _ (lab_mem_of_le i x A v hv.1)
  · simp only [recoveredArray, if_neg hv]

theorem mem_localRegion (A : tree i x) (hA : ¬IsMax A) :
    projectDR x.val ∈ ForestDRParameterIdentification.Region (tree i x) (lab i x) (frames i x)
      A (reference i x A hA) :=
  ⟨mem_finiteRegion i x A hA, recoveredRadius_pos i x A hA⟩

/-- Every actual compactification point belongs to the actual finite open
decoder region of its own extracted forest and constructed original-label references. -/
theorem mem_globalRegion :
    projectDR x.val ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x) :=
  mem_localRegion i x

theorem eventually_decode_original :
    ∀ᶠ k in atTop,
      ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x)
        (directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val) =
          (markedLocalRadii i x k, markedIncrements i x k) := by
  filter_upwards [eventually_positiveGaps i x] with k hk
  exact ForestDRInverse.decode_ofPositions (tree i x) (lab i x) (frames i x) (reference i x)
    (point i x k) (ExtractedForestParameters.center i x k)
    (fun A hA => (point_injective i x k).ne (reference_ne i x A hA))
    (point_lab_leaf i x k) (shift_compatible i x k) hk

/-- The actual decoder reads exactly the marked-frame limit parameters from
the original compactification point. -/
theorem decode_eq_limitingParameters :
    ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (projectDR x.val) =
      (limitingRadii i x, limitingIncrements i x) := by
  have h := (ForestDRInverse.continuousAt_decode (tree i x) (lab i x) (frames i x)
    (reference i x) (projectDR x.val) (mem_globalRegion i x)).tendsto.comp
      (ExtractedForestIdentification.tendsto_original_DR i x)
  exact tendsto_nhds_unique (h.congr' (eventually_decode_original i x)) (tendsto_markedParameters i x)

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRRegion
