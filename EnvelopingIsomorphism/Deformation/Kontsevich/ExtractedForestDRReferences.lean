import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameReflection
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRParameterIdentification

/-! Actual original-label references and finite stored-DR identification at every
node of the forest extracted from an actual compactification point. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRReferences

open Configuration Filter Topology ComplexConjugate
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestDRParameterIdentification MarkedDRIdentification
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def lab (v : tree i x) : DoubledLabel n m := (selectedLabel i x v).val

theorem lab_mem (v : tree i x) : lab i x v ∈ v.val := (selectedLabel i x v).property

theorem lab_mem_of_le (A v : tree i x) (hAv : A ≤ v) : lab i x v ∈ A.val :=
  hAv (lab_mem i x v)

def largeSubset (A : tree i x) (hA : ¬IsMax A) : SubsetNormalizedLimits.LargeSubset (DoubledLabel n m) :=
  ⟨A.val, ExtractedForestIdentification.nonleaf_large i x A hA⟩

def shape (A : tree i x) (hA : ¬IsMax A) : DoubledLabel n m → ℂ :=
  SubsetNormalizedLimits.extendedShape (extraction i x).shapes (largeSubset i x A hA)

theorem shape_child (A B : tree i x) (hA : ¬IsMax A) (hAB : A ⋖ B)
    (j : DoubledLabel n m) (hj : j ∈ B.val) : shape i x A hA j = canonicalIncrement i x B := by
  have h := increment_eq_shape_of_child (extraction i x) Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ A B hAB j hj
  exact h.symm

def refA (A : tree i x) (hA : ¬IsMax A) : DoubledLabel n m := lab i x (ExtractedForestFrames.markedPair i x A hA).1
def refB (A : tree i x) (hA : ¬IsMax A) : DoubledLabel n m := lab i x (ExtractedForestFrames.markedPair i x A hA).2

theorem refA_mem (A : tree i x) (hA : ¬IsMax A) : refA i x A hA ∈ A.val :=
  lab_mem_of_le i x _ _ (markedPair_spec i x A hA).1.le

theorem refB_mem (A : tree i x) (hA : ¬IsMax A) : refB i x A hA ∈ A.val :=
  lab_mem_of_le i x _ _ (markedPair_spec i x A hA).2.1.le

theorem reference_shape_ne (A : tree i x) (hA : ¬IsMax A) :
    shape i x A hA (refA i x A hA) ≠ shape i x A hA (refB i x A hA) := by
  unfold refA refB
  rw [shape_child i x A _ hA (markedPair_spec i x A hA).1 _ (lab_mem i x _),
    shape_child i x A _ hA (markedPair_spec i x A hA).2.1 _ (lab_mem i x _)]
  exact canonicalIncrement_siblings_distinct i x A _ _ (markedPair_spec i x A hA).1
    (markedPair_spec i x A hA).2.1 (markedPair_spec i x A hA).2.2

theorem reference_ne (A : tree i x) (hA : ¬IsMax A) : refA i x A hA ≠ refB i x A hA :=
  fun h => reference_shape_ne i x A hA (congrArg (shape i x A hA) h)

def reference (A : tree i x) (hA : ¬IsMax A) : Reference (DoubledLabel n m) where
  a := refA i x A hA
  b := refB i x A hA
  ne := reference_ne i x A hA
  correction := if reflection i x A = A then some (doubledReflection (refA i x A hA)) else none

theorem correction_mem (A : tree i x) (hA : ¬IsMax A) (c : DoubledLabel n m)
    (hc : (reference i x A hA).correction = some c) : c ∈ A.val := by
  simp only [reference] at hc
  split_ifs at hc with hs
  · have he : doubledReflection (refA i x A hA) = c := Option.some.inj hc
    rw [← he]
    have hm : doubledReflection (refA i x A hA) ∈ (reflection i x A).val :=
      Finset.mem_image.mpr ⟨_, refA_mem i x A hA, rfl⟩
    simpa only [hs] using hm

theorem outputs_subset (A : tree i x) (hA : ¬IsMax A) :
    outputs (tree i x) (lab i x) A (reference i x A hA) ⊆ A.val := by
  letI : DecidableEq (DoubledLabel n m) := Classical.decEq _
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact lab_mem_of_le i x A v (Finset.mem_filter.mp hv).2.1
  · exact correction_mem i x A hA j (Option.mem_toFinset.mp hj)

def normalizedArray (A : tree i x) (k : ℕ) : DoubledLabel n m → ℂ :=
  fun j => (positiveRadius i x k A)⁻¹ • (point i x k j - ExtractedForestParameters.center i x k A)

theorem tendsto_normalizedArray (A : tree i x) (hA : ¬IsMax A) (j : DoubledLabel n m) (hj : j ∈ A.val) :
    Tendsto (fun k => normalizedArray i x A k j) atTop (𝓝 (shape i x A hA j)) := by
  have hh := ((continuous_apply (⟨j, hj⟩ : (largeSubset i x A hA).val)).tendsto
    ((extraction i x).shapes (largeSubset i x A hA))).comp ((extraction i x).limits (largeSubset i x A hA))
  simpa only [Function.comp_def, ReflectedSubsetNormalization.normalizedOn_apply, normalizedArray,
    positiveRadius, ExtractedForestParameters.center,
    dif_pos (ExtractedForestIdentification.nonleaf_large i x A hA), shape,
    SubsetNormalizedLimits.extendedShape, dif_pos hj, largeSubset, point] using hh

private theorem ofPositions_normalize {I : Type*} (p : I → ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ofPositions (fun j => r⁻¹ • (p j - z)) = ofPositions p := by
  have hd (a b : I) : r⁻¹ • (p b - z) - r⁻¹ • (p a - z) = r⁻¹ • (p b - p a) := by
    rw [← smul_sub]
    congr 1
    abel
  apply Prod.ext
  · funext q
    exact (congrArg complexPhase (hd q.val.1 q.val.2)).trans
      (complexPhase_pos_real_smul (inv_pos.mpr hr) _)
  · funext q
    apply Subtype.ext
    change ‖_‖ / (‖_‖ + ‖_‖) = _
    rw [hd, hd]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [← mul_add, mul_div_mul_left _ _ (inv_pos.mpr hr).ne']
    rfl

theorem normalizedArray_DR (A : tree i x) (k : ℕ) :
    ofPositions (normalizedArray i x A k) =
      directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val :=
  ofPositions_normalize (point i x k) _ (positiveRadius_pos i x k A) _

def referenceGap (A : tree i x) (hA : ¬IsMax A) : ℝ :=
  ‖shape i x A hA (refB i x A hA) - shape i x A hA (refA i x A hA)‖

theorem referenceGap_pos (A : tree i x) (hA : ¬IsMax A) : 0 < referenceGap i x A hA :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (reference_shape_ne i x A hA).symm)

theorem stored_ratio_eq (A : tree i x) (hA : ¬IsMax A) (j : DoubledLabel n m) (hj : j ∈ A.val)
    (hja : j ≠ refA i x A hA) :
    (projectDR x.val |>.2 (markedTriple (refA i x A hA) j (refB i x A hA) hja.symm (reference_ne i x A hA)) : ℝ) =
      ‖shape i x A hA j - shape i x A hA (refA i x A hA)‖ /
        (‖shape i x A hA j - shape i x A hA (refA i x A hA)‖ + referenceGap i x A hA) := by
  have ha := tendsto_normalizedArray i x A hA _ (refA_mem i x A hA)
  have hb := tendsto_normalizedArray i x A hA _ (refB_mem i x A hA)
  have hh := tendsto_normalizedArray i x A hA j hj
  have hg := ((hh.sub ha).norm).div (((hh.sub ha).norm).add ((hb.sub ha).norm))
    (ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) (referenceGap_pos i x A hA)))
  let q := markedTriple (refA i x A hA) j (refB i x A hA) hja.symm (reference_ne i x A hA)
  have ho := continuous_subtype_val.continuousAt.tendsto.comp
    (ReflectedForestExtraction.compactificationExtraction_ratios i x q)
  have he (k : ℕ) :
      ((directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val).2 q : ℝ) =
        ‖normalizedArray i x A k j - normalizedArray i x A k (refA i x A hA)‖ /
          (‖normalizedArray i x A k j - normalizedArray i x A k (refA i x A hA)‖ +
            ‖normalizedArray i x A k (refB i x A hA) - normalizedArray i x A k (refA i x A hA)‖) := by
    rw [← normalizedArray_DR i x A k]
    rfl
  apply tendsto_nhds_unique _ hg
  simpa only [Function.comp_def, Pi.div_def, ← he, directionRatioCoordinates,
    projectDR, q, extraction] using ho

theorem stored_ratio_lt_one (A : tree i x) (hA : ¬IsMax A) (j : DoubledLabel n m) (hj : j ∈ A.val)
    (hja : j ≠ refA i x A hA) :
    (projectDR x.val |>.2 (markedTriple (refA i x A hA) j (refB i x A hA) hja.symm (reference_ne i x A hA)) : ℝ) < 1 := by
  rw [stored_ratio_eq i x A hA j hj hja]
  have hg := referenceGap_pos i x A hA
  exact (div_lt_one (add_pos_of_nonneg_of_pos (norm_nonneg _) hg)).mpr (lt_add_of_pos_right _ hg)

theorem mem_finiteRegion (A : tree i x) (hA : ¬IsMax A) :
    projectDR x.val ∈ ForestDRParameterIdentification.FiniteRegion (tree i x) (lab i x) A (reference i x A hA) := by
  intro j hja
  exact stored_ratio_lt_one i x A hA j.val (outputs_subset i x A hA j.property) hja

theorem normalizedArray_injective (A : tree i x) (k : ℕ) : Function.Injective (normalizedArray i x A k) := by
  intro a b hab
  apply point_injective i x k
  have h := congrArg (fun z : ℂ => positiveRadius i x k A • z) hab
  simpa only [normalizedArray, smul_smul, mul_inv_cancel₀ (positiveRadius_pos i x k A).ne',
    one_smul, sub_left_inj] using h

/-- The stored identification array at x is the actual finite normalized shape
limit, even when the output label shares its reference anchor's child fiber. -/
theorem recoverArray_eq_shape (A : tree i x) (hA : ¬IsMax A) (j : DoubledLabel n m) (hj : j ∈ A.val) :
    recoverArray (refA i x A hA) (refB i x A hA) (reference_ne i x A hA) (projectDR x.val) j =
      (shape i x A hA j - shape i x A hA (refA i x A hA)) / (referenceGap i x A hA : ℂ) := by
  have ha := tendsto_normalizedArray i x A hA _ (refA_mem i x A hA)
  have hb := tendsto_normalizedArray i x A hA _ (refB_mem i x A hA)
  have hh := tendsto_normalizedArray i x A hA j hj
  have hlim := (hh.sub ha).div (Complex.continuous_ofReal.continuousAt.tendsto.comp (hb.sub ha).norm)
    (Complex.ofReal_ne_zero.mpr (referenceGap_pos i x A hA).ne')
  have hr := (continuousAt_recoverArray (refA i x A hA) (refB i x A hA)
    (reference_ne i x A hA) j (projectDR x.val) (stored_ratio_lt_one i x A hA j hj)).tendsto.comp
      (ExtractedForestIdentification.tendsto_original_DR i x)
  have he (k : ℕ) : recoverArray (refA i x A hA) (refB i x A hA) (reference_ne i x A hA)
      (directionRatioCoordinates (normalizedSequence i x ((extraction i x).subsequence k)).val) j =
        (normalizedArray i x A k j - normalizedArray i x A k (refA i x A hA)) /
          (‖normalizedArray i x A k (refB i x A hA) - normalizedArray i x A k (refA i x A hA)‖ : ℂ) := by
    rw [← normalizedArray_DR i x A k]
    exact recoverArray_ofPositions _ _ _ _ ((normalizedArray_injective i x A k).ne (reference_ne i x A hA)) j
  apply tendsto_nhds_unique _ hlim
  simpa only [Function.comp_def, he, Pi.div_def] using hr

/-- Stable references include their actual reflected anchor in the correction;
the recovered leaf shape has exactly the corresponding affine center. -/
theorem corrected_eq_shape (A : tree i x) (hA : ¬IsMax A) (j : DoubledLabel n m) (hj : j ∈ A.val) :
    (reference i x A hA).corrected (projectDR x.val) j =
      (shape i x A hA j - (reference i x A hA).shift (shape i x A hA)) /
        (referenceGap i x A hA : ℂ) := by
  unfold Reference.corrected Reference.shift
  cases hc : (reference i x A hA).correction with
  | none => simpa only [sub_zero, reference] using recoverArray_eq_shape i x A hA j hj
  | some c =>
    change recoverArray _ _ _ _ j - recoverArray _ _ _ _ c / 2 = _
    dsimp only [reference]
    rw [recoverArray_eq_shape i x A hA j hj,
      recoverArray_eq_shape i x A hA c (correction_mem i x A hA c hc)]
    ring

theorem shape_reflection_stable (A : tree i x) (hA : ¬IsMax A) (hs : reflection i x A = A)
    (j : DoubledLabel n m) (hj : j ∈ A.val) :
    shape i x A hA (doubledReflection j) = conj (shape i x A hA j) := by
  have hrj : doubledReflection j ∈ A.val := by
    have hm : doubledReflection j ∈ (reflection i x A).val := Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa only [hs] using hm
  have he (k : ℕ) : normalizedArray i x A k (doubledReflection j) = conj (normalizedArray i x A k j) := by
    have hc := ExtractedMarkedFrameLimits.center_real_of_stable i x k A hA hs
    have hc' : conj (ExtractedForestParameters.center i x k A) = ExtractedForestParameters.center i x k A := by
      rw [← hc]
      simp only [ForestMarkedFrames.realPart_apply, Complex.conj_ofReal]
    have hp := (extraction i x).input_mirror ((extraction i x).subsequence k) j
    change point i x k (doubledReflection j) = conj (point i x k j) at hp
    simp only [normalizedArray, hp, Complex.real_smul, map_mul, map_sub, Complex.conj_ofReal, hc']
  have h := Complex.continuous_conj.continuousAt.tendsto.comp (tendsto_normalizedArray i x A hA j hj)
  apply tendsto_nhds_unique (tendsto_normalizedArray i x A hA _ hrj)
  simpa only [Function.comp_def, ← he] using h

theorem shift_shape_stable (A : tree i x) (hA : ¬IsMax A) (hs : reflection i x A = A) :
    (reference i x A hA).shift (shape i x A hA) = ((shape i x A hA (refA i x A hA)).re : ℂ) := by
  apply Reference.shift_stable _ _ (doubledReflection (refA i x A hA))
  · simp only [reference, if_pos hs]
  · exact shape_reflection_stable i x A hA hs _ (refA_mem i x A hA)

theorem corrected_eq_real_shape (A : tree i x) (hA : ¬IsMax A) (hs : reflection i x A = A)
    (j : DoubledLabel n m) (hj : j ∈ A.val) :
    (reference i x A hA).corrected (projectDR x.val) j =
      (shape i x A hA j - ((shape i x A hA (refA i x A hA)).re : ℂ)) /
        (referenceGap i x A hA : ℂ) := by
  rw [corrected_eq_shape, shift_shape_stable i x A hA hs]
  exact hj

theorem corrected_eq_complex_shape (A : tree i x) (hA : ¬IsMax A) (hs : reflection i x A ≠ A)
    (j : DoubledLabel n m) (hj : j ∈ A.val) :
    (reference i x A hA).corrected (projectDR x.val) j =
      (shape i x A hA j - shape i x A hA (refA i x A hA)) /
        (referenceGap i x A hA : ℂ) := by
  rw [corrected_eq_shape i x A hA j hj]
  simp only [Reference.shift, reference, if_neg hs]

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDRReferences
