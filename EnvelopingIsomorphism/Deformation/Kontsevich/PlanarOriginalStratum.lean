import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarSubtreeCoordinates

/-! Original planar configurations force positivity of every internal radius
below the upper cluster, through the actual stored-DR decoder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOriginalStratum

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterRoot PlanarClusterFrames PlanarClusterDoubledData
open ForestMarkedFrames ForestDRParameterIdentification MarkedDRIdentification
open ForestDirectionRatioCoordinates InteriorFiberAngleSplit
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

/-- Each actual complex center is one of its original descendant leaf values. -/
theorem center_selects_leaf (P : tree a x → ℂ) (v : tree a x) (hv : upperNode a x hx ≤ v) :
    ∃ j : Point N, Sum.inl (Sum.inl j) ∈ v.val ∧
      ForestMarkedFrames.center (tree a x) (frames a x) v P = P (canonicalLeaf a x (Sum.inl (Sum.inl j))) := by
  induction v using WellFoundedGT.induction with
  | ind v ih =>
    by_cases hn : IsMax v
    · obtain ⟨j, _, hj⟩ := ((extraction a x).tree_leaf_iff_singleton Finset.univ
        ⟨Sum.inr a, Finset.mem_univ _⟩ v).mp hn
      have he : v = canonicalLeaf a x j := Subtype.ext hj
      have hm : j ∈ upperLabels := hv (hj ▸ Finset.mem_singleton_self j)
      rcases j with (j | j) | j
      · refine ⟨j, hj ▸ Finset.mem_singleton_self _, ?_⟩
        rw [ForestMarkedFrames.center_leaf _ _ _ hn, he]
      · exact Fin.elim0 j
      · simp at hm
    · have hv0 : v ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans_le hv)
      obtain ⟨j, hj, he⟩ := ih (ExtractedForestFrames.markedPair a x v hn).1
        (markedPair_spec a x v hn).1.lt (hv.trans (markedPair_spec a x v hn).1.le)
      refine ⟨j, (markedPair_spec a x v hn).1.le hj, ?_⟩
      rw [center_complex (tree a x) (frames a x) v _ _ hn
        (markedPair_spec a x v hn).1 (markedPair_spec a x v hn).2.1
        (markedPair_spec a x v hn).2.2 (frames_nonroot a x hx v hv0 hn)]
      exact he

theorem marked_leaves_ne (v : tree a x) (hn : ¬IsMax v) (j k : Point N)
    (hj : Sum.inl (Sum.inl j) ∈ (ExtractedForestFrames.markedPair a x v hn).1.val)
    (hk : Sum.inl (Sum.inl k) ∈ (ExtractedForestFrames.markedPair a x v hn).2.val) : j ≠ k := by
  intro he
  subst k
  have h₁ := ExtractedForestDRReferences.shape_child a x v _ hn
    (markedPair_spec a x v hn).1 _ hj
  have h₂ := ExtractedForestDRReferences.shape_child a x v _ hn
    (markedPair_spec a x v hn).2.1 _ hk
  exact canonicalIncrement_siblings_distinct a x v _ _
    (markedPair_spec a x v hn).1 (markedPair_spec a x v hn).2.1
    (markedPair_spec a x v hn).2.2 (h₁.symm.trans h₂)

/-- Nonzero marked gaps are forced by injectivity of original leaf values;
they are not assumptions on an original configuration. -/
theorem radius_pos_of_leaf_injective (P : tree a x → ℂ) (A v : tree a x)
    (hA : upperNode a x hx ≤ A) (hAv : A ≤ v) (hv : ¬IsMax v)
    (hP : ∀ j k : Point N, Sum.inl (Sum.inl j) ∈ A.val → Sum.inl (Sum.inl k) ∈ A.val →
      P (canonicalLeaf a x (Sum.inl (Sum.inl j))) = P (canonicalLeaf a x (Sum.inl (Sum.inl k))) → j = k) :
    0 < ForestMarkedFrames.radius (tree a x) (frames a x) P v := by
  have hUv := hA.trans hAv
  have hv0 : v ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans_le hUv)
  obtain ⟨j, hj, hcj⟩ := center_selects_leaf a x hx P _ (hUv.trans (markedPair_spec a x v hv).1.le)
  obtain ⟨k, hk, hck⟩ := center_selects_leaf a x hx P _ (hUv.trans (markedPair_spec a x v hv).2.1.le)
  rw [radius_nonleaf _ _ _ _ hv, frames_nonroot a x hx v hv0 hv]
  change 0 < ‖ForestMarkedFrames.center (tree a x) (frames a x) (ExtractedForestFrames.markedPair a x v hv).2 P -
    ForestMarkedFrames.center (tree a x) (frames a x) (ExtractedForestFrames.markedPair a x v hv).1 P‖
  rw [hcj, hck]
  apply norm_pos_iff.mpr
  intro he
  exact marked_leaves_ne a x v hv j k hj hk
    (hP j k (hAv ((markedPair_spec a x v hv).1.le hj))
      (hAv ((markedPair_spec a x v hv).2.1.le hk)) (sub_eq_zero.mp he).symm)

omit hx in
theorem recoverArray_upper (d : DRData (N + 2) 0) (i j k : Point N) (hij : i ≠ j) :
    recoverArray (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl j))
      (fun h => hij (Sum.inl.inj (Sum.inl.inj h))) d (Sum.inl (Sum.inl k)) =
      recoverArray i j hij (projectUpper d) k := by
  by_cases hk : k = i
  · subst k
    simp
  · have hki : (Sum.inl (Sum.inl k) : DoubledLabel (N + 2) 0) ≠ Sum.inl (Sum.inl i) :=
      fun h => hk (Sum.inl.inj (Sum.inl.inj h))
    simp only [recoverArray, dif_neg hk, dif_neg hki]
    rfl

omit hx in
theorem upper_label_eq (j : DoubledLabel (N + 2) 0) (hj : j ∈ upperLabels) :
    j = Sum.inl (Sum.inl (index j)) := by
  rcases j with (j | j) | j
  · rfl
  · exact Fin.elim0 j
  · simp at hj

theorem correction_none (A : tree a x) (hA : upperNode a x hx ≤ A) (hn : ¬IsMax A) :
    (ExtractedForestDRReferences.reference a x A hn).correction = none := by
  have hA0 : A ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans_le hA)
  simp only [ExtractedForestDRReferences.reference, if_neg (nonroot_not_fixed a x hx A hA0)]

theorem corrected_leaf_injective (A : tree a x) (hA : upperNode a x hx ≤ A) (hn : ¬IsMax A)
    (d : DRData (N + 2) 0) (z : Point N → ℂ) (hz : Function.Injective z)
    (hd : projectUpper d = ofPositions z) :
    Function.Injective (fun j : Point N =>
      (ExtractedForestDRReferences.reference a x A hn).corrected d (Sum.inl (Sum.inl j))) := by
  let i := index (ExtractedForestDRReferences.refA a x A hn)
  let k := index (ExtractedForestDRReferences.refB a x A hn)
  have hi : ExtractedForestDRReferences.refA a x A hn = Sum.inl (Sum.inl i) :=
    upper_label_eq _ (hA (ExtractedForestDRReferences.refA_mem a x A hn))
  have hk : ExtractedForestDRReferences.refB a x A hn = Sum.inl (Sum.inl k) :=
    upper_label_eq _ (hA (ExtractedForestDRReferences.refB_mem a x A hn))
  have hik : i ≠ k := by
    intro he
    exact ExtractedForestDRReferences.reference_ne a x A hn (hi.trans ((congrArg (fun j => Sum.inl (Sum.inl j)) he).trans hk.symm))
  have he (j : Point N) :
      (ExtractedForestDRReferences.reference a x A hn).corrected d (Sum.inl (Sum.inl j)) =
        (z j - z i) / (‖z k - z i‖ : ℂ) := by
    simp only [Reference.corrected, correction_none a x hx A hA hn, sub_zero]
    change recoverArray (ExtractedForestDRReferences.refA a x A hn)
      (ExtractedForestDRReferences.refB a x A hn) _ d _ = _
    simp only [hi, hk]
    exact (recoverArray_upper d i k j hik).trans (by rw [hd]; exact recoverArray_ofPositions z i k hik (hz.ne hik) j)
  intro j l hjl
  have hratio := (he j).symm.trans (hjl.trans (he l))
  apply hz
  exact sub_left_inj.mp ((div_left_inj' (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz.ne hik.symm))))).mp hratio)

theorem recovered_radius_pos (A v : tree a x) (hA : upperNode a x hx ≤ A)
    (hnA : ¬IsMax A) (hAv : A ≤ v) (hnv : ¬IsMax v) (d : DRData (N + 2) 0)
    (z : Point N → ℂ) (hz : Function.Injective z) (hd : projectUpper d = ofPositions z) :
    0 < ForestMarkedFrames.radius (tree a x) (frames a x)
      (recoveredArray (tree a x) (ExtractedForestDRReferences.lab a x) A
        (ExtractedForestDRReferences.reference a x A hnA) d) v := by
  apply radius_pos_of_leaf_injective a x hx _ A v hA hAv hnv
  intro j k hj hk he
  have hh (l : Point N) (hl : Sum.inl (Sum.inl l) ∈ A.val) :
      recoveredArray (tree a x) (ExtractedForestDRReferences.lab a x) A
        (ExtractedForestDRReferences.reference a x A hnA) d
        (canonicalLeaf a x (Sum.inl (Sum.inl l))) =
      (ExtractedForestDRReferences.reference a x A hnA).corrected d (Sum.inl (Sum.inl l)) := by
    simp only [recoveredArray, (le_canonicalLeaf_iff a x A _).mpr hl,
      canonicalLeaf_isMax, and_self, ↓reduceIte, ExtractedForestDRRegion.lab_canonicalLeaf]
  exact corrected_leaf_injective a x hx A hA hnA d z hz hd
    ((hh j hj).symm.trans (he.trans (hh k hk)))

/-- Actual decoder radii are positive below the upper cluster for every original
planar DR array. The denominator is the chart's proved positive reference gap,
and the numerator is a nonzero gap between selected original leaves. -/
theorem decoder_radius_pos (y : Compactification a 0)
    (hy : y ∈ ForestChartOpenImage.referenceRegion a x)
    (z : Point N → ℂ) (hz : Function.Injective z)
    (hd : projectUpper (projectDR y.val) = ofPositions z)
    (v : tree a x) (hUv : upperNode a x hx < v) (hnv : ¬IsMax v) :
    0 < (ForestChartOpenImage.decoder a x y).1 v := by
  have hv0 : v ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans hUv)
  have hUp : upperNode a x hx ≤ Order.pred v := Order.le_pred_of_lt hUv
  have hnp := ForestDRInverse.pred_internal (tree a x) v hv0
  change 0 < ForestDRInverse.recoveredRadii (tree a x) (ExtractedForestDRReferences.lab a x)
    (frames a x) (ExtractedForestDRReferences.reference a x) (projectDR y.val) v
  rw [ForestDRInverse.recoveredRadii, if_neg hnv, dif_neg hv0]
  apply div_pos
  · exact recovered_radius_pos a x hx (Order.pred v) v hUp hnp (Order.pred_le v) hnv
      (projectDR y.val) z hz hd
  · exact (hy (Order.pred v) hnp).2

theorem positiveBelowUpper_of_original (p : ForestChartOpenImage.Source a x)
    (hp : ForestChartOpenImage.forward a x p ∈ ForestChartOpenImage.referenceRegion a x)
    (z : Point N → ℂ) (hz : Function.Injective z)
    (hd : projectUpper (projectDR (ForestChartOpenImage.forward a x p).val) = ofPositions z) :
    PlanarSubtreeCoordinates.PositiveBelowUpper a x hx p.val := by
  intro v hv hn
  have hUv : upperNode a x hx < v.val :=
    (show (⊥ : PlanarComplexForestCharts.upperTree a x hx) < v from bot_lt_iff_ne_bot.mpr hv)
  have hnv : ¬IsMax v.val := fun h => hn ((PlanarComplexForestCharts.isMax_iff a x hx v).mpr h)
  have h := decoder_radius_pos a x hx (ForestChartOpenImage.forward a x p) hp z hz hd v.val hUv hnv
  rw [ForestChartOpenImage.decoder_forward a x p hp] at h
  exact h

variable (b : Point N) (hab : a ≠ b)

/-- The actual original planar stratum is precisely positivity below the upper
cluster in each genuine chart. The collapsed upper radius is not required positive. -/
theorem original_iff_positiveBelowUpper (p : ForestChartOpenImage.Source a x)
    (hp : ForestChartOpenImage.forward a x p ∈ ForestChartOpenImage.referenceRegion a x) :
    (∃ z : PlanarClusterCompactification.Normalized a b,
      PlanarClusterFiber.projection a b hab (ForestChartOpenImage.forward a x p) =
        PlanarClusterCompactification.embedding a b z) ↔
      PlanarSubtreeCoordinates.PositiveBelowUpper a x hx p.val := by
  constructor
  · rintro ⟨z, hz⟩
    exact positiveBelowUpper_of_original a x hx p hp z.val z.property.1 (congrArg Subtype.val hz)
  · intro h
    exact ⟨PlanarSubtreeCoordinates.normalized a x hx b hab p h,
      PlanarSubtreeCoordinates.projection_eq_normalized_embedding a x hx b hab p h⟩

theorem original_eq_normalized (p : ForestChartOpenImage.Source a x)
    (hp : ForestChartOpenImage.forward a x p ∈ ForestChartOpenImage.referenceRegion a x)
    (z : PlanarClusterCompactification.Normalized a b)
    (hz : PlanarClusterFiber.projection a b hab (ForestChartOpenImage.forward a x p) =
      PlanarClusterCompactification.embedding a b z) :
    z = PlanarSubtreeCoordinates.normalized a x hx b hab p
      ((original_iff_positiveBelowUpper a x hx b hab p hp).mp ⟨z, hz⟩) := by
  apply PlanarClusterCompactification.embedding_injective a b
  exact hz.symm.trans (PlanarSubtreeCoordinates.projection_eq_normalized_embedding a x hx b hab p _)

theorem inverse_original_positive (y : Compactification a 0) (hy : y ∈ ForestChartOpenImage.target a x)
    (z : PlanarClusterCompactification.Normalized a b)
    (hz : projectUpper (projectDR y.val) = PlanarClusterCompactification.encode a b z) :
    PlanarSubtreeCoordinates.PositiveBelowUpper a x hx
      (ForestChartOpenImage.inverse a x ⟨y, hy⟩).val := by
  apply positiveBelowUpper_of_original a x hx (ForestChartOpenImage.inverse a x ⟨y, hy⟩)
    (by rw [ForestChartOpenImage.forward_inverse]; exact hy.1) z.val z.property.1
  rw [ForestChartOpenImage.forward_inverse]
  exact hz

theorem inverse_original_normalized (y : Compactification a 0) (hy : y ∈ ForestChartOpenImage.target a x)
    (z : PlanarClusterCompactification.Normalized a b)
    (hz : projectUpper (projectDR y.val) = PlanarClusterCompactification.encode a b z) :
    z = PlanarSubtreeCoordinates.normalized a x hx b hab (ForestChartOpenImage.inverse a x ⟨y, hy⟩)
      (inverse_original_positive a x hx b y hy z hz) := by
  apply PlanarClusterCompactification.embedding_injective a b
  have h := PlanarSubtreeCoordinates.projection_eq_normalized_embedding a x hx b hab
    (ForestChartOpenImage.inverse a x ⟨y, hy⟩) (inverse_original_positive a x hx b y hy z hz)
  rw [ForestChartOpenImage.forward_inverse] at h
  have he : PlanarClusterFiber.projection a b hab y = PlanarClusterCompactification.embedding a b z :=
    Subtype.ext hz
  exact he.symm.trans h

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOriginalStratum
