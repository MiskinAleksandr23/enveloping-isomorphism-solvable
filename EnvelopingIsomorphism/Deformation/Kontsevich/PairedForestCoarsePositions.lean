import EnvelopingIsomorphism.Deformation.Kontsevich.ActualPairedForestPlanarFactor

/-! Native coarse positions on an actual paired forest face. All heights and
pair separation follow from the actual radius zero locus and resolved units. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoarsePositions

open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference AncestorScaleRatios ComplexConjugate ReflectedRadiusCoordinates
open BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)

abbrev node := (upperNode 0 x o ho).val
abbrev labelsSet := ActualPairedForestPlanarFactor.labelsSet x o ho

variable (z : ForestRadialFaceLocalization.source hdim x o)

def sourcePoint : ForestChartOpenImage.Source 0 x :=
  ForestOrthantRealization.sourcePoint 0 x
    (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val)) z.property.2

def parameters : ForestDirectionRatioCoordinates.Parameters (tree 0 x) :=
  realization 0 x (faceAmbient hdim x o z.val)

theorem sourcePoint_parameters : (sourcePoint hdim x o z).val.val = parameters hdim x o z := by
  change (parameterPoint 0 x
    (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val))).val = _
  unfold parameterPoint
  rw [← realization_eq_model, ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x
    (faceAmbient hdim x o z.val)
    (ForestRadialFaceLocalization.faceAmbient_nonneg hdim x o z.val z.property.1)]
  rfl

theorem radius_nonneg (v : tree 0 x) : 0 ≤ (parameters hdim x o z).1 v := by
  rw [← sourcePoint_parameters]
  exact (sourcePoint hdim x o z).val.property.1.2.2.2 v

theorem openConditions : ForestChartConfigurations.OpenConditions (shapeData 0 x)
    (parameters hdim x o z) := by
  rw [← sourcePoint_parameters]
  exact (sourcePoint hdim x o z).property

theorem radius_reflect (v : tree 0 x) :
    (parameters hdim x o z).1 (reflection 0 x v) = (parameters hdim x o z).1 v :=
  radiusArray_reflection 0 x _ v

theorem increment_reflect (v : tree 0 x) :
    (parameters hdim x o z).2 (reflection 0 x v) = conj ((parameters hdim x o z).2 v) := by
  rw [← sourcePoint_parameters]
  exact (sourcePoint hdim x o z).val.property.2.2.1 v

/-- Precisely the selected upper node and its mirror have zero native radius. -/
theorem radius_zero_iff (v : tree 0 x) :
    (parameters hdim x o z).1 v = 0 ↔ v = node x o ho ∨ v = reflection 0 x (node x o ho) := by
  change radiusArray 0 x (faceAmbient hdim x o z.val) v = 0 ↔ _
  rw [radiusArray_face_zero_iff hdim x o z.val z.property.1 v]
  constructor
  · rintro ⟨hv, he⟩
    have h := (orbitClass_eq_iff (tree 0 x) (reflection 0 x) (reflection_reflection 0 x)
      (upperNode 0 x o ho) ⟨v, hv⟩).mp ((upperNode_spec 0 x o ho).1.trans he.symm)
    rcases h with h | h
    · exact Or.inl (congrArg Subtype.val h).symm
    · exact Or.inr (congrArg Subtype.val h).symm
  · rintro (rfl | rfl)
    · exact ⟨(upperNode 0 x o ho).property, (upperNode_spec 0 x o ho).1⟩
    · exact ⟨(ReflectedRadiusCoordinates.active_reflect_iff (tree 0 x) (reflection 0 x) _).mpr
        (upperNode 0 x o ho).property,
        (ReflectedRadiusCoordinates.orbitClass_reflect (tree 0 x) (reflection 0 x)
          (reflection_reflection 0 x) (upperNode 0 x o ho)).trans (upperNode_spec 0 x o ho).1⟩

theorem radius_pos_of_ne (v : tree 0 x) (hv : v ≠ node x o ho)
    (hrv : v ≠ reflection 0 x (node x o ho)) : 0 < (parameters hdim x o z).1 v :=
  lt_of_le_of_ne (radius_nonneg hdim x o z v)
    (Ne.symm fun h => ((radius_zero_iff hdim x o ho z v).mp h).elim hv hrv)

theorem scale_zero_iff (v : tree 0 x) :
    scale (parameters hdim x o z).1 v = 0 ↔ node x o ho ≤ v ∨ reflection 0 x (node x o ho) ≤ v := by
  simp only [scale, Finset.prod_eq_zero_iff, mem_ancestors, radius_zero_iff hdim x o ho z]
  constructor
  · rintro ⟨u, huv, rfl | rfl⟩
    · exact Or.inl huv
    · exact Or.inr huv
  · rintro (h | h)
    · exact ⟨node x o ho, h, Or.inl rfl⟩
    · exact ⟨reflection 0 x (node x o ho), h, Or.inr rfl⟩

theorem scale_pos_of_not_le (v : tree 0 x) (hv : ¬node x o ho ≤ v)
    (hrv : ¬reflection 0 x (node x o ho) ≤ v) : 0 < scale (parameters hdim x o z).1 v := by
  apply Finset.prod_pos
  intro u hu
  have huv := (mem_ancestors u v).mp hu
  exact radius_pos_of_ne hdim x o ho z u (fun h => hv (h ▸ huv)) (fun h => hrv (h ▸ huv))

theorem node_not_mirror (j : Fin (n + 1)) : Sum.inr j ∉ (node x o ho).val := by
  intro h
  obtain ⟨k, hk⟩ := (upperNode_spec 0 x o ho).2 _ h
  cases hk

theorem node_not_boundary (j : Fin m) : Sum.inl (Sum.inr j) ∉ (node x o ho).val := by
  intro h
  obtain ⟨k, hk⟩ := (upperNode_spec 0 x o ho).2 _ h
  cases Sum.inl.inj hk

theorem reflected_not_upper (j : Fin (n + 1)) :
    Sum.inl (Sum.inl j) ∉ (reflection 0 x (node x o ho)).val := by
  rw [mem_reflection_iff]
  exact node_not_mirror x o ho j

theorem reflected_not_boundary (j : Fin m) :
    Sum.inl (Sum.inr j) ∉ (reflection 0 x (node x o ho)).val := by
  rw [mem_reflection_iff]
  exact node_not_boundary x o ho j

/-- Unnormalized coarse positions retain every original label; only the
selected cluster labels can have equal positions. -/
def positions (a : DoubledLabel (n + 1) m) : ℂ :=
  position (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2 (canonicalLeaf 0 x a)

theorem positions_reflect (a : DoubledLabel (n + 1) m) :
    positions hdim x o z (doubledReflection a) = conj (positions hdim x o z a) :=
  ForestChartConfigurations.positions_reflect (shapeData 0 x) _
    (radius_reflect hdim x o z) (increment_reflect hdim x o z) a

theorem positions_sub (a b : DoubledLabel (n + 1) m) :
    positions hdim x o z a - positions hdim x o z b =
      scale (parameters hdim x o z).1 (canonicalLeaf 0 x a ⊓ canonicalLeaf 0 x b) •
        unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
          (canonicalLeaf 0 x a) (canonicalLeaf 0 x b) :=
  position_sub_position (tree 0 x) _ _ _ _

include ho in
theorem positions_upper_im_pos (j : Fin (n + 1)) :
    0 < (positions hdim x o z (Sum.inl (Sum.inl j))).im := by
  have hc : 0 < scale (parameters hdim x o z).1
      (canonicalLeaf 0 x (Sum.inl (Sum.inl j)) ⊓ canonicalLeaf 0 x (Sum.inr j)) := by
    apply scale_pos_of_not_le hdim x o ho z
    · intro h
      exact node_not_mirror x o ho j ((le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_right))
    · intro h
      exact reflected_not_upper x o ho j ((le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_left))
  have hp := (openConditions hdim x o z).2.1 j
  change 0 < (unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inl j))) (canonicalLeaf 0 x (Sum.inr j))).im at hp
  have h := congrArg Complex.im (positions_sub hdim x o z (Sum.inl (Sum.inl j)) (Sum.inr j))
  have href := positions_reflect hdim x o z (Sum.inl (Sum.inl j))
  change positions hdim x o z (Sum.inr j) = conj (positions hdim x o z (Sum.inl (Sum.inl j))) at href
  rw [href] at h
  simp only [Complex.sub_im, Complex.conj_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
  have := mul_pos hc hp
  linarith

include ho in
theorem positions_boundary_strictMono :
    StrictMono (fun j : Fin m => (positions hdim x o z (Sum.inl (Sum.inr j))).re) := by
  intro j k hjk
  have hc : 0 < scale (parameters hdim x o z).1
      (canonicalLeaf 0 x (Sum.inl (Sum.inr k)) ⊓ canonicalLeaf 0 x (Sum.inl (Sum.inr j))) := by
    apply scale_pos_of_not_le hdim x o ho z
    · intro h
      exact node_not_boundary x o ho j ((le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_right))
    · intro h
      exact reflected_not_boundary x o ho j ((le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_right))
  have hp := (openConditions hdim x o z).2.2 j k hjk
  change 0 < (unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inr k))) (canonicalLeaf 0 x (Sum.inl (Sum.inr j)))).re at hp
  have h := congrArg Complex.re (positions_sub hdim x o z (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr j)))
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_pos.mp (h ▸ mul_pos hc hp)

theorem positions_upper_eq_iff (j k : Fin (n + 1)) :
    positions hdim x o z (Sum.inl (Sum.inl j)) = positions hdim x o z (Sum.inl (Sum.inl k)) ↔
      j = k ∨ j ∈ labelsSet x o ho ∧ k ∈ labelsSet x o ho := by
  by_cases hjk : j = k
  · subst k
    simp
  have hab : (Sum.inl (Sum.inl k) : DoubledLabel (n + 1) m) ≠ Sum.inl (Sum.inl j) := by
    simpa only [ne_eq, Sum.inl.injEq] using Ne.symm hjk
  have hu := (openConditions hdim x o z).1 ⟨(Sum.inl (Sum.inl k), Sum.inl (Sum.inl j)), hab⟩
  change unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inl j))) (canonicalLeaf 0 x (Sum.inl (Sum.inl k))) ≠ 0 at hu
  rw [← sub_eq_zero, positions_sub, smul_eq_zero]
  change (_ = 0 ∨ _ = 0) ↔ _
  rw [or_iff_left hu, scale_zero_iff hdim x o ho z, le_inf_iff, le_inf_iff]
  have hr : ¬ reflection 0 x (node x o ho) ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl j)) :=
    fun h => reflected_not_upper x o ho j ((le_canonicalLeaf_iff 0 x _ _).mp h)
  simp only [hr, false_and, or_false, hjk, false_or, le_canonicalLeaf_iff]
  simp only [labelsSet, ActualPairedForestPlanarFactor.labelsSet, mem_interiorLabels, node]

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoarsePositions
