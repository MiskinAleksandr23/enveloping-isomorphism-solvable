import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoarsePositions

/-! Literal coarse positions on proper real native forest faces. Exactly the
chosen fixed node collapses; all other position separation and geometric signs
are derived from the native radius and resolved-unit conditions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoarsePositions
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference AncestorScaleRatios ComplexConjugate ReflectedRadiusCoordinates
open PairedForestCoarsePositions (sourcePoint parameters sourcePoint_parameters radius_nonneg
  openConditions radius_reflect increment_reflect positions positions_reflect positions_sub)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n+1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)

abbrev node := (representative 0 x o).val
abbrev labelsSet := interiorLabels 0 x (node x o)

def IsFixed : Prop := reflection 0 x (node x o) = node x o

theorem properReal_isFixed (h : kind 0 x o = .properReal) : IsFixed x o :=
  ((nodeKind_properReal_iff 0 x _).mp ((kind_representative 0 x o).trans h)).1

theorem pureBoundary_isFixed (h : kind 0 x o = .pureBoundary) : IsFixed x o :=
  ((nodeKind_pureBoundary_iff 0 x _).mp ((kind_representative 0 x o).trans h)).1

theorem infinity_isFixed (h : kind 0 x o = .infinity) : IsFixed x o :=
  ((nodeKind_infinity_iff 0 x _).mp ((kind_representative 0 x o).trans h)).1

variable (ho : IsFixed x o)

include ho

theorem node_fixed : reflection 0 x (node x o) = node x o := ho

variable (z : ForestRadialFaceLocalization.source hdim x o)

theorem radius_zero_iff (v : tree 0 x) :
    (parameters hdim x o z).1 v = 0 ↔ v = node x o := by
  change radiusArray 0 x (faceAmbient hdim x o z.val) v = 0 ↔ _
  rw [radiusArray_face_zero_iff hdim x o z.val z.property.1 v]
  constructor
  · rintro ⟨hv, he⟩
    have h := (orbitClass_eq_iff (tree 0 x) (reflection 0 x) (reflection_reflection 0 x)
      (representative 0 x o) ⟨v,hv⟩).mp ((representative_orbit 0 x o).trans he.symm)
    rcases h with h | h
    · exact (congrArg Subtype.val h).symm
    · have hh := congrArg Subtype.val h
      change reflection 0 x (node x o) = v at hh
      exact hh.symm.trans (node_fixed x o ho)
  · rintro rfl
    exact ⟨(representative 0 x o).property, representative_orbit 0 x o⟩

theorem radius_pos_of_ne (v : tree 0 x) (hv : v ≠ node x o) :
    0 < (parameters hdim x o z).1 v :=
  lt_of_le_of_ne (radius_nonneg hdim x o z v)
    (Ne.symm fun h ↦ hv ((radius_zero_iff hdim x o ho z v).mp h))

theorem scale_zero_iff (v : tree 0 x) :
    scale (parameters hdim x o z).1 v = 0 ↔ node x o ≤ v := by
  simp only [scale, Finset.prod_eq_zero_iff, mem_ancestors, radius_zero_iff hdim x o ho z]
  exact ⟨fun ⟨u,hu,he⟩ ↦ he ▸ hu, fun h ↦ ⟨node x o,h,rfl⟩⟩

theorem scale_pos_of_not_le (v : tree 0 x) (hv : ¬node x o ≤ v) :
    0 < scale (parameters hdim x o z).1 v := by
  apply Finset.prod_pos
  intro u hu
  exact radius_pos_of_ne hdim x o ho z u
    (fun h ↦ hv (h ▸ (mem_ancestors u v).mp hu))

/-- The complete doubled mask is the precise coarse collision equivalence. -/
theorem positions_eq_iff (j k : DoubledLabel (n+1) m) :
    positions hdim x o z j = positions hdim x o z k ↔
      j = k ∨ j ∈ (node x o).val ∧ k ∈ (node x o).val := by
  by_cases hjk : j = k
  · subst k; simp
  have hu := (openConditions hdim x o z).1 ⟨(k,j), Ne.symm hjk⟩
  change unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x j) (canonicalLeaf 0 x k) ≠ 0 at hu
  rw [← sub_eq_zero, positions_sub, smul_eq_zero]
  change (_ = 0 ∨ _ = 0) ↔ _
  rw [or_iff_left hu, scale_zero_iff hdim x o ho z, le_inf_iff]
  simp only [hjk, false_or, le_canonicalLeaf_iff]

def center : ℝ :=
  (position (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2 (node x o)).re

theorem node_position_real :
    position (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2 (node x o) =
      (center hdim x o z : ℂ) := by
  have hi := ReflectedForestInsertion.position_im_eq_zero_of_fixed (tree 0 x) (reflection 0 x)
    (parameters hdim x o z).1 (radius_reflect hdim x o z)
    (parameters hdim x o z).2 (increment_reflect hdim x o z) (node x o) (node_fixed x o ho)
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi

theorem positions_inside (j : DoubledLabel (n+1) m) (hj : j ∈ (node x o).val) :
    positions hdim x o z j = (center hdim x o z : ℂ) := by
  change position _ _ _ _ = _
  rw [position_factor_from_ancestor (tree 0 x) _ _ ((le_canonicalLeaf_iff 0 x _ _).mpr hj),
    (scale_zero_iff hdim x o ho z _).mpr le_rfl, zero_smul, add_zero,
    node_position_real hdim x o ho z]

theorem positions_upper_im_pos_off (j : Fin (n+1)) (hj : j ∉ labelsSet x o) :
    0 < (positions hdim x o z (Sum.inl (Sum.inl j))).im := by
  have hc : 0 < scale (parameters hdim x o z).1
      (canonicalLeaf 0 x (Sum.inl (Sum.inl j)) ⊓ canonicalLeaf 0 x (Sum.inr j)) := by
    apply scale_pos_of_not_le hdim x o ho z
    intro h
    exact hj ((mem_interiorLabels 0 x _ _).mpr
      ((le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_left)))
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

/-- Actual increasing boundary coordinates remain strictly ordered unless
both labels are in the collapsed block. -/
theorem positions_boundary_lt (j k : Fin m) (hjk : j < k)
    (hblock : ¬(Sum.inl (Sum.inr j) ∈ (node x o).val ∧ Sum.inl (Sum.inr k) ∈ (node x o).val)) :
    (positions hdim x o z (Sum.inl (Sum.inr j))).re <
      (positions hdim x o z (Sum.inl (Sum.inr k))).re := by
  have hc : 0 < scale (parameters hdim x o z).1
      (canonicalLeaf 0 x (Sum.inl (Sum.inr k)) ⊓ canonicalLeaf 0 x (Sum.inl (Sum.inr j))) := by
    apply scale_pos_of_not_le hdim x o ho z
    intro h
    exact hblock ⟨(le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_right),
      (le_canonicalLeaf_iff 0 x _ _).mp (h.trans inf_le_left)⟩
  have hp := (openConditions hdim x o z).2.2 j k hjk
  change 0 < (unitDifference (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (canonicalLeaf 0 x (Sum.inl (Sum.inr k))) (canonicalLeaf 0 x (Sum.inl (Sum.inr j)))).re at hp
  have h := congrArg Complex.re (positions_sub hdim x o z (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr j)))
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_pos.mp (h ▸ mul_pos hc hp)

theorem boundary_mem_node_iff (j : Fin m) :
    Sum.inl (Sum.inr j) ∈ (node x o).val ↔
      j ∈ boundaryClusterBlock (blockLower 0 x (node x o)) (blockUpper 0 x (node x o)) :=
  fixed_label_mask 0 x _ (node_fixed x o ho) _

/-- Nonempty physical boundary blocks locate their coarse center uniquely
between the genuine outside boundary labels. -/
theorem boundary_lt_center
    (hne : (boundaryClusterBlock (blockLower 0 x (node x o)) (blockUpper 0 x (node x o))).Nonempty)
    (j : Fin m) (hj : j.val < (blockLower 0 x (node x o)).val) :
    (positions hdim x o z (Sum.inl (Sum.inr j))).re < center hdim x o z := by
  obtain ⟨k,hk⟩ := hne
  have hk' := (mem_boundaryClusterBlock _ _ k).mp hk
  have hjk : j < k := by change j.val < k.val; omega
  have hnot : Sum.inl (Sum.inr j) ∉ (node x o).val := by
    rw [boundary_mem_node_iff x o ho]
    simp only [mem_boundaryClusterBlock]
    omega
  have h := positions_boundary_lt hdim x o ho z j k hjk (fun h ↦ hnot h.1)
  rw [positions_inside hdim x o ho z _ ((boundary_mem_node_iff x o ho k).mpr hk)] at h
  exact h

theorem center_lt_boundary
    (hne : (boundaryClusterBlock (blockLower 0 x (node x o)) (blockUpper 0 x (node x o))).Nonempty)
    (j : Fin m) (hj : (blockUpper 0 x (node x o)).val ≤ j.val) :
    center hdim x o z < (positions hdim x o z (Sum.inl (Sum.inr j))).re := by
  obtain ⟨k,hk⟩ := hne
  have hk' := (mem_boundaryClusterBlock _ _ k).mp hk
  have hkj : k < j := by change k.val < j.val; omega
  have hnot : Sum.inl (Sum.inr j) ∉ (node x o).val := by
    rw [boundary_mem_node_iff x o ho]
    simp only [mem_boundaryClusterBlock]
    omega
  have h := positions_boundary_lt hdim x o ho z k j hkj (fun h ↦ hnot h.2)
  rw [positions_inside hdim x o ho z _ ((boundary_mem_node_iff x o ho k).mpr hk)] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoarsePositions
