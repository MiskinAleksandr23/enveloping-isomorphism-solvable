import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSmoothProduct
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestNormalScale
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterStandardCoordinates

/-! The actual full collar overlap, including its signed normal coordinate.
Its physical insertion equals the original normalized forest insertion on a
full neighborhood of every strict paired face point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestFullOverlap
open Configuration ExtractedForestParameters ExtractedForestChildShapes
open ForestRadialFaceClassification ForestOrthantRealization ForestInsertionDifference
open ForestRadialClusterLabels ForestNormalizationTelescope AncestorScaleRatios
open PairedForestSimpleCluster PairedForestSmoothProduct InteriorGraphFaceCoordinates BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

abbrev Angular := ClusterAngularCoordinates (0 : Fin (n + 1)) (anchor x o ho) (reference x o ho) (S x o ho) m

def overlap (u : Circle) (w : Coord (r + 1)) : Angular x o ho :=
  let q := toAngular (fullToProduct hdim x o ho u w)
  (q.1, q.2.1, q.2.2.1, q.2.2.2.1, PairedForestNormalScale.simpleRadius hdim x o ho w)

@[simp] theorem overlap_radius (u : Circle) (w : Coord (r + 1)) :
    (overlap hdim x o ho u w).toFree.radius = PairedForestNormalScale.simpleRadius hdim x o ho w := rfl

theorem contDiffAt_overlap (z : Source hdim x o) :
    ContDiffAt ℝ ⊤ (overlap hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o z) := by
  have hq := (contDiff_toAngular.contDiffAt.comp (facePoint hdim x o z)
    (contDiffAt_fullToProduct hdim x o ho z))
  have hr : ContDiffAt ℝ ⊤ (PairedForestNormalScale.simpleRadius hdim x o ho) (facePoint hdim x o z) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (r + 1) ↦ ℝ) (axis hdim x o)).contDiff.contDiffAt).mul (PairedForestNormalScale.contDiffAt_normalScale hdim x o ho z)
  exact hq.fst.prodMk (hq.snd.fst.prodMk (hq.snd.snd.fst.prodMk (hq.snd.snd.snd.fst.prodMk hr)))

theorem rawBase_eq_forward (w : Coord (r + 1)) (hw : rawHeight hdim x o w ≠ 0) (j : Fin (n + 1)) :
    rawBase hdim x o j w = GraphForms.interiorPoint j
      (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm w)) := by
  rw [ForestPositiveChartSmooth.interiorPoint_forwardCoordinates 0 x _ hw]
  simp only [Equiv.swap_self, Equiv.refl_apply]
  change ((rawHeight hdim x o w)⁻¹ : ℝ) * rawPosition hdim x o (Sum.inl (Sum.inl j)) w +
      ((-(rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).re / rawHeight hdim x o w : ℝ) : ℂ) =
    (rawPosition hdim x o (Sum.inl (Sum.inl j)) w -
      ((rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).re : ℂ)) / (rawHeight hdim x o w : ℂ)
  push_cast
  ring

theorem overlap_base (u : Circle) (w : Coord (r + 1)) (hw : rawHeight hdim x o w ≠ 0) (j : Fin (n + 1)) :
    (overlap hdim x o ho u w).toFree.base j = rawBase hdim x o (ClusterFreeCoordinates.representative (S x o ho) (anchor x o ho) j) w := by
  unfold ClusterFreeCoordinates.base
  split_ifs with h
  · rw [h, rawBase_eq_forward hdim x o w hw]
    rfl
  · simp [overlap, toAngular, fullToProduct, ClusterAngularCoordinates.toFree]

theorem overlap_velocity (u : Circle) (w : Coord (r + 1))
    (hw : 0 < rawShapeRadius hdim x o ho w) (j : Fin (n + 1)) :
    (overlap hdim x o ho u w).toFree.velocity j = rawVelocity hdim x o ho j w := by
  have href : rawVelocity hdim x o ho (reference x o ho) w ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [rawVelocity_reference_norm hdim x o ho w hw]; exact one_ne_zero)
  unfold ClusterFreeCoordinates.velocity
  split_ifs with ha hb hs
  · subst j
    simp [rawVelocity]
  · subst j
    simpa only [overlap, ClusterAngularCoordinates.toFree, toAngular, fullToProduct, circleParameter_eq] using
      circleParameter_angle_full hdim x o ho u w hw
  · simp only [overlap, ClusterAngularCoordinates.toFree, toAngular, fullToProduct,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rw [circleParameter_angle_full hdim x o ho u w hw]
    exact mul_div_cancel₀ _ href
  · exact (if_neg hs).symm

/-- Cancellation of the selected radius is done algebraically before dividing
by the nonzero reference unit. Thus the formula extends across radius zero. -/
theorem rawPosition_difference (w : Coord (r + 1)) (j : Fin (n + 1)) (hj : j ∈ S x o ho) :
    rawPosition hdim x o (Sum.inl (Sum.inl j)) w - rawPosition hdim x o (Sum.inl (Sum.inl (anchor x o ho))) w =
      (w (axis hdim x o) * PairedForestNormalScale.parentScale hdim x o ho w) •
        (rawShape hdim x o ho j w - rawShape hdim x o ho (anchor x o ho) w) := by
  have ha : PairedForestCoarsePositions.node x o ho ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl (anchor x o ho))) :=
    (le_canonicalLeaf_iff 0 x _ _).mpr ((mem_interiorLabels 0 x _ _).mp (anchor_mem x o ho))
  have hj' : PairedForestCoarsePositions.node x o ho ≤ canonicalLeaf 0 x (Sum.inl (Sum.inl j)) :=
    (le_canonicalLeaf_iff 0 x _ _).mpr ((mem_interiorLabels 0 x _ _).mp hj)
  unfold rawPosition
  rw [position_factor_from_ancestor (tree 0 x) _ _ hj', position_factor_from_ancestor (tree 0 x) _ _ ha]
  rw [scale_step (tree 0 x) _ _ (upperNode 0 x o ho).property.1]
  have hr : (rawParameters hdim x o w).1 (PairedForestCoarsePositions.node x o ho) = w (axis hdim x o) :=
    PairedForestNormalScale.selected_radius hdim x o ho w
  rw [hr]
  change (_ + _ • _) - (_ + _ • _) = _ • (_ - _)
  simp only [smul_sub]
  abel

theorem overlap_position (u : Circle) (w : Coord (r + 1))
    (hheight : rawHeight hdim x o w ≠ 0) (hshape : 0 < rawShapeRadius hdim x o ho w) (j : Fin (n + 1)) :
    (overlap hdim x o ho u w).position j = GraphForms.interiorPoint j
      (ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm w)) := by
  rw [ClusterAngularCoordinates.position, overlap_base hdim x o ho u w hheight, overlap_radius,
    overlap_velocity hdim x o ho u w hshape, ← rawBase_eq_forward hdim x o w hheight]
  by_cases hj : j ∈ S x o ho
  · rw [ClusterFreeCoordinates.representative, if_pos hj, rawVelocity, if_pos hj]
    have hdiff := rawPosition_difference hdim x o ho w j hj
    simp only [Complex.real_smul, Complex.ofReal_mul] at hdiff
    unfold rawBase
    have hn : (rawShapeRadius hdim x o ho w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hshape.ne'
    have hh : (rawHeight hdim x o w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hheight
    change _ + (((w (axis hdim x o) * (PairedForestNormalScale.parentScale hdim x o ho w *
      rawShapeRadius hdim x o ho w / rawHeight hdim x o w) : ℝ) : ℂ) * _) = _
    push_cast
    field_simp
    linear_combination -hdiff
  · rw [ClusterFreeCoordinates.representative, if_neg hj, rawVelocity, if_neg hj, mul_zero, add_zero]

/-- The full overlap reproduces the original physical graph insertion, with
no limiting or face-form identity assumed. -/
theorem physicalInsertion_overlap (u : Circle) (w : Coord (r + 1))
    (hheight : rawHeight hdim x o w ≠ 0) (hshape : 0 < rawShapeRadius hdim x o ho w) :
    ClusterStandardCoordinates.freeGraph (0 : Fin (n + 1))
      (InteriorClusterInsertionCoordinates.insertion (overlap hdim x o ho u w)) =
      ForestPositiveChartSmooth.forwardCoordinates 0 x ((ForestGlobalGraphStokes.sourceCoordinates hdim x).symm w) := by
  apply Prod.ext
  · funext j
    change (overlap hdim x o ho u w).position j.succ = _
    exact overlap_position hdim x o ho u w hheight hshape j.succ
  · funext j
    change rawBoundary hdim x o j w = _
    unfold rawBoundary rawShift ForestPositiveChartSmooth.forwardCoordinates
    change (rawHeight hdim x o w)⁻¹ * (rawPosition hdim x o (Sum.inl (Sum.inr j)) w).re +
      (-(rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).re / rawHeight hdim x o w) =
      ((rawPosition hdim x o (Sum.inl (Sum.inr j)) w).re -
        (rawPosition hdim x o (Sum.inl (Sum.inl 0)) w).re) / rawHeight hdim x o w
    ring

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestFullOverlap
