import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCoordinates

/-! Genuine simple infinity data for an empty boundary cluster, located at
the native collision center's actual ordered gap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestSimpleCluster
open Configuration ExtractedForestParameters ForestRadialFaceClassification ForestRadialClusterLabels
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (normalize_im normalize_self normalize_injective)
open InfinityForestSimpleCluster (interior_mem shapeAnchor shapeAnchor_pos offset coarseScale boundaryBase)
open scoped Classical
open Filter
open scoped Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (node x o).val)
  (q : Fin m) (z : ForestRadialFaceLocalization.source hdim x o)

abbrev slot := EmptyRealForestSlot.physicalSlot hdim x o
  (RealForestCoarsePositions.infinity_isFixed x o ho) z hempty 0 (interior_mem x o ho 0)

include ho hempty in
theorem coarseScale_pos : 0 < coarseScale hdim x o q z := by
  apply abs_pos.mpr
  exact sub_ne_zero.mpr (EmptyRealForestSlot.boundaryValues_ne_center hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z hempty 0 (interior_mem x o ho 0) q)

include ho hempty in
theorem offset_neg (j : Fin m) (hj : j.val < (slot hdim x o ho hempty z).val) :
    offset hdim x o z j < 0 :=
  sub_neg.mpr ((EmptyRealForestSlot.physicalSlot_isGap hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z hempty 0 (interior_mem x o ho 0)).1 j hj)

include ho hempty in
theorem offset_pos (j : Fin m) (hj : (slot hdim x o ho hempty z).val ≤ j.val) :
    0 < offset hdim x o z j :=
  sub_pos.mpr ((EmptyRealForestSlot.physicalSlot_isGap hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z hempty 0 (interior_mem x o ho 0)).2 j hj)

def datum : BoundaryAnchoredInfinityData (0 : Fin (n+1)) m
    (slot hdim x o ho hempty z) (slot hdim x o ho hempty z) q where
  shape j := ⟨RealForestSimpleCluster.normalize (shapeAnchor hdim x o z)
    (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inl j))), by
    rw [normalize_im]
    exact div_pos (RealForestShapePositions.positions_upper_im_pos hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z j (interior_mem x o ho j))
      (shapeAnchor_pos hdim x o ho z)⟩
  boundaryBase := boundaryBase hdim x o q z
  boundaryVelocity := fun _ ↦ 0
  shape_injective := by
    intro j k he
    have h := normalize_injective _ (shapeAnchor_pos hdim x o ho z)
      (congrArg (fun t : UpperHalfPlane ↦ (t : ℂ)) he)
    exact Sum.inl.inj (Sum.inl.inj (RealForestShapePositions.positions_injective_on hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho j))
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho k)) h))
  shape_anchor := by apply UpperHalfPlane.ext; exact normalize_self _ (shapeAnchor_pos hdim x o ho z)
  block_order := le_rfl
  outside_not_mem := by simp [boundaryClusterBlock_self]
  boundaryBase_zero_on j hj := by simpa only [boundaryClusterBlock_self, Finset.notMem_empty] using hj
  boundaryBase_neg_left j hj := div_neg_of_neg_of_pos (offset_neg hdim x o ho hempty z j hj)
    (coarseScale_pos hdim x o ho hempty q z)
  boundaryBase_pos_right j hj := div_pos (offset_pos hdim x o ho hempty z j hj)
    (coarseScale_pos hdim x o ho hempty q z)
  boundaryBase_lt j k hjk _ := by
    apply div_lt_div_of_pos_right _ (coarseScale_pos hdim x o ho hempty q z)
    apply sub_lt_sub_right
    exact RealForestCoarsePositions.positions_boundary_lt hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z j k hjk (fun h ↦ hempty j h.1)
  boundaryVelocity_zero_off _ _ := rfl
  boundaryVelocity_strictMono_on j _ hj _ _ := by
    simpa only [boundaryClusterBlock_self, Finset.notMem_empty] using hj
  boundaryBase_anchor := by
    unfold boundaryBase InfinityForestSimpleCluster.coarseScale BoundaryAnchoredInfinityData.referenceSign
    split_ifs with hleft
    · rw [abs_of_neg (offset_neg hdim x o ho hempty z q hleft), div_neg,
        div_self (offset_neg hdim x o ho hempty z q hleft).ne]
    · rw [abs_of_pos (offset_pos hdim x o ho hempty z q (by omega)),
        div_self (offset_pos hdim x o ho hempty z q (by omega)).ne']

def domain : BoundaryAnchoredInfinityDomain (0 : Fin (n+1)) m
    (slot hdim x o ho hempty z) (slot hdim x o ho hempty z) q :=
  ⟨(datum hdim x o ho hempty q z, 0), BoundaryAnchoredInfinityData.admissibleScale_zero _⟩

def freeDomain : BoundaryAnchoredInfinityFreeDomain (0 : Fin (n+1)) m
    (slot hdim x o ho hempty z) (slot hdim x o ho hempty z) q :=
  (domain hdim x o ho hempty q z).toFreeDomain

theorem coordinates_eq_freeDomain :
    BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
      (InfinityForestSimpleCoordinates.coordinates hdim x o q z.val) =
      (freeDomain hdim x o ho hempty q z).val := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j
      simp only [InfinityForestSimpleCoordinates.coordinates,
        EmptyRealForestSimpleCluster.classifier_block_empty x o
          (RealForestCoarsePositions.infinity_isFixed x o ho) hempty,
        Finset.notMem_empty, ↓reduceIte]
      change _ = if j.val ∈ boundaryClusterBlock _ _ then _ else boundaryBase hdim x o q z j.val
      simp only [boundaryClusterBlock_self, Finset.notMem_empty, ↓reduceIte]
      rfl
    · rfl

theorem coordinates_mem_source :
    (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding
      (InfinityForestSimpleCoordinates.coordinates hdim x o q z.val)).OpenConditions
      (slot hdim x o ho hempty z) (slot hdim x o ho hempty z) := by
  rw [coordinates_eq_freeDomain hdim x o ho hempty q z]
  exact (freeDomain hdim x o ho hempty q z).property.2

include ho hempty in
theorem contDiffAt_coordinates : ContDiffAt ℝ ⊤ (InfinityForestSimpleCoordinates.coordinates hdim x o q) z.val := by
  have hs := (RealForestSimpleCoordinates.contDiff_shapePosition hdim x o (Sum.inl (Sum.inl 0))).contDiffAt (x := z.val)
  have hp : 0 < (RealForestSimpleCoordinates.shapePosition hdim x o (Sum.inl (Sum.inl 0)) z.val).im :=
    shapeAnchor_pos hdim x o ho z
  have hg : 0 < |InfinityForestSimpleCoordinates.offset hdim x o q z.val| :=
    coarseScale_pos hdim x o ho hempty q z
  have hg' := abs_pos.mp hg
  have hnorm : ContDiffAt ℝ ⊤ (fun w ↦ |InfinityForestSimpleCoordinates.offset hdim x o q w|) z.val := by
    simpa only [Real.norm_eq_abs] using
      (InfinityForestSimpleCoordinates.contDiff_offset hdim x o q).contDiffAt.norm ℝ hg'
  unfold InfinityForestSimpleCoordinates.coordinates
  refine (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hs
    (RealForestSimpleCoordinates.contDiff_shapePosition hdim x o _).contDiffAt hp).prodMk
      (contDiffAt_pi.mpr fun j ↦ ?_)
  split_ifs
  · exact RealForestSimpleCoordinates.smooth_normalizeReal hs
      (Complex.reCLM.contDiff.contDiffAt.comp _ (RealForestSimpleCoordinates.contDiff_shapePosition hdim x o _).contDiffAt) hp
  · exact (InfinityForestSimpleCoordinates.contDiff_offset hdim x o j.val).contDiffAt.div hnorm hg.ne'

/-- The recovered physical gap is constant near a strict native face point.
This is needed when differentiating the chart, whose outside anchor has a
sign determined by that gap. -/
theorem eventually_slot_eq : ∀ᶠ w in 𝓝 z.val,
    ∀ hw : w ∈ ForestRadialFaceLocalization.source hdim x o,
      slot hdim x o ho hempty ⟨w,hw⟩ = slot hdim x o ho hempty z := by
  let s := slot hdim x o ho hempty z
  have heach (j : Fin m) : ∀ᶠ w in 𝓝 z.val,
      (j.val < s.val → InfinityForestSimpleCoordinates.offset hdim x o j w < 0) ∧
      (s.val ≤ j.val → 0 < InfinityForestSimpleCoordinates.offset hdim x o j w) := by
    by_cases hj : j.val < s.val
    · have he := (isOpen_lt (InfinityForestSimpleCoordinates.contDiff_offset hdim x o j).continuous
        continuous_const).mem_nhds (offset_neg hdim x o ho hempty z j hj)
      filter_upwards [he] with w hw
      exact ⟨fun _ ↦ hw, fun h ↦ (Nat.not_lt_of_ge h hj).elim⟩
    · have he := (isOpen_lt continuous_const
        (InfinityForestSimpleCoordinates.contDiff_offset hdim x o j).continuous).mem_nhds
          (offset_pos hdim x o ho hempty z j (by omega))
      filter_upwards [he] with w hw
      exact ⟨fun h ↦ (hj h).elim, fun _ ↦ hw⟩
  filter_upwards [Filter.eventually_all.mpr heach] with w hw hsource
  apply OrderedBoundaryGap.gap_unique (EmptyRealForestSlot.physicalSlot_isGap hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) ⟨w,hsource⟩ hempty 0 (interior_mem x o ho 0))
  exact ⟨fun j hj ↦ sub_neg.mp ((hw j).1 hj), fun j hj ↦ sub_pos.mp ((hw j).2 hj)⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestSimpleCluster
