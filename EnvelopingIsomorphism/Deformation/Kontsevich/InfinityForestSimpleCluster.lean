import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityFreeCoordinateEquiv

/-! Actual all-interior infinity primitive data obtained from a strict native
fixed forest face. The coarse center is zero and an actual outside real label
is normalized to its prescribed sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCluster
open Configuration ExtractedForestParameters ForestRadialFaceClassification ForestRadialClusterLabels
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (normalize_im normalize_self normalize_injective normalizeReal_strictMono)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .infinity)

abbrev lower := blockLower 0 x (node x o)
abbrev upper := blockUpper 0 x (node x o)

include ho in
theorem interior_mem (j : Fin (n+1)) : j ∈ labelsSet x o := by
  have h := infinity_interiorLabels 0 x (node x o) ((kind_representative 0 x o).trans ho)
  rw [show labelsSet x o = Finset.univ from h]
  simp

variable (q : Fin m) (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

def shapeAnchor : ℂ := RealForestSimpleCluster.shapeAnchor hdim x o 0 z
include ho in
theorem shapeAnchor_pos : 0 < (shapeAnchor hdim x o z).im :=
  RealForestSimpleCluster.shapeAnchor_pos hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho)
    0 (interior_mem x o ho 0) z

def offset (j : Fin m) : ℝ :=
  (PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re -
    RealForestCoarsePositions.center hdim x o z

def coarseScale : ℝ := |offset hdim x o z q|

include ho hne in
theorem offset_neg (j : Fin m) (hj : j.val < (lower x o).val) : offset hdim x o z j < 0 :=
  sub_neg.mpr (RealForestCoarsePositions.boundary_lt_center hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z hne j hj)

include ho hne in
theorem offset_pos (j : Fin m) (hj : (upper x o).val ≤ j.val) : 0 < offset hdim x o z j :=
  sub_pos.mpr (RealForestCoarsePositions.center_lt_boundary hdim x o
    (RealForestCoarsePositions.infinity_isFixed x o ho) z hne j hj)

include ho hq hne in
theorem coarseScale_pos : 0 < coarseScale hdim x o q z := by
  apply abs_pos.mpr
  have hnot : ¬ ((lower x o).val ≤ q.val ∧ q.val < (upper x o).val) := by
    simpa only [mem_boundaryClusterBlock] using hq
  by_cases hleft : q.val < (lower x o).val
  · exact (offset_neg hdim x o ho hne z q hleft).ne
  · exact (offset_pos hdim x o ho hne z q (by omega)).ne'

def boundaryBase (j : Fin m) : ℝ := offset hdim x o z j / coarseScale hdim x o q z

def boundaryVelocity (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock (lower x o) (upper x o) then
    RealForestSimpleCluster.normalizeReal (shapeAnchor hdim x o z)
      (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re else 0

def datum : BoundaryAnchoredInfinityData (0 : Fin (n+1)) m (lower x o) (upper x o) q where
  shape j := ⟨RealForestSimpleCluster.normalize (shapeAnchor hdim x o z)
    (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inl j))), by
    rw [normalize_im]
    exact div_pos (RealForestShapePositions.positions_upper_im_pos hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z j (interior_mem x o ho j))
      (shapeAnchor_pos hdim x o ho z)⟩
  boundaryBase := boundaryBase hdim x o q z
  boundaryVelocity := boundaryVelocity hdim x o z
  shape_injective := by
    intro j k he
    have h := normalize_injective _ (shapeAnchor_pos hdim x o ho z)
      (congrArg (fun t : UpperHalfPlane ↦ (t : ℂ)) he)
    exact Sum.inl.inj (Sum.inl.inj (RealForestShapePositions.positions_injective_on hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho j))
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho k)) h))
  shape_anchor := by apply UpperHalfPlane.ext; exact normalize_self _ (shapeAnchor_pos hdim x o ho z)
  block_order := block_order 0 x (node x o)
  outside_not_mem := hq
  boundaryBase_zero_on j hj := by
    unfold boundaryBase offset
    rw [RealForestCoarsePositions.positions_inside hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z _
      ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.infinity_isFixed x o ho) j).mpr hj)]
    simp
  boundaryBase_neg_left j hj := div_neg_of_neg_of_pos (offset_neg hdim x o ho hne z j hj)
    (coarseScale_pos hdim x o ho q hq hne z)
  boundaryBase_pos_right j hj := div_pos (offset_pos hdim x o ho hne z j hj)
    (coarseScale_pos hdim x o ho q hq hne z)
  boundaryBase_lt j k hjk hnot := by
    apply div_lt_div_of_pos_right _ (coarseScale_pos hdim x o ho q hq hne z)
    apply sub_lt_sub_right
    apply RealForestCoarsePositions.positions_boundary_lt hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z j k hjk
    simpa only [RealForestCoarsePositions.boundary_mem_node_iff x o
      (RealForestCoarsePositions.infinity_isFixed x o ho)] using hnot
  boundaryVelocity_zero_off j hj := by simp [boundaryVelocity, hj]
  boundaryVelocity_strictMono_on j k hj hk hjk := by
    simp only [boundaryVelocity, if_pos hj, if_pos hk]
    apply normalizeReal_strictMono _ (shapeAnchor_pos hdim x o ho z)
    exact RealForestShapePositions.positions_boundary_lt hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z j k hjk
      ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.infinity_isFixed x o ho) j).mpr hj)
      ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.infinity_isFixed x o ho) k).mpr hk)
  boundaryBase_anchor := by
    unfold boundaryBase coarseScale BoundaryAnchoredInfinityData.referenceSign
    split_ifs with hleft
    · rw [abs_of_neg (offset_neg hdim x o ho hne z q hleft), div_neg,
        div_self (offset_neg hdim x o ho hne z q hleft).ne]
    · have hright : (upper x o).val ≤ q.val := by
        have hn : ¬ ((lower x o).val ≤ q.val ∧ q.val < (upper x o).val) := by
          simpa only [mem_boundaryClusterBlock] using hq
        omega
      rw [abs_of_pos (offset_pos hdim x o ho hne z q hright),
        div_self (offset_pos hdim x o ho hne z q hright).ne']

def domain : BoundaryAnchoredInfinityDomain (0 : Fin (n+1)) m (lower x o) (upper x o) q :=
  ⟨(datum hdim x o ho q hq hne z, 0), BoundaryAnchoredInfinityData.admissibleScale_zero _⟩

def freeDomain : BoundaryAnchoredInfinityFreeDomain (0 : Fin (n+1)) m (lower x o) (upper x o) q :=
  (domain hdim x o ho q hq hne z).toFreeDomain

@[simp] theorem freeDomain_radius : (freeDomain hdim x o ho q hq hne z).val.radius = 0 := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCluster
