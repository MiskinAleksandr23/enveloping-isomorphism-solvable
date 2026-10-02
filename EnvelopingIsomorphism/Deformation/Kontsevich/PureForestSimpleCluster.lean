import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterFreeChart
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates

/-! Actual pure-boundary primitive data extracted from a strict native forest
face. Both endpoint shapes and the global interior anchor are normalized by
proved positive affine transformations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCluster
open Configuration ExtractedForestParameters ForestRadialFaceClassification ForestRadialClusterLabels
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (normalize normalizeReal normalize_im normalize_self normalize_injective normalizeReal_strictMono)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .pureBoundary)

abbrev lower := blockLower 0 x (node x o)
abbrev upper := blockUpper 0 x (node x o)

include ho in
theorem interior_not_mem (j : Fin (n+1)) : j ∉ labelsSet x o := by
  have h := pureBoundary_interiorLabels 0 x (node x o) ((kind_representative 0 x o).trans ho)
  rw [show labelsSet x o = ∅ from h]
  simp

include ho in
/-- Endpoint labels are obtained from the actual nontrivial consecutive block. -/
theorem exists_endpoints : ∃ a b : Fin m,
    a.val = (lower x o).val ∧ b.val + 1 = (upper x o).val ∧ a < b := by
  have hc := pureBoundary_block_card 0 x (representative 0 x o) ((kind_representative 0 x o).trans ho)
  have hlen := BoundaryGraphOrderedCoordinates.shapeM_eq_sub (block_order 0 x (node x o))
  have he : BoundaryGraphFaceFactorization.shapeM (lower x o) (upper x o) =
      (boundaryClusterBlock (lower x o) (upper x o)).card := Fintype.card_coe _
  rw [he] at hlen
  change (boundaryClusterBlock (lower x o) (upper x o)).card = (upper x o).val - (lower x o).val at hlen
  change 1 < (boundaryClusterBlock (lower x o) (upper x o)).card at hc
  have hu := (upper x o).isLt
  let a : Fin m := ⟨(lower x o).val, by omega⟩
  let b : Fin m := ⟨(upper x o).val - 1, by omega⟩
  refine ⟨a,b,rfl,?_,?_⟩
  · dsimp [b]; omega
  · change (lower x o).val < (upper x o).val - 1
    omega

variable (a b : Fin m) (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

include hl hu hab in
theorem left_mem : a ∈ boundaryClusterBlock (lower x o) (upper x o) := by
  rw [mem_boundaryClusterBlock]
  have h : a.val < b.val := hab
  constructor <;> omega

include hl hu hab in
theorem right_mem : b ∈ boundaryClusterBlock (lower x o) (upper x o) := by
  rw [mem_boundaryClusterBlock]
  have h : a.val < b.val := hab
  constructor <;> omega

def anchor : ℂ := RealForestSimpleCluster.coarseAnchor hdim x o 0 z

include ho in
theorem anchor_pos : 0 < (anchor hdim x o z).im :=
  RealForestSimpleCluster.coarseAnchor_pos hdim x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho)
    0 (interior_not_mem x o ho 0) z

def shapePosition (j : Fin m) : ℝ :=
  (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re

def gap : ℝ := shapePosition hdim x o z b - shapePosition hdim x o z a

include ho hl hu hab in
theorem gap_pos : 0 < gap hdim x o a b z := by
  apply sub_pos.mpr
  exact RealForestShapePositions.positions_boundary_lt hdim x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z a b hab
    ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho) a).mpr
      (left_mem x o a b hl hu hab))
    ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho) b).mpr
      (right_mem x o a b hl hu hab))

def velocity (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock (lower x o) (upper x o)
  then (shapePosition hdim x o z j - shapePosition hdim x o z a) / gap hdim x o a b z else 0

def datum : PureBoundaryClusterData (0 : Fin (n+1)) m (lower x o) (upper x o) a b where
  center := RealForestSimpleCluster.center hdim x o 0 z
  interior j := ⟨RealForestSimpleCluster.base hdim x o 0 z j, by
    rw [RealForestSimpleCluster.base, normalize_im]
    exact div_pos (RealForestCoarsePositions.positions_upper_im_pos_off hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z j (interior_not_mem x o ho j))
      (anchor_pos hdim x o ho z)⟩
  boundaryBase := RealForestSimpleCluster.boundaryBase hdim x o 0 z
  boundaryVelocity := velocity hdim x o a b z
  left_endpoint := hl
  right_endpoint := hu
  endpoint_lt := hab
  interior_injective := by
    intro j k he
    have h := normalize_injective _ (anchor_pos hdim x o ho z)
      (congrArg (fun t : UpperHalfPlane ↦ (t : ℂ)) he)
    rcases (RealForestCoarsePositions.positions_eq_iff hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z _ _).mp h with he | hin
    · exact Sum.inl.inj (Sum.inl.inj he)
    · exact (interior_not_mem x o ho j ((mem_interiorLabels 0 x _ _).mpr hin.1)).elim
  interior_normalized := by
    apply UpperHalfPlane.ext
    exact normalize_self _ (anchor_pos hdim x o ho z)
  boundaryBase_eq_center j hj := by
    unfold RealForestSimpleCluster.boundaryBase RealForestSimpleCluster.center
    rw [RealForestCoarsePositions.positions_inside hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z _
      ((RealForestCoarsePositions.boundary_mem_node_iff x o
        (RealForestCoarsePositions.pureBoundary_isFixed x o ho) j).mpr hj)]
    rfl
  boundaryBase_lt_center j hj :=
    normalizeReal_strictMono _ (anchor_pos hdim x o ho z)
      (RealForestCoarsePositions.boundary_lt_center hdim x o
        (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z ⟨a,left_mem x o a b hl hu hab⟩ j hj)
  center_lt_boundaryBase j hj :=
    normalizeReal_strictMono _ (anchor_pos hdim x o ho z)
      (RealForestCoarsePositions.center_lt_boundary hdim x o
        (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z ⟨a,left_mem x o a b hl hu hab⟩ j hj)
  boundaryBase_lt j k hjk hnot := by
    apply normalizeReal_strictMono _ (anchor_pos hdim x o ho z)
    apply RealForestCoarsePositions.positions_boundary_lt hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z j k hjk
    simpa only [RealForestCoarsePositions.boundary_mem_node_iff x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho)] using hnot
  boundaryVelocity_zero_off j hj := by simp [velocity, hj]
  boundaryVelocity_strictMono_on j k hj hk hjk := by
    simp only [velocity, if_pos hj, if_pos hk]
    apply div_lt_div_of_pos_right _ (gap_pos hdim x o ho a b hl hu hab z)
    apply sub_lt_sub_right
    exact RealForestShapePositions.positions_boundary_lt hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z j k hjk
      ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho) j).mpr hj)
      ((RealForestCoarsePositions.boundary_mem_node_iff x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho) k).mpr hk)
  boundaryVelocity_left := by simp [velocity, left_mem x o a b hl hu hab]
  boundaryVelocity_right := by
    simp only [velocity, if_pos (right_mem x o a b hl hu hab)]
    exact div_self (gap_pos hdim x o ho a b hl hu hab z).ne'

def domain : PureBoundaryClusterDomain (0 : Fin (n+1)) m (lower x o) (upper x o) a b :=
  ⟨(datum hdim x o ho a b hl hu hab z, 0), PureBoundaryClusterData.admissibleScale_zero _⟩

def freeDomain : PureBoundaryClusterFreeDomain (0 : Fin (n+1)) m (lower x o) (upper x o) a b :=
  (domain hdim x o ho a b hl hu hab z).toFreeDomain

@[simp] theorem freeDomain_radius : (freeDomain hdim x o ho a b hl hu hab z).val.radius = 0 := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCluster
