import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSlot
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates

/-! The actual empty-boundary proper real forest produces genuine simple
cluster data at its physical slot. No nonempty block is required, and the
classifier's arbitrary empty-mask slot is never used for boundary ordering. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSimpleCluster
open Configuration ExtractedForestParameters ForestRadialClusterLabels
open ForestRadialFaceClassification RealForestSimpleCoordinates RealForestResolvedCoordinates
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (node x o).val)
  (z : ForestRadialFaceLocalization.source hdim x o)

abbrev slot := EmptyRealForestSlot.physicalSlot hdim x o ho z hempty a ha

include ho hempty in
theorem classifier_block_empty : boundaryClusterBlock (lower x o) (upper x o) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact hempty j ((RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mpr hj)

def datum : BoundaryClusterData b a m (labelsSet x o)
    (slot hdim x o ho a ha hempty z) (slot hdim x o ho a ha hempty z) where
  center := RealForestSimpleCluster.center hdim x o b z
  base := base hdim x o b z
  velocity := velocity hdim x o a z
  boundaryBase := boundaryBase hdim x o b z
  boundaryVelocity := fun _ ↦ 0
  anchor_mem := ha
  normalized_not_mem := hb
  block_order := le_rfl
  base_eq_center j hj := by
    unfold base RealForestSimpleCluster.center
    rw [RealForestCoarsePositions.positions_inside hdim x o ho z _
      ((mem_interiorLabels 0 x _ _).mp hj), normalize_real]
  base_im_pos_off j hj := by
    rw [base, normalize_im]
    exact div_pos (RealForestCoarsePositions.positions_upper_im_pos_off hdim x o ho z j hj)
      (coarseAnchor_pos hdim x o ho b hb z)
  base_injective_off j k hj hk he := by
    have h := normalize_injective _ (coarseAnchor_pos hdim x o ho b hb z) he
    rcases (RealForestCoarsePositions.positions_eq_iff hdim x o ho z _ _).mp h with h | h
    · exact Sum.inl.inj (Sum.inl.inj h)
    · exact (hj ((mem_interiorLabels 0 x _ _).mpr h.1)).elim
  base_normalized := normalize_self _ (coarseAnchor_pos hdim x o ho b hb z)
  velocity_im_pos j hj := by
    simp only [velocity, if_pos hj, normalize_im]
    exact div_pos (RealForestShapePositions.positions_upper_im_pos hdim x o ho z j hj)
      (shapeAnchor_pos hdim x o ho a ha z)
  velocity_zero_off j hj := by simp [velocity, hj]
  velocity_injective_on j k hj hk he := by
    simp only [velocity, if_pos hj, if_pos hk] at he
    have h := normalize_injective _ (shapeAnchor_pos hdim x o ho a ha z) he
    exact Sum.inl.inj (Sum.inl.inj (RealForestShapePositions.positions_injective_on hdim x o ho z
      ((mem_interiorLabels 0 x _ _).mp hj) ((mem_interiorLabels 0 x _ _).mp hk) h))
  velocity_anchor := by
    simp only [velocity, if_pos ha]
    exact normalize_self _ (shapeAnchor_pos hdim x o ho a ha z)
  boundaryBase_eq_center j hj := by simpa only [boundaryClusterBlock_self, Finset.notMem_empty] using hj
  boundaryBase_lt_center j hj :=
    normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
      ((EmptyRealForestSlot.physicalSlot_isGap hdim x o ho z hempty a ha).1 j hj)
  center_lt_boundaryBase j hj :=
    normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
      ((EmptyRealForestSlot.physicalSlot_isGap hdim x o ho z hempty a ha).2 j hj)
  boundaryBase_lt j k hjk _ :=
    normalizeReal_strictMono _ (coarseAnchor_pos hdim x o ho b hb z)
      (RealForestCoarsePositions.positions_boundary_lt hdim x o ho z j k hjk
        (fun h ↦ hempty j h.1))
  boundaryVelocity_zero_off _ _ := rfl
  boundaryVelocity_strictMono_on j _ hj _ _ := by
    simpa only [boundaryClusterBlock_self, Finset.notMem_empty] using hj

def domain : BoundaryClusterDomain b a m (labelsSet x o)
    (slot hdim x o ho a ha hempty z) (slot hdim x o ho a ha hempty z) :=
  ⟨(datum hdim x o ho a b ha hb hempty z, 0), BoundaryClusterData.admissibleScale_zero _⟩

def freeDomain : BoundaryClusterFreeDomain b a (labelsSet x o) m
    (slot hdim x o ho a ha hempty z) (slot hdim x o ho a ha hempty z) :=
  (domain hdim x o ho a b ha hb hempty z).toFreeDomain

theorem coordinates_eq_freeDomain :
    BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val) =
      (freeDomain hdim x o ho a b ha hb hempty z).val := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j
      change RealForestSimpleCluster.normalize _ _ = velocity hdim x o a z j.val
      rw [velocity, if_pos j.property.1]
      rfl
    · apply Prod.ext
      · funext j
        simp only [coordinates, classifier_block_empty x o ho hempty, Finset.notMem_empty, ↓reduceIte]
        change _ = if j ∈ boundaryClusterBlock _ _ then _ else boundaryBase hdim x o b z j
        simp only [boundaryClusterBlock_self, Finset.notMem_empty, ↓reduceIte]
        rfl
      · rfl

include hb in
theorem coordinates_mem_source :
    (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val)).OpenConditions
      (slot hdim x o ho a ha hempty z) (slot hdim x o ho a ha hempty z) := by
  rw [coordinates_eq_freeDomain hdim x o ho a b ha hb hempty z]
  exact (freeDomain hdim x o ho a b ha hb hempty z).property.2

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSimpleCluster
