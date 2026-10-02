import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCoarsePositions
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFreeCoordinateEquiv

/-! Actual normalized simple interior-cluster data extracted from a strict
paired forest face. The marked anchor is the global anchor when it lies inside
the cluster; no coarse admissibility or shape injectivity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster

open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestInsertionDifference AncestorScaleRatios ComplexConjugate
open BoxStokes PairedForestCoarsePositions
open scoped Classical UpperHalfPlane

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x) (ho : kind 0 x o = .paired)

abbrev S := labelsSet x o ho

theorem S_nonempty : (S x o ho).Nonempty :=
  Finset.card_pos.mp (lt_trans Nat.zero_lt_one (upperNode_card 0 x o ho))

def anchor : Fin (n + 1) := if 0 ∈ S x o ho then 0 else (S_nonempty x o ho).choose

theorem anchor_mem : anchor x o ho ∈ S x o ho := by
  unfold anchor
  split_ifs with h
  · exact h
  · exact (S_nonempty x o ho).choose_spec

theorem anchor_global (h : 0 ∈ S x o ho) : anchor x o ho = 0 := if_pos h

def reference : Fin (n + 1) :=
  ((S x o ho).exists_mem_ne (upperNode_card 0 x o ho) (anchor x o ho)).choose

theorem reference_mem : reference x o ho ∈ S x o ho :=
  ((S x o ho).exists_mem_ne (upperNode_card 0 x o ho) (anchor x o ho)).choose_spec.1

theorem reference_ne_anchor : reference x o ho ≠ anchor x o ho :=
  ((S x o ho).exists_mem_ne (upperNode_card 0 x o ho) (anchor x o ho)).choose_spec.2

variable (z : ForestRadialFaceLocalization.source hdim x o)

def upperPoint (j : Fin (n + 1)) : ℍ :=
  ⟨positions hdim x o z (Sum.inl (Sum.inl j)), positions_upper_im_pos hdim x o ho z j⟩

def normalizer : PositiveAffine :=
  ⟨(upperPoint hdim x o ho z 0).im⁻¹,
    -(upperPoint hdim x o ho z 0).re / (upperPoint hdim x o ho z 0).im,
    inv_pos.mpr (upperPoint hdim x o ho z 0).im_pos⟩

def base (j : Fin (n + 1)) : ℍ := (normalizer hdim x o ho z).onUpper (upperPoint hdim x o ho z j)

def boundary (j : Fin m) : ℝ :=
  (normalizer hdim x o ho z).onReal (positions hdim x o z (Sum.inl (Sum.inr j))).re

theorem base_normalized : base hdim x o ho z 0 = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext_re_im
  · simp [base, normalizer, div_eq_mul_inv, mul_comm]
  · simp [base, normalizer, (upperPoint hdim x o ho z 0).im_ne_zero]

theorem base_eq_iff (j k : Fin (n + 1)) :
    base hdim x o ho z j = base hdim x o ho z k ↔ j = k ∨ j ∈ S x o ho ∧ k ∈ S x o ho := by
  unfold base
  rw [(normalizer hdim x o ho z).onUpper_injective.eq_iff]
  rw [UpperHalfPlane.ext_iff]
  exact positions_upper_eq_iff hdim x o ho z j k

theorem boundary_strictMono : StrictMono (boundary hdim x o ho z) :=
  (normalizer hdim x o ho z).onReal_strictMono.comp (positions_boundary_strictMono hdim x o ho z)

def shapePosition (j : Fin (n + 1)) : ℂ :=
  branchUnit (tree 0 x) (parameters hdim x o z).1 (parameters hdim x o z).2
    (node x o ho) (canonicalLeaf 0 x (Sum.inl (Sum.inl j)))

theorem positiveBelow : ForestDescendantPlanarCoordinates.PositiveBelow 0 x (node x o ho)
    (PairedForestCoarsePositions.sourcePoint hdim x o z).val := by
  intro v hv _
  rw [sourcePoint_parameters]
  change 0 < radiusArray 0 x (faceAmbient hdim x o z.val) v.val
  apply radiusArray_face_descendant_pos hdim x o z.val z.property.1 (upperNode 0 x o ho)
    (upperNode_spec 0 x o ho).1
  exact lt_of_le_of_ne v.property (fun h => hv (Subtype.ext h.symm))

theorem shapePosition_injective_on : Set.InjOn (shapePosition hdim x o ho z) (S x o ho) := by
  intro j hj k hk he
  have hjr : j ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hj
  have hkr : k ∈ Set.range (ActualPairedForestPlanarFactor.labels x o ho) :=
    (ActualPairedForestPlanarFactor.labels_range x o ho).symm ▸ hk
  obtain ⟨a, rfl⟩ := hjr
  obtain ⟨b, rfl⟩ := hkr
  have hh := ForestDescendantPlanarCoordinates.positions_injective 0 x (node x o ho)
    (ActualPairedForestPlanarFactor.labels x o ho) (ActualPairedForestPlanarFactor.labels_injective x o ho)
    (ActualPairedForestPlanarFactor.labels_below x o ho)
    (PairedForestCoarsePositions.sourcePoint hdim x o z) (positiveBelow hdim x o ho z)
  apply congrArg (ActualPairedForestPlanarFactor.labels x o ho)
  apply hh
  change branchUnit _ _ _ _ _ = branchUnit _ _ _ _ _
  rw [sourcePoint_parameters]
  exact he

def shapeRadius : ℝ :=
  ‖shapePosition hdim x o ho z (reference x o ho) - shapePosition hdim x o ho z (anchor x o ho)‖

theorem shapeRadius_pos : 0 < shapeRadius hdim x o ho z := by
  apply norm_pos_iff.mpr
  apply sub_ne_zero.mpr
  intro h
  exact reference_ne_anchor x o ho
    (shapePosition_injective_on hdim x o ho z (reference_mem x o ho) (anchor_mem x o ho) h)

def velocity (j : Fin (n + 1)) : ℂ :=
  if j ∈ S x o ho then
    (shapePosition hdim x o ho z j - shapePosition hdim x o ho z (anchor x o ho)) /
      (shapeRadius hdim x o ho z : ℂ)
  else 0

theorem velocity_anchor : velocity hdim x o ho z (anchor x o ho) = 0 := by
  simp [velocity]

theorem velocity_reference_norm : ‖velocity hdim x o ho z (reference x o ho)‖ = 1 := by
  rw [velocity, if_pos (reference_mem x o ho), norm_div]
  rw [Complex.norm_real, Real.norm_of_nonneg (shapeRadius_pos hdim x o ho z).le]
  exact div_self (shapeRadius_pos hdim x o ho z).ne'

theorem velocity_zero_off (j : Fin (n + 1)) (hj : j ∉ S x o ho) : velocity hdim x o ho z j = 0 :=
  if_neg hj

theorem velocity_normalized : velocity hdim x o ho z 0 = 0 := by
  by_cases hi : 0 ∈ S x o ho
  · rw [← anchor_global x o ho hi]
    exact velocity_anchor hdim x o ho z
  · exact velocity_zero_off hdim x o ho z 0 hi

theorem velocity_injective_on : Set.InjOn (velocity hdim x o ho z) (S x o ho) := by
  intro j hj k hk he
  change j ∈ S x o ho at hj
  change k ∈ S x o ho at hk
  rw [velocity, if_pos hj, velocity, if_pos hk] at he
  apply shapePosition_injective_on hdim x o ho z hj hk
  exact sub_left_inj.mp ((div_left_inj' (Complex.ofReal_ne_zero.mpr
    (shapeRadius_pos hdim x o ho z).ne')).mp he)

/-- Genuine simple collision data with actual normalized coarse positions and
native subtree velocities. -/
def datum : SingleInteriorCluster (0 : Fin (n + 1)) m (S x o ho) where
  base := base hdim x o ho z
  velocity := velocity hdim x o ho z
  separated := by
    intro j k hb hv
    rcases (base_eq_iff hdim x o ho z j k).mp hb with h | ⟨hj, hk⟩
    · exact h
    · exact velocity_injective_on hdim x o ho z hj hk hv
  boundary := boundary hdim x o ho z
  boundary_strictMono := boundary_strictMono hdim x o ho z
  base_normalized := base_normalized hdim x o ho z
  velocity_normalized := velocity_normalized hdim x o ho z
  cluster_nonempty := S_nonempty x o ho
  base_eq_iff := base_eq_iff hdim x o ho z
  velocity_zero_off := velocity_zero_off hdim x o ho z

/-- An actual normalized zero-radius simple-cluster parameter point. -/
def slice : NormalizedInteriorClusterSlice (0 : Fin (n + 1)) m (S x o ho)
    (anchor x o ho) (reference x o ho) :=
  ⟨⟨(datum hdim x o ho z, 0), (datum hdim x o ho z).toInteriorCollisionData.admissibleScale_zero⟩,
    velocity_anchor hdim x o ho z, velocity_reference_norm hdim x o ho z⟩

@[simp] theorem slice_scale : (slice hdim x o ho z).val.scale = 0 := rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleCluster
