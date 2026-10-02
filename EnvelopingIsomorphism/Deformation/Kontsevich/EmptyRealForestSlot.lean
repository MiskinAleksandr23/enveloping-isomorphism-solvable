import EnvelopingIsomorphism.Deformation.Kontsevich.OrderedBoundaryGap
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestCoarsePositions

/-! Actual empty real-cluster faces have a unique physical boundary slot.
The slot is recovered from the native collision center and boundary positions,
so the arbitrary empty-mask representative is not used as positional data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSlot

open Configuration ExtractedForestParameters ForestRadialClusterLabels
open ForestRadialFaceClassification PairedForestCoarsePositions
open RealForestCoarsePositions OrderedBoundaryGap
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
    (x : Compactification (0 : Fin (n + 1)) m)
    (o : ForestRadialFaceClassification.Orbit 0 x)
    (ho : RealForestCoarsePositions.IsFixed x o)
    (z : ForestRadialFaceLocalization.source hdim x o)

def boundaryValues : Fin m → ℝ := fun j =>
  (positions hdim x o z (Sum.inl (Sum.inr j))).re

variable (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (RealForestCoarsePositions.node x o).val)

include ho hempty in
theorem boundaryValues_strictMono : StrictMono (boundaryValues hdim x o z) := by
  intro j k hjk
  exact RealForestCoarsePositions.positions_boundary_lt hdim x o ho z j k hjk
    (fun h => hempty j h.1)

theorem boundaryPosition_im_zero (j : Fin m) :
    (positions hdim x o z (Sum.inl (Sum.inr j))).im = 0 := by
  have h := congrArg Complex.im (positions_reflect hdim x o z (Sum.inl (Sum.inr j)))
  simp only [doubledReflection, Complex.conj_im] at h
  linarith

variable (a : Fin (n + 1)) (ha : a ∈ RealForestCoarsePositions.labelsSet x o)

include ho hempty ha in
theorem boundaryValues_ne_center (j : Fin m) :
    boundaryValues hdim x o z j ≠ RealForestCoarsePositions.center hdim x o z := by
  intro hj
  have ha' : Sum.inl (Sum.inl a) ∈ (RealForestCoarsePositions.node x o).val :=
    (mem_interiorLabels 0 x _ _).mp ha
  have he : positions hdim x o z (Sum.inl (Sum.inr j)) =
      positions hdim x o z (Sum.inl (Sum.inl a)) := by
    rw [positions_inside hdim x o ho z _ ha']
    apply Complex.ext
    · exact hj
    · simpa only [Complex.ofReal_im] using boundaryPosition_im_zero hdim x o z j
  rcases (positions_eq_iff hdim x o ho z _ _).mp he with he | he
  · cases he
  · exact hempty j he.1

def physicalSlot : Fin (m + 1) :=
  OrderedBoundaryGap.slot (boundaryValues hdim x o z)
    (boundaryValues_strictMono hdim x o ho z hempty)
    (RealForestCoarsePositions.center hdim x o z)
    (boundaryValues_ne_center hdim x o ho z hempty a ha)

theorem physicalSlot_isGap :
    IsGap (boundaryValues hdim x o z) (RealForestCoarsePositions.center hdim x o z)
      (physicalSlot hdim x o ho z hempty a ha) :=
  OrderedBoundaryGap.slot_isGap _ _ _ _

theorem physicalSlot_empty_block :
    boundaryClusterBlock (physicalSlot hdim x o ho z hempty a ha)
      (physicalSlot hdim x o ho z hempty a ha) = ∅ :=
  OrderedBoundaryGap.slot_empty_block _ _ _ _

include ho hempty ha in
theorem existsUnique_physicalSlot :
    ∃! s : Fin (m + 1),
      IsGap (boundaryValues hdim x o z) (RealForestCoarsePositions.center hdim x o z) s :=
  OrderedBoundaryGap.existsUnique_gap _ (boundaryValues_strictMono hdim x o ho z hempty) _
    (boundaryValues_ne_center hdim x o ho z hempty a ha)

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSlot
