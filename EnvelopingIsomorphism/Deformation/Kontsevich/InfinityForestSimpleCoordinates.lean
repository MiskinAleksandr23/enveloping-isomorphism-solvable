import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestResolvedCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinitySmoothForms

/-! Explicit smooth native-forest-to-infinity-face coordinates. The only
absolute-value denominator is the actual nonzero outside-anchor gap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCoordinates
open Configuration ForestRadialFaceClassification BoxStokes
open RealForestSimpleCoordinates (coarsePosition shapePosition centerPosition contDiff_coarsePosition contDiff_shapePosition contDiff_centerPosition)
open InfinityForestSimpleCluster (lower upper)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x) (q : Fin m)

def offset (j : Fin m) (y : Coord r) : ℝ :=
  (coarsePosition hdim x o (Sum.inl (Sum.inr j)) y).re - centerPosition hdim x o y

def coordinates (y : Coord r) : BoundaryAnchoredInfinityFreeCoordinates.FaceCoordinates (0 : Fin (n+1)) m q :=
  (fun j ↦ RealForestSimpleCluster.normalize (shapePosition hdim x o (Sum.inl (Sum.inl 0)) y)
      (shapePosition hdim x o (Sum.inl (Sum.inl j.val)) y),
   fun j ↦ if j.val ∈ boundaryClusterBlock (lower x o) (upper x o) then
      RealForestSimpleCluster.normalizeReal (shapePosition hdim x o (Sum.inl (Sum.inl 0)) y)
        (shapePosition hdim x o (Sum.inl (Sum.inr j.val)) y).re
    else offset hdim x o j.val y / |offset hdim x o q y|)

theorem contDiff_offset (j : Fin m) : ContDiff ℝ ⊤ (offset hdim x o j) :=
  (Complex.reCLM.contDiff.comp (contDiff_coarsePosition hdim x o _)).sub (contDiff_centerPosition hdim x o)

variable (ho : kind 0 x o = .infinity)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho hq hne in
theorem contDiffAt_coordinates : ContDiffAt ℝ ⊤ (coordinates hdim x o q) z.val := by
  have hs := (contDiff_shapePosition hdim x o (Sum.inl (Sum.inl 0))).contDiffAt (x := z.val)
  have hp : 0 < (shapePosition hdim x o (Sum.inl (Sum.inl 0)) z.val).im :=
    InfinityForestSimpleCluster.shapeAnchor_pos hdim x o ho z
  have hg : 0 < |offset hdim x o q z.val| :=
    InfinityForestSimpleCluster.coarseScale_pos hdim x o ho q hq hne z
  have hg' : offset hdim x o q z.val ≠ 0 := abs_pos.mp hg
  have hnorm : ContDiffAt ℝ ⊤ (fun w ↦ |offset hdim x o q w|) z.val := by
    simpa only [Real.norm_eq_abs] using (contDiff_offset hdim x o q).contDiffAt.norm ℝ hg'
  unfold coordinates
  refine (contDiffAt_pi.mpr fun j ↦ RealForestSimpleCoordinates.smooth_normalize hs
    (contDiff_shapePosition hdim x o _).contDiffAt hp).prodMk (contDiffAt_pi.mpr fun j ↦ ?_)
  split_ifs
  · exact RealForestSimpleCoordinates.smooth_normalizeReal hs
      (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiff_shapePosition hdim x o _).contDiffAt) hp
  · exact (contDiff_offset hdim x o j.val).contDiffAt.div hnorm hg.ne'

theorem coordinates_eq_freeDomain :
    BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val) =
      (InfinityForestSimpleCluster.freeDomain hdim x o ho q hq hne z).val := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j
      change (if j.val ∈ boundaryClusterBlock (lower x o) (upper x o) then _ else _) =
        (if j.val ∈ boundaryClusterBlock (lower x o) (upper x o) then
          InfinityForestSimpleCluster.boundaryVelocity hdim x o z j.val
        else InfinityForestSimpleCluster.boundaryBase hdim x o q z j.val)
      by_cases hj : j.val ∈ boundaryClusterBlock (lower x o) (upper x o)
      · rw [if_pos hj, if_pos hj, InfinityForestSimpleCluster.boundaryVelocity, if_pos hj]
        rfl
      · rw [if_neg hj, if_neg hj]
        rfl
    · rfl

include ho hq hne in
theorem coordinates_mem_source :
    (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val)).OpenConditions
      (lower x o) (upper x o) := by
  rw [coordinates_eq_freeDomain hdim x o q ho hq hne z]
  exact (InfinityForestSimpleCluster.freeDomain hdim x o ho q hq hne z).property.2

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCoordinates
