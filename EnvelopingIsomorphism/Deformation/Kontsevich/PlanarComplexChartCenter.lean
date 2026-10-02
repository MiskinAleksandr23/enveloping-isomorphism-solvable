import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexPhaseCoordinates

/-! Exact agreement of the actual extracted native chart center with the
corner center of the independent complex forest coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexChartCenter

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open PlanarClusterFrames PlanarComplexForestCharts PlanarComplexPhaseCoordinates
open ExtractedMarkedFrameLimits ForestChildShapeDecomposition ComplexForestFreeShapes
open InteriorFiberAngleSplit
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

def nativeCenter : NativeParameters a x := (ForestChartOpenImage.sourcePoint a x).val

theorem normal_radius_zero (v : Normal a x hx) : radius a x hx (nativeCenter a x) v.val = 0 := by
  have hv := (ComplexForestNormalizedCharts.mem_normalNodes _ v.val).mp v.property
  have hv0 : v.val.val ≠ ⊥ := ne_of_gt ((root_covBy_upper a x hx).lt.trans_le v.val.property)
  have hn : ¬IsMax v.val.val := fun h => hv.2 ((PlanarComplexForestCharts.isMax_iff a x hx v.val).mpr h)
  change SubtreeForestInsertion.radius (tree a x) (upperNode a x hx) (limitingRadii a x) v.val = 0
  rw [SubtreeForestInsertion.radius_nonroot _ _ _ _ hv.1]
  simp only [limitingRadii, if_neg hv0,
    if_pos (ExtractedForestIdentification.nonleaf_large a x v.val.val hn)]

theorem coordinates_normal_zero : (coordinates a x hx (nativeCenter a x)).1 = 0 := by
  funext v
  have hv := (ComplexForestNormalizedCharts.mem_normalNodes _ v.val).mp v.property
  change ComplexForestInsertion.complexWeight _ _ _ v.val = 0
  rw [ComplexForestInsertion.complexWeight, if_neg hv.1, normal_radius_zero a x hx v,
    Complex.ofReal_zero, zero_mul, zero_div]

theorem limiting_child_ratio (v : Parent (upperTree a x hx)) (u : Child (upperTree a x hx) v.val) :
    limitingIncrements a x u.val.val /
      limitingIncrements a x ((marks a x hx).reference v).val.val =
      (nativeChild a x hx v u - nativeChild a x hx v ((marks a x hx).anchor v)) /
        childDenominator a x hx v := by
  have hzero := (normalizedShapes a x hx (nativeCenter a x) v).1
  change limitingIncrements a x ((marks a x hx).anchor v).val.val = 0 at hzero
  have hu := ExtractedForestNormalizedPoint.increment_sub_children a x v.val.val u.val.val
    ((marks a x hx).anchor v).val.val (child_covBy_native a x hx u.property)
    (child_covBy_native a x hx ((marks a x hx).anchor v).property)
  have hr := ExtractedForestNormalizedPoint.increment_sub_children a x v.val.val
    ((marks a x hx).reference v).val.val ((marks a x hx).anchor v).val.val
    (child_covBy_native a x hx ((marks a x hx).reference v).property)
    (child_covBy_native a x hx ((marks a x hx).anchor v).property)
  rw [hzero, sub_zero] at hu hr
  rw [hu, hr, div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr (ExtractedMarkedFrameLimits.leadingRadius_pos a x v.val.val).ne')]
  rfl

theorem coordinates_free_center : (coordinates a x hx (nativeCenter a x)).2 = centerFree a x hx := by
  funext e
  change limitingIncrements a x e.2.val.val.val / phase a x hx (nativeCenter a x) e.1.val = _
  have hphase : phase a x hx (nativeCenter a x) e.1.val =
      limitingIncrements a x ((marks a x hx).reference e.1).val.val := by
    unfold phase ComplexForestPhaseCoordinates.nativePhase
    rw [dif_neg e.1.property]
    rfl
  rw [hphase]
  exact limiting_child_ratio a x hx e.1 e.2.val

/-- The center of every actual fiber chart maps to the corner whose bounded
complex unit neighborhoods were constructed from the extracted shape data. -/
theorem coordinates_center : coordinates a x hx (nativeCenter a x) = (0, centerFree a x hx) :=
  Prod.ext (coordinates_normal_zero a x hx) (coordinates_free_center a x hx)

theorem coordinates_sourcePoint : coordinates a x hx (ForestChartOpenImage.sourcePoint a x).val =
    (0, centerFree a x hx) := coordinates_center a x hx

theorem coordinates_inverse_self :
    coordinates a x hx (ForestChartOpenImage.inverse a x ⟨x, ForestChartOpenImage.self_mem_target a x⟩).val =
      (0, centerFree a x hx) := by
  have h := ForestChartOpenImage.inverse_forward a x (ForestChartOpenImage.sourcePoint a x)
    (ForestChartOpenImage.sourcePoint_mem_source a x)
  simp only [ForestChartOpenImage.forward_sourcePoint] at h
  rw [h, coordinates_sourcePoint]

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexChartCenter
