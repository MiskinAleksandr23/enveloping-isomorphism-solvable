import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexForestCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestPhaseCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarSubtreeCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarOriginalStratum

/-! Exact native planar-fiber insertion in the independent complex forest chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexPhaseCoordinates

open Configuration ExtractedForestParameters ExtractedForestFrames PlanarClusterFrames
open PlanarComplexForestCharts ForestChildShapeDecomposition ComplexForestPhaseCoordinates
open InteriorFiberAngleSplit ForestInsertionDifference
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

abbrev NativeParameters := ForestChartOpenImage.ParameterSpace a x

def radius (p : NativeParameters a x) : upperTree a x hx → ℝ :=
  SubtreeForestInsertion.radius (tree a x) (upperNode a x hx) p.val.1

@[simp] theorem radius_root (p : NativeParameters a x) : radius a x hx p ⊥ = 1 :=
  SubtreeForestInsertion.radius_root (tree a x) (upperNode a x hx) p.val.1

def increment (p : NativeParameters a x) : upperTree a x hx → ℂ :=
  SubtreeForestInsertion.increment (tree a x) (upperNode a x hx) p.val.2

theorem normalizedShapes (p : NativeParameters a x) :
    NormalizedShapes (upperTree a x hx) (marks a x hx) (increment a x hx p) := by
  intro v
  have hv0 : (parent a x hx v).val ≠ ⊥ :=
    ne_of_gt ((root_covBy_upper a x hx).lt.trans_le v.val.property)
  have h := p.property.2.1 (parent a x hx v).val (parent a x hx v).property
  rw [frames_nonroot a x hx _ hv0 (parent a x hx v).property] at h
  exact h

/-- The phases are the actual native reference-child increments; no phases are supplied. -/
def phase (p : NativeParameters a x) : upperTree a x hx → ℂ :=
  nativePhase (upperTree a x hx) (marks a x hx) (increment a x hx p)

theorem phase_ne_zero (p : NativeParameters a x) (v : upperTree a x hx) : phase a x hx p v ≠ 0 :=
  nativePhase_ne_zero _ _ _ (normalizedShapes a x hx p) v

theorem norm_phase (p : NativeParameters a x) (v : upperTree a x hx) : ‖phase a x hx p v‖ = 1 :=
  norm_nativePhase _ _ _ (normalizedShapes a x hx p) v

def coordinates (p : NativeParameters a x) : Coordinates a x hx :=
  phaseCoordinates (upperTree a x hx) (marks a x hx) (radius a x hx p) (phase a x hx p) (increment a x hx p)

theorem nativeMarks (p : NativeParameters a x) :
    NativeMarks (upperTree a x hx) (marks a x hx) (phase a x hx p) (increment a x hx p) :=
  nativeMarks_nativePhase _ _ _ (normalizedShapes a x hx p)

/-- The old native residual insertion, including the collapsed upper radius,
equals the actual complex insertion times only its root rotation. -/
theorem branchUnit_eq_complexCartesian (p : NativeParameters a x) (v : upperTree a x hx) :
    branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx) v.val =
      phase a x hx p ⊥ *
        ComplexForestInsertion.complexCartesian (upperTree a x hx)
          (ComplexForestNormalizedCharts.includeParameters (upperTree a x hx)
            (ComplexForestFreeShapes.parameters (upperTree a x hx) (marks a x hx) (coordinates a x hx p))) v := by
  rw [← SubtreeForestInsertion.position_eq_branchUnit (tree a x) (upperNode a x hx) p.val.1 p.val.2 v]
  have h := position_phaseCoordinates (upperTree a x hx) (marks a x hx)
    (radius a x hx p) (phase a x hx p) (increment a x hx p)
    (phase_ne_zero a x hx p) (nativeMarks a x hx p) v
  rw [radius_root, Complex.ofReal_one, one_mul] at h
  simpa only [upperTree, SubtreeForestInsertion.Tree, radius, increment, coordinates] using h

/-- Actual normalized original pair ratios on the planar fiber agree with the
complex chart ratios; the native collapsed upper scale is never divided out. -/
theorem native_pairRatio_eq_chart (p : NativeParameters a x)
    (hp : coordinates a x hx p ∈ chartDomain a x hx) (j k b c : Point N) :
    (branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx) (leaf a x hx k).val -
      branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx) (leaf a x hx j).val) /
    (branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx) (leaf a x hx c).val -
      branchUnit (tree a x) p.val.1 p.val.2 (upperNode a x hx) (leaf a x hx b).val) =
      shapeDifference j k (chart a x hx (coordinates a x hx p)) /
        shapeDifference b c (chart a x hx (coordinates a x hx p)) := by
  simp only [← SubtreeForestInsertion.position_eq_branchUnit (tree a x) (upperNode a x hx) p.val.1 p.val.2]
  exact normalized_pairRatio_phaseCoordinates (upperTree a x hx) (marks a x hx) (leaf a x hx)
    (leaf_injective a x hx) (radius a x hx p) (phase a x hx p) (increment a x hx p)
    (phase_ne_zero a x hx p) (nativeMarks a x hx p)
    (by rw [radius_root]; exact one_ne_zero) hp j k b c

/-- Actual native positive-stratum parameters land in the genuine punctured
complex chart, using the native source's proved unit and positivity conditions. -/
theorem coordinates_mem_chartDomain (p : ForestChartOpenImage.Source a x)
    (hp : PlanarSubtreeCoordinates.PositiveBelowUpper a x hx p.val) :
    coordinates a x hx p.val ∈ chartDomain a x hx := by
  apply phaseCoordinates_mem_chartDomain (upperTree a x hx) (marks a x hx) (leaf a x hx)
    (radius a x hx p.val) (phase a x hx p.val) (increment a x hx p.val)
    (phase_ne_zero a x hx p.val) (nativeMarks a x hx p.val)
  · intro v
    exact (PlanarSubtreeCoordinates.radius_pos a x hx p.val hp v.val).ne'
  · exact PlanarSubtreeCoordinates.positions_injective a x hx p hp

/-- Complete native-to-complex ratio matching on the actual positive planar
stratum: the chart-domain condition is derived from native data. -/
theorem native_pairRatio_eq_chart_positive (p : ForestChartOpenImage.Source a x)
    (hp : PlanarSubtreeCoordinates.PositiveBelowUpper a x hx p.val) (j k b c : Point N) :
    (PlanarSubtreeCoordinates.positions a x hx p.val k - PlanarSubtreeCoordinates.positions a x hx p.val j) /
      (PlanarSubtreeCoordinates.positions a x hx p.val c - PlanarSubtreeCoordinates.positions a x hx p.val b) =
      shapeDifference j k (chart a x hx (coordinates a x hx p.val)) /
        shapeDifference b c (chart a x hx (coordinates a x hx p.val)) := by
  simp only [PlanarSubtreeCoordinates.positions_eq_branchUnit]
  exact native_pairRatio_eq_chart a x hx p.val (coordinates_mem_chartDomain a x hx p hp) j k b c

theorem continuous_radius (v : upperTree a x hx) : Continuous (fun p : NativeParameters a x ↦ radius a x hx p v) := by
  unfold radius SubtreeForestInsertion.radius
  split_ifs <;> fun_prop

theorem continuous_increment (v : upperTree a x hx) : Continuous (fun p : NativeParameters a x ↦ increment a x hx p v) := by
  unfold increment SubtreeForestInsertion.increment
  fun_prop

theorem continuous_phase (v : upperTree a x hx) : Continuous (fun p : NativeParameters a x ↦ phase a x hx p v) := by
  unfold phase nativePhase
  split_ifs
  · exact continuous_const
  · exact continuous_increment a x hx _

/-- The actual coordinate conversion is continuous across every native zero
radius. This pulls bounded complex neighborhoods back to genuine forest neighborhoods. -/
theorem continuous_coordinates : Continuous (coordinates a x hx) := by
  unfold coordinates phaseCoordinates
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    have hv : v.val ≠ ⊥ := (ComplexForestNormalizedCharts.mem_normalNodes _ v.val).mp v.property |>.1
    simp only [ComplexForestInsertion.complexWeight, if_neg hv]
    exact ((Complex.continuous_ofReal.comp (continuous_radius a x hx v.val)).mul
      (continuous_phase a x hx v.val)).div (continuous_phase a x hx (Order.pred v.val))
        (fun p ↦ phase_ne_zero a x hx p _)
  · apply continuous_pi
    intro e
    exact (continuous_increment a x hx e.2.val.val).div (continuous_phase a x hx e.1.val)
      (fun p ↦ phase_ne_zero a x hx p _)

/-- Literal original normalized planar pair ratios in the actual complex chart.
Positivity and chart-domain membership are obtained from the original-point identity. -/
theorem original_pairRatio_eq_chart (b : Point N) (hab : a ≠ b)
    (p : ForestChartOpenImage.Source a x)
    (hp : ForestChartOpenImage.forward a x p ∈ ForestChartOpenImage.referenceRegion a x)
    (z : PlanarClusterCompactification.Normalized a b)
    (hz : PlanarClusterFiber.projection a b hab (ForestChartOpenImage.forward a x p) =
      PlanarClusterCompactification.embedding a b z) (j k c d : Point N) :
    (z.val k - z.val j) / (z.val d - z.val c) =
      shapeDifference j k (chart a x hx (coordinates a x hx p.val)) /
        shapeDifference c d (chart a x hx (coordinates a x hx p.val)) := by
  have hpositive := (PlanarOriginalStratum.original_iff_positiveBelowUpper a x hx b hab p hp).mp ⟨z, hz⟩
  rw [PlanarOriginalStratum.original_eq_normalized a x hx b hab p hp z hz]
  change ((_ - _) / (PlanarSubtreeCoordinates.referenceRadius a x hx b p.val : ℂ) -
      (_ - _) / (PlanarSubtreeCoordinates.referenceRadius a x hx b p.val : ℂ)) /
      ((_ - _) / (PlanarSubtreeCoordinates.referenceRadius a x hx b p.val : ℂ) -
      (_ - _) / (PlanarSubtreeCoordinates.referenceRadius a x hx b p.val : ℂ)) = _
  rw [← sub_div, ← sub_div,
    div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr
      (PlanarSubtreeCoordinates.referenceRadius_pos a x hx b hab p hpositive).ne')]
  have hcancel (s t : Point N) :
      (PlanarSubtreeCoordinates.positions a x hx p.val t - PlanarSubtreeCoordinates.positions a x hx p.val a) -
        (PlanarSubtreeCoordinates.positions a x hx p.val s - PlanarSubtreeCoordinates.positions a x hx p.val a) =
      PlanarSubtreeCoordinates.positions a x hx p.val t - PlanarSubtreeCoordinates.positions a x hx p.val s := by abel
  rw [hcancel j k, hcancel c d]
  exact native_pairRatio_eq_chart_positive a x hx p hpositive j k c d

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexPhaseCoordinates
