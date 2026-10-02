import EnvelopingIsomorphism.Deformation.Kontsevich.BoundedPlanarComplexCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexChartCenter

/-! An actual finite cover of X_N by bounded complex forest charts, obtained
from compactness of the original planar DR closure and the literal native decoder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.FinitePlanarComplexChartCover

open Configuration InteriorFiberAngleSplit PlanarComplexForestCharts
open PlanarComplexPhaseCoordinates PlanarClusterFiber Topology
open scoped Classical

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : IsFiber a x)

def localCoordinates (y : ForestChartOpenImage.target a x) : Coordinates a x hx :=
  coordinates a x hx (ForestChartOpenImage.inverse a x y).val

theorem continuous_localCoordinates : Continuous (localCoordinates a x hx) :=
  (continuous_coordinates a x hx).comp (continuous_subtype_val.comp (ForestChartOpenImage.continuous_inverse a x))

def nativeNeighborhood : Set (Compactification a 0) :=
  Subtype.val '' (localCoordinates a x hx ⁻¹' BoundedPlanarComplexCharts.ball a x hx)

theorem isOpen_nativeNeighborhood : IsOpen (nativeNeighborhood a x hx) :=
  (ForestChartOpenImage.isOpen_target a x).isOpenMap_subtype_val _
    (Metric.isOpen_ball.preimage (continuous_localCoordinates a x hx))

theorem self_mem_nativeNeighborhood : x ∈ nativeNeighborhood a x hx := by
  refine ⟨⟨x, ForestChartOpenImage.self_mem_target a x⟩, ?_, rfl⟩
  change coordinates a x hx (ForestChartOpenImage.inverse a x ⟨x, _⟩).val ∈ BoundedPlanarComplexCharts.ball a x hx
  rw [PlanarComplexChartCenter.coordinates_inverse_self a x hx]
  exact Metric.mem_ball_self (BoundedPlanarComplexCharts.radius_pos a x hx)

theorem nativeNeighborhood_data {y : Compactification a 0} (hy : y ∈ nativeNeighborhood a x hx) :
    ∃ p : ForestChartOpenImage.Source a x,
      ForestChartOpenImage.forward a x p = y ∧
      ForestChartOpenImage.forward a x p ∈ ForestChartOpenImage.referenceRegion a x ∧
      coordinates a x hx p.val ∈ BoundedPlanarComplexCharts.ball a x hx := by
  obtain ⟨y, hy, rfl⟩ := hy
  refine ⟨ForestChartOpenImage.inverse a x y, ForestChartOpenImage.forward_inverse a x y, ?_, hy⟩
  rw [ForestChartOpenImage.forward_inverse]
  exact y.property.1

abbrev CompactPlanar (N : ℕ) := PlanarClusterCompactification.Space (0 : Point N) 1

def fiberPoint (z : CompactPlanar N) : Fiber (0 : Point N) :=
  homeomorph 0 1 Fin.zero_ne_one z

def neighborhood (z : CompactPlanar N) : Set (CompactPlanar N) :=
  (fun y ↦ (fiberPoint y).val) ⁻¹' nativeNeighborhood 0 (fiberPoint z).val (fiberPoint z).property

theorem isOpen_neighborhood (z : CompactPlanar N) : IsOpen (neighborhood z) :=
  (isOpen_nativeNeighborhood _ _ _).preimage (continuous_subtype_val.comp (homeomorph 0 1 Fin.zero_ne_one).continuous)

theorem self_mem_neighborhood (z : CompactPlanar N) : z ∈ neighborhood z :=
  self_mem_nativeNeighborhood _ _ _

/-- The small bounded neighborhoods are constructed first, then compactness
selects finitely many of these actual neighborhoods. -/
theorem finite_native_cover : ∃ centers : Finset (CompactPlanar N),
    ∀ z : CompactPlanar N, ∃ c ∈ centers, z ∈ neighborhood c := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun c : CompactPlanar N ↦ neighborhood c)
    isOpen_neighborhood (fun z hz ↦ Set.mem_iUnion.mpr ⟨z, self_mem_neighborhood z⟩)
  refine ⟨s, fun z ↦ ?_⟩
  simpa only [Set.mem_iUnion, exists_prop] using hs (Set.mem_univ z)

abbrev LocalCoordinates (c : CompactPlanar N) := Coordinates 0 (fiberPoint c).val (fiberPoint c).property

def chartAt (c : CompactPlanar N) : LocalCoordinates c → Shape N :=
  chart 0 (fiberPoint c).val (fiberPoint c).property

def domainAt (c : CompactPlanar N) : Set (LocalCoordinates c) :=
  BoundedPlanarComplexCharts.ball 0 (fiberPoint c).val (fiberPoint c).property ∩
    chartDomain 0 (fiberPoint c).val (fiberPoint c).property

def originalPoint (η : PlanarNormalizedCoordinates.Configuration N) : CompactPlanar N :=
  PlanarClusterCompactification.embedding 0 1 (PlanarNormalizedCoordinates.ofCoordinates (1, η))

theorem chart_covers_original (c : CompactPlanar N) (η : PlanarNormalizedCoordinates.Configuration N)
    (hη : originalPoint η ∈ neighborhood c) : η.val ∈ chartAt c '' domainAt c := by
  let x := (fiberPoint c).val
  let hx := (fiberPoint c).property
  obtain ⟨p, hp, hpRef, hball⟩ := nativeNeighborhood_data 0 x hx hη
  have hproj : projection 0 1 Fin.zero_ne_one (ForestChartOpenImage.forward 0 x p) = originalPoint η := by
    rw [hp]
    exact (homeomorph 0 1 Fin.zero_ne_one).symm_apply_apply (originalPoint η)
  have hpositive := (PlanarOriginalStratum.original_iff_positiveBelowUpper 0 x hx 1 Fin.zero_ne_one p hpRef).mp
    ⟨PlanarNormalizedCoordinates.ofCoordinates (1, η), hproj⟩
  have hdomain := coordinates_mem_chartDomain 0 x hx p hpositive
  refine ⟨coordinates 0 x hx p.val, ⟨hball, hdomain⟩, ?_⟩
  funext j
  have he := original_pairRatio_eq_chart 0 x hx 1 Fin.zero_ne_one p hpRef
    (PlanarNormalizedCoordinates.ofCoordinates (1, η)) hproj 0 j.succ.succ 0 1
  simpa only [shapeDifference, normalizedPoint_anchor, normalizedPoint_reference, sub_zero, div_one,
    PlanarNormalizedCoordinates.ofCoordinates, PlanarNormalizedCoordinates.restore, Circle.coe_one,
    one_mul, sub_self, normalizedPoint_free, chartAt, x, hx] using he.symm

/-- A concrete finite cover of the entire original X_N by images of bounded
punctured complex forest domains. No finite-cover premise is assumed. -/
theorem finite_complex_cover : ∃ centers : Finset (CompactPlanar N),
    ∀ η : PlanarNormalizedCoordinates.Configuration N, ∃ c ∈ centers, η.val ∈ chartAt c '' domainAt c := by
  obtain ⟨s, hs⟩ := finite_native_cover (N := N)
  refine ⟨s, fun η ↦ ?_⟩
  obtain ⟨c, hc, hη⟩ := hs (originalPoint η)
  exact ⟨c, hc, chart_covers_original c η hη⟩

theorem isOpen_domainAt (c : CompactPlanar N) : IsOpen (domainAt c) :=
  Metric.isOpen_ball.inter (PlanarComplexForestCharts.isOpen_chartDomain _ _ _)

theorem isBounded_domainAt (c : CompactPlanar N) : Bornology.IsBounded (domainAt c) :=
  Metric.isBounded_ball.subset Set.inter_subset_left

theorem chartAt_mapsTo_configuration (c : CompactPlanar N) :
    Set.MapsTo (chartAt c) (domainAt c) (shapeConfiguration N) :=
  fun _ hz ↦ chart_mem_configuration _ _ _ hz.2

theorem chartAt_injOn (c : CompactPlanar N) : Set.InjOn (chartAt c) (domainAt c) :=
  (openPartialHomeomorph _ _ _).injOn.mono Set.inter_subset_right

theorem analyticOnNhd_chartAt (c : CompactPlanar N) :
    AnalyticOnNhd ℂ (chartAt c) (domainAt c) :=
  (analyticOnNhd_chart _ _ _).mono Set.inter_subset_right

def localChart (c : CompactPlanar N) : OpenPartialHomeomorph (LocalCoordinates c) (Shape N) :=
  (openPartialHomeomorph 0 (fiberPoint c).val (fiberPoint c).property).restrOpen
    (BoundedPlanarComplexCharts.ball 0 (fiberPoint c).val (fiberPoint c).property) Metric.isOpen_ball

@[simp] theorem localChart_source (c : CompactPlanar N) : (localChart c).source = domainAt c := by
  rw [localChart, OpenPartialHomeomorph.restrOpen_source, openPartialHomeomorph_source]
  exact Set.inter_comm _ _

@[simp] theorem localChart_apply (c : CompactPlanar N) (z : LocalCoordinates c) : localChart c z = chartAt c z := rfl

theorem localChart_target (c : CompactPlanar N) : (localChart c).target = chartAt c '' domainAt c := by
  rw [← (localChart c).image_source_eq_target, localChart_source]
  rfl

theorem isOpen_image_chartAt (c : CompactPlanar N) : IsOpen (chartAt c '' domainAt c) := by
  rw [← localChart_target]
  exact (localChart c).open_target

theorem local_uniform_unit_bounds (c : CompactPlanar N) (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ domainAt c,
      ‖unit 0 (fiberPoint c).val (fiberPoint c).property j k b d z‖ ≤ C ∧
      ‖(unit 0 (fiberPoint c).val (fiberPoint c).property j k b d z)⁻¹‖ ≤ C ∧
      ‖fderiv ℂ (unit 0 (fiberPoint c).val (fiberPoint c).property j k b d) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := BoundedPlanarComplexCharts.uniform_unit_bounds 0
    (fiberPoint c).val (fiberPoint c).property j k b d hjk hbd
  exact ⟨C, hC, fun z hz ↦ hbound z hz.1⟩

theorem chartAt_pairRatio_monomial (c : CompactPlanar N) {z : LocalCoordinates c} (hz : z ∈ domainAt c)
    (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d) :
    shapeDifference j k (chartAt c z) / shapeDifference b d (chartAt c z) =
      (∏ v : PlanarComplexForestCharts.Normal 0 (fiberPoint c).val (fiberPoint c).property,
        z.1 v ^ exponent 0 (fiberPoint c).val (fiberPoint c).property j k b d v) *
        unit 0 (fiberPoint c).val (fiberPoint c).property j k b d z :=
  ComplexForestFreeShapes.chart_pairRatio_monomial _ _ _
    (leaf_injective _ _ _) hz.2 j k b d hjk hbd

theorem chartAt_pairDifference_monomial (c : CompactPlanar N) {z : LocalCoordinates c} (hz : z ∈ domainAt c)
    (j k : Point N) (hjk : j ≠ k) :
    shapeDifference j k (chartAt c z) =
      (∏ v : PlanarComplexForestCharts.Normal 0 (fiberPoint c).val (fiberPoint c).property,
        z.1 v ^ exponent 0 (fiberPoint c).val (fiberPoint c).property j k 0 1 v) *
        unit 0 (fiberPoint c).val (fiberPoint c).property j k 0 1 z := by
  simpa [shapeDifference] using chartAt_pairRatio_monomial c hz j k 0 1 hjk Fin.zero_ne_one

end EnvelopingIsomorphism.Deformation.Kontsevich.FinitePlanarComplexChartCover
