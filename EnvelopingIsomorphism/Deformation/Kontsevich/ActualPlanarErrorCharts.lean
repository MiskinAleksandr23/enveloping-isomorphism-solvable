import EnvelopingIsomorphism.Deformation.Kontsevich.FlattenedPlanarComplexCharts
import EnvelopingIsomorphism.Deformation.Kontsevich.MonomialLocalDataBuilder
import EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoffGlobalDomination

/-! Concrete bounded monomial error charts from the actual compact planar forest cover.
All local geometric and unit hypotheses are discharged by the native complex charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarErrorCharts
open InteriorFiberAngleSplit RatioCutoffStokes NormalCrossingStokes
open FinitePlanarComplexChartCover
open scoped Classical BigOperators
variable {N : ℕ}

/-- The edge associated to an actual signed ratio differential. -/
def radialPair {M : ℕ} : RatioCutoff.RadialIndex M → Point M × Point M :=
  Sum.elim (fun t ↦ (t.val.1, t.val.2.1)) (fun t ↦ (t.val.1, t.val.2.2))

theorem radialPair_distinct {M : ℕ} (k : RatioCutoff.RadialIndex M) :
    (radialPair k).1 ≠ (radialPair k).2 := by
  cases k with
  | inl t => exact t.property.1
  | inr t => exact t.property.2

theorem radialFunction_eq {M : ℕ} (k : RatioCutoff.RadialIndex M) :
    RatioCutoff.radialFunction k = shapeDifference (radialPair k).1 (radialPair k).2 := by
  cases k <;> rfl

variable (e : RatioCutoffStokes.Edges N) (he : ∀ j, (e j).1 ≠ (e j).2)
variable (c : CompactPlanar (N + 1))

private theorem domain_polydisc : ∃ R : ℝ,
    FlattenedPlanarComplexCharts.domain c ⊆ NormalCrossing.puncturedPolydisc (fun _ ↦ R) := by
  obtain ⟨R, hR⟩ := (FlattenedPlanarComplexCharts.isBounded_domain c).exists_norm_le
  refine ⟨R + 1, fun z hz i hi ↦ ⟨?_, ?_⟩⟩
  · exact norm_pos_iff.mpr (FlattenedPlanarComplexCharts.domain_coordinates_ne_zero c hz i)
  · exact (norm_le_pi_norm z i).trans_lt (lt_of_le_of_lt (hR z hz) (by linarith))

def monomial : BoundedLogMonomialCombination.LocalData (Fin (N + 1))
    (RatioCutoff.RadialIndex (N + 1)) (Degree N) :=
  BoundedLogMonomialCombination.LocalData.ofUnitBounds
    (fun j ↦ FlattenedPlanarComplexCharts.exponent c (e j).1 (e j).2 0 1)
    (fun k ↦ FlattenedPlanarComplexCharts.exponent c (radialPair k).1 (radialPair k).2 0 1)
    (fun j ↦ FlattenedPlanarComplexCharts.unit c (e j).1 (e j).2 0 1)
    (fun k ↦ FlattenedPlanarComplexCharts.unit c (radialPair k).1 (radialPair k).2 0 1)
    (fun _ ↦ (domain_polydisc c).choose)
    (FlattenedPlanarComplexCharts.domain c)
    (FlattenedPlanarComplexCharts.isOpen_domain c).measurableSet
    (domain_polydisc c).choose_spec
    (FlattenedPlanarComplexCharts.domain c)
    (FlattenedPlanarComplexCharts.isOpen_domain c) (Set.Subset.refl _)
    (fun j x hx ↦ (((FlattenedPlanarComplexCharts.analyticOnNhd_unit c (e j).1 (e j).2 0 1
      (he j) Fin.zero_ne_one) x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt)
    (fun k x hx ↦ (((FlattenedPlanarComplexCharts.analyticOnNhd_unit c (radialPair k).1 (radialPair k).2 0 1
      (radialPair_distinct k) Fin.zero_ne_one) x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt)
    (fun j _ hx ↦ FlattenedPlanarComplexCharts.unit_ne_zero c _ _ _ _ (he j) Fin.zero_ne_one hx)
    (fun k _ hx ↦ FlattenedPlanarComplexCharts.unit_ne_zero c _ _ _ _ (radialPair_distinct k) Fin.zero_ne_one hx)
    (fun j ↦ FlattenedPlanarComplexCharts.uniform_unit_bounds c _ _ _ _ (he j) Fin.zero_ne_one)
    (fun k ↦ FlattenedPlanarComplexCharts.uniform_unit_bounds c _ _ _ _ (radialPair_distinct k) Fin.zero_ne_one)

/-- This chart contains only proved native geometry; no local L1 or error bound is assumed. -/
def chart : RatioCutoffGlobalDomination.ErrorChart e where
  monomial := monomial e he c
  map := FlattenedPlanarComplexCharts.chart c
  map_C1 x hx := ((FlattenedPlanarComplexCharts.analyticOnNhd_chart c x hx).contDiffAt).restrict_scalars ℝ
  map_injective := FlattenedPlanarComplexCharts.chart_injOn c
  image_open := FlattenedPlanarComplexCharts.isOpen_chart_image c
  image_configuration := by
    rintro z ⟨y, hy, rfl⟩
    exact FlattenedPlanarComplexCharts.chart_mapsTo c hy
  identitySet := FlattenedPlanarComplexCharts.domain c
  identity_open := FlattenedPlanarComplexCharts.isOpen_domain c
  region_identity := Set.Subset.refl _
  base_identity j y hy := by
    change shapeDifference (e j).1 (e j).2 (FlattenedPlanarComplexCharts.chart c y) =
      LogMonomial.value (FlattenedPlanarComplexCharts.exponent c (e j).1 (e j).2 0 1)
        (FlattenedPlanarComplexCharts.unit c (e j).1 (e j).2 0 1 y) y
    rw [FlattenedPlanarComplexCharts.pairDifference_monomial c hy _ _ (he j)]
    exact mul_comm _ _
  extra_identity k y hy := by
    rw [radialFunction_eq]
    change shapeDifference (radialPair k).1 (radialPair k).2 (FlattenedPlanarComplexCharts.chart c y) =
      LogMonomial.value (FlattenedPlanarComplexCharts.exponent c (radialPair k).1 (radialPair k).2 0 1)
        (FlattenedPlanarComplexCharts.unit c (radialPair k).1 (radialPair k).2 0 1 y) y
    rw [FlattenedPlanarComplexCharts.pairDifference_monomial c hy _ _ (radialPair_distinct k)]
    exact mul_comm _ _

/-- Unconditional finite actual monomial cover of the original configuration space. -/
theorem finite_cover : ∃ centers : Finset (CompactPlanar (N + 1)),
    shapeConfiguration (N + 1) ⊆ ⋃ c ∈ centers,
      (chart e he c).map '' (chart e he c).monomial.region :=
  FlattenedPlanarComplexCharts.finite_cover

end EnvelopingIsomorphism.Deformation.Kontsevich.ActualPlanarErrorCharts
