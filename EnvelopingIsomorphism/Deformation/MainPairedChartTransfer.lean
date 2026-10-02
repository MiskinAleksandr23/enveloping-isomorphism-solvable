import EnvelopingIsomorphism.Deformation.MainPairedClusterAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestSimpleProductCover

/-! Exact pointwise transfer criterion for a fixed chart of the original
finite Stokes partition. Chart-target membership and uniqueness are proved;
the remaining zero/positive radial pattern is explicit and is not asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedChartTransfer
open Kontsevich Configuration ForestRadialFaceClassification ForestOrthantRealization
open ForestRadialFaceLocalization ForestRadialFaceReconstruction
open UniformBinaryGraphs MainScalarBoundaryAssembly
open scoped Classical

section General
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x q : Compactification (0 : Fin (n+1)) m) (S : Finset (Fin (n+1)))

/-- The actual inverse of this specified original forest chart. -/
def decodedAmbient : Ambient 0 x :=
  includeOrthant 0 x ((ForestOrthantCharts.chart 0 x).symm q)

/-- Elementary native-coordinate content of the remaining transfer: one zero
paired radius with exactly the prescribed mask, and positive other radii. -/
def DecodedPairedPattern : Prop :=
  ∃ (o : Orbit 0 x) (ho : kind 0 x o = .paired),
    PairedForestSimpleCluster.S x o ho = S ∧
    (decodedAmbient x q).1 (orbitEquiv 0 x o) = 0 ∧
    ∀ o' : Orbit 0 x, o' ≠ o → 0 < (decodedAmbient x q).1 (orbitEquiv 0 x o')

/-- The desired original-chart source and literal represented physical point. -/
def HasPairedSource : Prop :=
  ∃ (o : Orbit 0 x) (ho : kind 0 x o = .paired) (z : source hdim x o),
    PairedForestSimpleCluster.S x o ho = S ∧ PairedForestSimpleOverlap.facePoint hdim x o z = q

/-- At a native face point, the full inverse of the original chart is exactly
its included face coordinates. -/
theorem decodedAmbient_eq_faceAmbient (o : Orbit 0 x) (z : source hdim x o)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z = q) :
    decodedAmbient x q = faceAmbient hdim x o z.val := by
  rw [decodedAmbient, ← hz, PairedForestSimpleOverlap.facePoint,
    (ForestOrthantCharts.chart 0 x).left_inv z.property.2,
    ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x _
      (faceAmbient_nonneg hdim x o z.val z.property.1)]

/-- Necessary and sufficient transfer criterion in each SPECIFIED forest
chart, rather than only in the chart centered at q. -/
theorem hasPairedSource_iff_decodedPattern
    (hq : q ∈ (ForestOrthantCharts.chart 0 x).target) :
    HasPairedSource hdim x q S ↔ DecodedPairedPattern x q S := by
  constructor
  · rintro ⟨o,ho,z,hS,hz⟩
    refine ⟨o,ho,hS,?_,?_⟩
    · rw [decodedAmbient_eq_faceAmbient hdim x q o z hz, faceAmbient_selected_zero]
    · intro o' hne
      rw [decodedAmbient_eq_faceAmbient hdim x q o z hz]
      exact faceAmbient_other_positive hdim x o o' z.val z.property.1 hne
  · rintro ⟨o,ho,hS,hzero,hpos⟩
    have hchart : ForestPositiveChartSmooth.ofAmbient 0 x (decodedAmbient x q) ∈
        (ForestOrthantCharts.chart 0 x).source := by
      rw [decodedAmbient, ForestPositiveChartSmooth.ofAmbient_includeOrthant]
      exact (ForestOrthantCharts.chart 0 x).map_target hq
    obtain ⟨z,hz,_⟩ := existsUnique_source_parameter hdim x o (decodedAmbient x q) hzero hpos hchart
    refine ⟨o,ho,z,hS,?_⟩
    rw [PairedForestSimpleOverlap.facePoint, hz, decodedAmbient,
      ForestPositiveChartSmooth.ofAmbient_includeOrthant,
      (ForestOrthantCharts.chart 0 x).right_inv hq]

/-- A represented strict face point has only one possible radial orbit in
this chart. Thus an eventual transfer proof need not assume multiplicity one. -/
theorem source_orbit_unique
    (o p : Orbit 0 x) (z : source hdim x o) (w : source hdim x p)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z = q)
    (hw : PairedForestSimpleOverlap.facePoint hdim x p w = q) : o = p := by
  by_contra hne
  have hp := faceAmbient_other_positive hdim x o p z.val z.property.1 (Ne.symm hne)
  have he : faceAmbient hdim x o z.val = faceAmbient hdim x p w.val :=
    (decodedAmbient_eq_faceAmbient hdim x q o z hz).symm.trans
      (decodedAmbient_eq_faceAmbient hdim x q p w hw)
  rw [he, faceAmbient_selected_zero] at hp
  exact lt_irrefl _ hp

/-- Once its orbit is fixed, the strict source parameter is unique as well. -/
theorem source_parameter_unique (o : Orbit 0 x) (z w : source hdim x o)
    (hz : PairedForestSimpleOverlap.facePoint hdim x o z = q)
    (hw : PairedForestSimpleOverlap.facePoint hdim x o w = q) : z = w := by
  apply Subtype.ext
  apply faceAmbient_injective hdim x o
  exact (decodedAmbient_eq_faceAmbient hdim x q o z hz).symm.trans
    (decodedAmbient_eq_faceAmbient hdim x q o w hw)

end General

variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)

/-- A nonzero original cutoff itself supplies chart membership. This is not
an extra coverage premise for any of the statements below. -/
theorem mem_chart_of_cutoff_ne_zero (j : P.charts)
    (q : Compactification (0 : Fin (n+2)) 3)
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0) :
    q ∈ (ForestOrthantCharts.chart 0 j.val).target :=
  ForestChartOrientation.smallChart_target_subset 0 j.val (P.support j (subset_tsupport _ hρ))

/-- Exact original-partition transfer, reduced to its explicit pointwise
radial pattern with target membership discharged by the proved support bound. -/
theorem hasPairedSource_iff_decodedPattern_of_cutoff (j : P.charts)
    (q : Compactification (0 : Fin (n+2)) 3) (S : Finset (Fin (n+2)))
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0) :
    HasPairedSource (main_dimension n) j.val q S ↔ DecodedPairedPattern j.val q S :=
  hasPairedSource_iff_decodedPattern (main_dimension n) j.val q S
    (mem_chart_of_cutoff_ne_zero P j q hρ)

/-- The exact quantified remaining transfer proposition. `IsSimple` is a
predicate specifying the physical points and their prescribed masks; it can
be instantiated by canonical simple face data without changing this statement. -/
theorem forall_source_transfer_iff_decodedPattern
    (IsSimple : Compactification (0 : Fin (n+2)) 3 → Finset (Fin (n+2)) → Prop) :
    (∀ j : P.charts, ∀ q S, IsSimple q S →
      CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0 →
      HasPairedSource (main_dimension n) j.val q S) ↔
    (∀ j : P.charts, ∀ q S, IsSimple q S →
      CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0 →
      DecodedPairedPattern j.val q S) := by
  constructor
  · intro h j q S hs hρ
    exact (hasPairedSource_iff_decodedPattern_of_cutoff P j q S hρ).mp (h j q S hs hρ)
  · intro h j q S hs hρ
    exact (hasPairedSource_iff_decodedPattern_of_cutoff P j q S hρ).mpr (h j q S hs hρ)

/-- The same exact criterion specialized to genuine simple collision data,
with every original finite partition index and physical cluster quantified. -/
theorem simpleDatum_source_transfer_iff_decodedPattern :
    (∀ j : P.charts, ∀ (S : Finset (Fin (n+2)))
      (D : SingleInteriorCluster (0 : Fin (n+2)) 3 S), 1 < S.card →
      CompactDRAmbientPartition.cutoff 0 (P.partition j) D.toInteriorCollisionData.boundaryPoint ≠ 0 →
      HasPairedSource (main_dimension n) j.val D.toInteriorCollisionData.boundaryPoint S) ↔
    (∀ j : P.charts, ∀ (S : Finset (Fin (n+2)))
      (D : SingleInteriorCluster (0 : Fin (n+2)) 3 S), 1 < S.card →
      CompactDRAmbientPartition.cutoff 0 (P.partition j) D.toInteriorCollisionData.boundaryPoint ≠ 0 →
      DecodedPairedPattern j.val D.toInteriorCollisionData.boundaryPoint S) := by
  constructor
  · intro h j S D hS hρ
    exact (hasPairedSource_iff_decodedPattern_of_cutoff P j D.toInteriorCollisionData.boundaryPoint S hρ).mp
      (h j S D hS hρ)
  · intro h j S D hS hρ
    exact (hasPairedSource_iff_decodedPattern_of_cutoff P j D.toInteriorCollisionData.boundaryPoint S hρ).mpr
      (h j S D hS hρ)

/-- Once the explicit radial pattern is proved at a supported point, all
local graph-form, orientation, cutoff and summability factors are supplied by
the original P certificates. No analytic matching premise is added. -/
theorem exists_native_graph_series_of_decodedPattern (j : P.charts)
    (q : Compactification (0 : Fin (n+2)) 3) (S : Finset (Fin (n+2)))
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) q ≠ 0)
    (hp : DecodedPairedPattern j.val q S) :
    ∃ (o : Orbit 0 j.val) (ho : kind 0 j.val o = .paired)
      (z : source (main_dimension n) j.val o),
      PairedForestSimpleCluster.S j.val o ho = S ∧
      PairedForestSimpleOverlap.facePoint (main_dimension n) j.val o z = q ∧
      HasSum (fun l : PairedForestCountableLocalization.Index (main_dimension n) j.val o ho ↦
        PairedForestOverlapJacobian.productFaceSign (main_dimension n) j.val o ho *
          PairedForestGraphFormOverlap.localizedGraphIntegral (main_dimension n) j.val o ho
            (P.partition j) (mainEdges H) l)
        (MainClassifiedFaceAssembly.orbitValue P j o) := by
  obtain ⟨o,ho,z,hS,hq⟩ := (hasPairedSource_iff_decodedPattern_of_cutoff P j q S hρ).mpr hp
  refine ⟨o,ho,z,hS,hq,?_⟩
  exact PairedForestGraphFormOverlap.hasSum_localizedGraphIntegral
    (main_dimension n) j.val o ho (P.partition j) (mainEdges H) (mainEdges_noLoops H)
    (P.localizer j) (P.localization j) (P.support j) (P.orientation j)
    (P.orientation_jacobian j) (P.regular j).1 (P.regular j).2

end EnvelopingIsomorphism.Deformation.MainPairedChartTransfer
