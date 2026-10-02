import EnvelopingIsomorphism.Deformation.MainPairedChartTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceZeroNodeLabels

/-! Unconditional transfer of a genuine simple interior face into every
specified original forest chart whose target contains it. The actual inverse
supplies admissibility and full-DR equality; its radial pattern is proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MainSimplePairedChartTransfer

open Kontsevich Configuration MainPairedChartTransfer
open ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestDirectionRatioCoordinates ForestOrthantRealization
open ReflectedRadiusCoordinates ForestRadialFaceClassification
open PairedForestReverseCoverageCriterion
open UniformBinaryGraphs MainScalarBoundaryAssembly
open scoped Classical

section General
variable {n m : ℕ} (x q : Compactification (0 : Fin (n + 1)) m)

/-- Native admissible parameters of the actual inverse in this specified chart. -/
def decodedParameters (hq : q ∈ (ForestOrthantCharts.chart 0 x).target) :
    Domain (tree 0 x) (canonicalLeaf 0 x) :=
  ⟨realization 0 x (decodedAmbient x q),
    realization_admissible 0 x ((ForestOrthantCharts.chart 0 x).symm q)
      ((ForestOrthantCharts.chart 0 x).map_target hq)⟩

/-- Its encoder agrees with the full coordinates of the original physical point. -/
theorem decodedParameters_fullDR (hq : q ∈ (ForestOrthantCharts.chart 0 x).target) :
    doubledCoordinates (tree 0 x) (canonicalLeaf 0 x) (decodedParameters x q hq) =
      projectDR q.val := by
  apply CompactDRCoordinates.dataEmbedding_injective
  apply (CompactDRCoordinates.realCoordinates (n + 1) m).injective
  change ambientDR 0 x (decodedAmbient x q) = CompactDRCoordinates.embedding 0 q
  rw [decodedAmbient, ambientDR_eq_chart 0 x ((ForestOrthantCharts.chart 0 x).symm q)
    ((ForestOrthantCharts.chart 0 x).map_target hq), (ForestOrthantCharts.chart 0 x).right_inv hq]

/-- Active-node radii are literally the corresponding decoded free coordinates. -/
theorem decodedParameters_radius (hq : q ∈ (ForestOrthantCharts.chart 0 x).target)
    (v : ActiveNode (tree 0 x)) :
    (decodedParameters x q hq).val.1 v.val = (decodedAmbient x q).1
      (orbitEquiv 0 x (orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) v)) := by
  change radiusArray 0 x (decodedAmbient x q) v.val = _
  rw [radiusArray, dif_pos v.property]
  rfl

variable {S : Finset (Fin (n + 1))}
  (D : SingleInteriorCluster (0 : Fin (n + 1)) m S)

/-- Actual transfer geometry: the inverse in any containing forest chart has
one zero paired orbit with exactly S and strictly positive other free radii. -/
theorem decodedPattern_of_mem_target (hS : 1 < S.card)
    (hq : D.toInteriorCollisionData.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    DecodedPairedPattern x D.toInteriorCollisionData.boundaryPoint S := by
  let q := D.toInteriorCollisionData.boundaryPoint
  let p := decodedParameters x q hq
  obtain ⟨u, hu, hz, hpos⟩ := SimpleFaceZeroNodeLabels.exists_unique_zero_orbit D x p
    (decodedParameters_fullDR x q hq) hS
  let o := orbitClass (tree 0 x) (reflection 0 x) (reflection_reflection 0 x) u
  have ho : kind 0 x o = .paired := kind_of_label x S u hu
  refine ⟨o, ho, upperNode_labels_of_label x S u hu, ?_, ?_⟩
  · exact (decodedParameters_radius x q hq u).symm.trans hz
  · intro o' hne
    have hp := hpos (representative 0 x o') (by simpa only [representative_orbit] using hne)
    rw [decodedParameters_radius x q hq, representative_orbit] at hp
    exact hp

/-- The strict paired source of the specified chart represents the very same
simple point and the same original cluster mask. -/
theorem hasPairedSource_of_mem_target {r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
    (hS : 1 < S.card)
    (hq : D.toInteriorCollisionData.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    HasPairedSource hdim x D.toInteriorCollisionData.boundaryPoint S :=
  (hasPairedSource_iff_decodedPattern hdim x D.toInteriorCollisionData.boundaryPoint S hq).mpr
    (decodedPattern_of_mem_target x D hS hq)

end General

variable {n : ℕ} {H : BinaryGraph (n + 2) 3} (P : MainPartition H)
  (j : P.charts) {S : Finset (Fin (n + 2))}
  (D : SingleInteriorCluster (0 : Fin (n + 2)) 3 S)

/-- A nonzero cutoff of the original finite partition supplies all chart
membership needed for the proved decoded radial pattern. -/
theorem decodedPattern_of_cutoff (hS : 1 < S.card)
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) D.toInteriorCollisionData.boundaryPoint ≠ 0) :
    DecodedPairedPattern j.val D.toInteriorCollisionData.boundaryPoint S :=
  decodedPattern_of_mem_target j.val D hS
    (mem_chart_of_cutoff_ne_zero P j D.toInteriorCollisionData.boundaryPoint hρ)

/-- Genuine original-partition source transfer, with no coverage or matching
certificate as input. -/
theorem hasPairedSource_of_cutoff (hS : 1 < S.card)
    (hρ : CompactDRAmbientPartition.cutoff 0 (P.partition j) D.toInteriorCollisionData.boundaryPoint ≠ 0) :
    HasPairedSource (main_dimension n) j.val D.toInteriorCollisionData.boundaryPoint S :=
  hasPairedSource_of_mem_target j.val D (main_dimension n) hS
    (mem_chart_of_cutoff_ne_zero P j D.toInteriorCollisionData.boundaryPoint hρ)

end EnvelopingIsomorphism.Deformation.MainSimplePairedChartTransfer
