import EnvelopingIsomorphism.Deformation.MainPairedFixedChartIntegral
import EnvelopingIsomorphism.Deformation.MainPairedClusterAssembly

/-! The original finite Stokes partition reassembles to one full physical
interior-cluster face, with the computed outward minus sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedFullFaceIntegral
open Kontsevich InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open MainScalarBoundaryAssembly MainPairedClusterAssembly MainPairedFixedChartCover
open MainPairedFixedChartIntegral UniformBinaryGraphs MeasureTheory
open scoped Classical
variable {n : ℕ} {H : BinaryGraph (n+2) 3} (P : MainPartition H)
  (T : Finset (Fin (n+2))) (hT : 1 < T.card)

/-- The complete original finite chart/orbit sum, with no coverage, matching,
orientation or weighted-integral hypothesis. -/
theorem clusterValue_eq_neg_integral :
    clusterValue P T = -(∫ y in Face T, density (H := H) T hT y) := by
  have hlocal : clusterValue P T =
      ∑ j : P.charts, -(∫ y in Face T, faceWeight P j T hT y * density (H := H) T hT y) := by
    unfold clusterValue
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [MainClassifiedFaceAssembly.pairedValue_eq_orbitValue]
    exact sum_orbitValue_eq_neg_integral P j T hT
  rw [hlocal, Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun j _ ↦ integrable_weighted P j T hT)]
  congr 1
  apply setIntegral_congr_fun measurableSet_faceRegion
  intro y hy
  dsimp only
  rw [← Finset.sum_mul]
  change (∑ j : P.charts, weight P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) j y) * _ = _
  rw [sum_weight P.partition (anchorMem T hT) (referenceMem T hT)
    (referenceNe T hT) (anchorGlobal T) y hy, one_mul]

/-- Large paired clusters vanish only after the original finite partition
has been reassembled. No individual weighted piece is set to zero. -/
theorem clusterValue_eq_zero_of_large (hlarge : 3 ≤ T.card) : clusterValue P T = 0 := by
  have hT : 1 < T.card := by omega
  rw [clusterValue_eq_neg_integral P T hT]
  have hz := InteriorFaceFullIntegrability.integral_realFaceDensity_zero
    (PairedForestCommonRealDensity.edges (main_dimension n)
      (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) (mainEdges H))
    (anchorMem T hT) (referenceMem T hT) (referenceNe T hT)
    (fun q ↦ mainEdges_noLoops H (finCongr
      (PairedForestCommonRealDensity.degree_eq (main_dimension n)
        (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T)) q)) hlarge
  change -(∫ y in Face T, realFaceDensity _ y) = 0
  rw [hz, neg_zero]

end EnvelopingIsomorphism.Deformation.MainPairedFullFaceIntegral
