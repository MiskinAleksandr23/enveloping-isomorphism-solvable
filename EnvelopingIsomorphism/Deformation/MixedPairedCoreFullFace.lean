import EnvelopingIsomorphism.Deformation.MixedPairedCoreIntegral

/-! The original finite Stokes partition reassembles to one full physical
interior-cluster face, with the computed outward minus sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedCoreFullFace
open Kontsevich InteriorGraphFaceCoordinates InteriorFacePartitionReassembly
open MixedPairedCoreData MixedPairedCoreCover
open MixedPairedCoreIntegral MeasureTheory
open scoped Classical
variable {n m r : ℕ} {hdim : GraphForms.dimension n m = r+1}
  {es : Fin r → GraphForms.Edge n m} (P : PairedData hdim es)
  (T : Finset (Fin (n+1))) (hT : 1 < T.card)


def clusterValue (T : Finset (Fin (n+1))) : ℝ :=
  ∑ j : P.charts, ∑ o : ForestRadialFaceClassification.Orbit 0 j.val,
    if ho : ForestRadialFaceClassification.kind 0 j.val o = .paired then
      if PairedForestSimpleCluster.S j.val o ho = T then PairedData.orbitValue P j o else 0
    else 0

/-- The complete original finite chart/orbit sum, with no coverage, matching,
orientation or weighted-integral hypothesis. -/
theorem clusterValue_eq_neg_integral :
    clusterValue P T = -(∫ y in Face (m := m) T, density (hdim := hdim) (es := es) T hT y) := by
  have hlocal : clusterValue P T =
      ∑ j : P.charts, -(∫ y in Face (m := m) T, faceWeight P j T hT y * density (hdim := hdim) (es := es) T hT y) := by
    unfold clusterValue
    apply Finset.sum_congr rfl
    intro j _
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
    (PairedForestCommonRealDensity.edges hdim
      (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T) es)
    (anchorMem T hT) (referenceMem T hT) (referenceNe T hT)
    (fun q ↦ P.noLoops (finCongr
      (PairedForestCommonRealDensity.degree_eq hdim
        (anchorMem T hT) (referenceMem T hT) (referenceNe T hT) (anchorGlobal T)) q)) hlarge
  change -(∫ y in Face (m := m) T, realFaceDensity _ y) = 0
  rw [hz, neg_zero]

end EnvelopingIsomorphism.Deformation.MixedPairedCoreFullFace
