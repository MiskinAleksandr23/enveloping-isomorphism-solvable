import EnvelopingIsomorphism.Deformation.MainRealFixedChartIntegral
import EnvelopingIsomorphism.Deformation.MainRealPartitionReassembly

/-! The inherited simple-face basis and the actual ordered product basis are
related by their genuine volume-preserving coordinate permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealOrderedChartIntegral
open Kontsevich Configuration ForestRadialFaceClassification
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestFaceChangeVariables BoundaryGraphNativeTransport
open BoundaryGraphFaceFactorization BoundaryGraphOrderedIntegrals
open MainRealFixedChartIntegral OrientedFormChangeVariables
open MeasureTheory Set BoxStokes
open scoped Classical

theorem coordinateCast_measurePreserving {a b : ℕ} (h : a = b) :
    MeasurePreserving (ForestGlobalGraphStokes.coordinateCast h) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin b => ℝ) (finCongr h)

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
  (a b : Fin (n+1)) (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)

def orderedMap : Coord r ≃L[ℝ]
    MainRealPartitionReassembly.RealSpace (i := b) (a := a) (S := labelsSet x o) (l := lower x o) (u := upper x o) :=
  (simpleCoordinates hdim x o a b ha hb).symm.trans
    (orderedRealCoordinates (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)))

theorem orderedMap_measurePreserving :
    MeasurePreserving (orderedMap hdim x o a b ha hb) volume (volume.prod volume) := by
  have h := (nativeToOrdered_measurePreserving (i := b) (a := a) (S := labelsSet x o)
    (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o))).comp
      (coordinateCast_measurePreserving (dimension_eq hdim x o a b ha hb).symm)
  exact h

theorem simpleRegion_eq_preimage :
    simpleRegion hdim x o a b ha hb = (orderedMap hdim x o a b ha hb) ⁻¹'
      MainRealPartitionReassembly.FaceRegion := by
  ext y
  change (ForestGlobalGraphStokes.coordinateCast (dimension_eq hdim x o a b ha hb)).symm y ∈
      nativeDomain (i := b) (a := a) (S := labelsSet x o) (l := lower x o) (u := upper x o) ↔ _
  rw [nativeDomain_eq_preimage ha hb (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o))]
  rfl

/-- Literal transport of any measurable or nonmeasurable scalar density;
the Bochner integral identity itself requires no convergence premise. -/
theorem integral_simpleRegion_eq_ordered (f : Coord r → ℝ) :
    (∫ y in simpleRegion hdim x o a b ha hb, f y) =
      ∫ z in MainRealPartitionReassembly.FaceRegion,
        f ((orderedMap hdim x o a b ha hb).symm z) ∂volume.prod volume := by
  have h := (orderedMap_measurePreserving hdim x o a b ha hb).setIntegral_preimage_emb
    (orderedMap hdim x o a b ha hb).toHomeomorph.measurableEmbedding
    (fun z => f ((orderedMap hdim x o a b ha hb).symm z)) MainRealPartitionReassembly.FaceRegion
  rw [← simpleRegion_eq_preimage hdim x o a b ha hb] at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

def nativeEdges (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    Fin (shapeDegree a (labelsSet x o) (lower x o) (upper x o) +
      coarseDegree b (labelsSet x o) (lower x o) (upper x o)) → BoundaryGraphFaceFactorization.Edge (n+1) m :=
  fun j => let e := edges (finCongr (dimension_eq hdim x o a b ha hb) j); (e.source,e.target)

theorem density_simpleForm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) (y : Coord r) :
    density (simpleForm hdim x o a b ha hb edges) y =
      nativeRealDensity (nativeEdges hdim x o a b ha hb edges)
        ((ForestGlobalGraphStokes.coordinateCast (dimension_eq hdim x o a b ha hb)).symm y) := by
  have hd := dimension_eq hdim x o a b ha hb
  subst r
  change graphForm (fun j => ((edges j).source,(edges j).target))
      (BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm y))
      (fun j => BoundaryClusterFreeCoordinates.faceEmbedding (nativeCoordinates.symm (Pi.single j 1))) = _
  simp only [nativeCoordinates_symm_single]
  rfl

theorem density_simpleForm_orderedMap_symm (edges : Fin r → ForestGraphTopForms.Edge (n+1) m)
    (z : MainRealPartitionReassembly.RealSpace (i := b) (a := a) (S := labelsSet x o) (l := lower x o) (u := upper x o)) :
    density (simpleForm hdim x o a b ha hb edges) ((orderedMap hdim x o a b ha hb).symm z) =
      orderedRealDensity (nativeEdges hdim x o a b ha hb edges)
        (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) z := by
  rw [density_simpleForm]
  change nativeFaceDensity _ _ = nativeFaceDensity _ _
  congr 1
  change (simpleCoordinates hdim x o a b ha hb).symm
    ((simpleCoordinates hdim x o a b ha hb)
      (orderedRealFace (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) z)) = _
  exact (simpleCoordinates hdim x o a b ha hb).symm_apply_apply _

variable {J : Type*} [Fintype J]
  (ρ : InteriorFacePartitionReassembly.Partition J (0 : Fin (n+1)) m) (j : J)

theorem simpleCutoff_orderedMap_symm
    (z : MainRealPartitionReassembly.RealSpace (i := b) (a := a) (S := labelsSet x o) (l := lower x o) (u := upper x o)) :
    simpleCutoff hdim x o a b ha hb (ρ j) ((orderedMap hdim x o a b ha hb).symm z) =
      MainRealPartitionReassembly.weight ha hb
        (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) ρ j z := by
  have hm : (orderedMap hdim x o a b ha hb).symm z ∈ simpleRegion hdim x o a b ha hb ↔
      z ∈ MainRealPartitionReassembly.FaceRegion := by
    rw [simpleRegion_eq_preimage]
    simp only [mem_preimage,ContinuousLinearEquiv.apply_symm_apply]
  unfold simpleCutoff MainRealPartitionReassembly.weight
  split_ifs with hy hz hz
  · congr 1
    unfold simplePoint MainRealPartitionReassembly.facePoint
      MainRealPartitionReassembly.freePoint
    apply congrArg (fun p : BoundaryClusterFreeDomain b a (labelsSet x o) m (lower x o) (upper x o) =>
      anchorHomeomorph b 0 p.datum.boundaryPoint)
    apply Subtype.ext
    change BoundaryClusterFreeCoordinates.faceEmbedding _ = BoundaryClusterFreeCoordinates.faceEmbedding _
    congr 1
    change (simpleCoordinates hdim x o a b ha hb).symm
      ((simpleCoordinates hdim x o a b ha hb)
        (orderedRealFace (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) z)) = _
    exact (simpleCoordinates hdim x o a b ha hb).symm_apply_apply _
  · exact False.elim (hz (hm.mp hy))
  · exact False.elim (hy (hm.mpr hz))
  · rfl

/-- The same original partition weight and graph density, transported to the
ordered physical product chamber without a basis or measure hypothesis. -/
theorem integral_weighted_simpleForm_eq_ordered
    (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (∫ y in simpleRegion hdim x o a b ha hb,
      simpleCutoff hdim x o a b ha hb (ρ j) y * density (simpleForm hdim x o a b ha hb edges) y) =
    ∫ z in MainRealPartitionReassembly.FaceRegion,
      MainRealPartitionReassembly.weight ha hb
        (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) ρ j z *
      orderedRealDensity (nativeEdges hdim x o a b ha hb edges)
        (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) z ∂volume.prod volume := by
  rw [integral_simpleRegion_eq_ordered]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [simpleCutoff_orderedMap_symm,density_simpleForm_orderedMap_symm]

/-- The original signed Stokes orbit in the whole ordered physical product
domain, with its actual original partition weight. -/
theorem oriented_contribution_eq_ordered_integral
    (ho : kind 0 x o = .properReal)
    (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
    (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 (ρ j)) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : ForestOrthantRealization.Ambient 0 x → ℝ)
    (hmatch : ForestRadialFaceLocalization.LocalizationAgreement x (ρ j) edges hloop κ)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y =
        |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * contribution hdim x (ForestGlobalGraphStokes.localForm hdim x (ρ j) edges hloop κ) o =
    -((-1 : ℝ)^r) *
      (∫ z in MainRealPartitionReassembly.FaceRegion,
        MainRealPartitionReassembly.weight ha hb
          (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) ρ j z *
        orderedRealDensity
          (nativeEdges hdim x o a b ha hb (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)))
          (ForestRadialClusterLabels.block_order 0 x (RealForestCoarsePositions.node x o)) z ∂volume.prod volume) := by
  rw [oriented_contribution_eq_full_weighted_integral hdim x o a b ho ha hb hne (ρ j) hρ edges hloop κ hmatch ε hε,
    integral_weighted_simpleForm_eq_ordered]

end EnvelopingIsomorphism.Deformation.MainRealOrderedChartIntegral
