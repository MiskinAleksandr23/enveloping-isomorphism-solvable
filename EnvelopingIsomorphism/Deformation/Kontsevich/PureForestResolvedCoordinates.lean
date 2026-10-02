import EnvelopingIsomorphism.Deformation.Kontsevich.PureForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSingleZeroDR
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates

/-! Every full doubled DR coordinate of the actual pure-boundary primitive
extracted from the native forest face agrees with the forest point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureForestResolvedCoordinates
open Configuration ExtractedForestParameters ExtractedForestChildShapes ForestRadialFaceClassification ForestRadialClusterLabels
open ForestSingleZeroLinearDR ComplexConjugate
open RealForestCoarsePositions (node)
open PureForestSimpleCluster
open RealForestResolvedCoordinates (normalize_sub normalize_conj)
open RealForestSimpleCluster (normalize normalizeReal normalize_real)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .pureBoundary) (a b : Fin m)
  (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem doubledBase_eq (j : DoubledLabel (n+1) m) :
    (datum hdim x o ho a b hl hu hab z).doubledBase j =
      RealForestSimpleCluster.normalize (anchor hdim x o z) (PairedForestCoarsePositions.positions hdim x o z j) := by
  rcases j with (j | j) | j
  · rfl
  · have hr := ForestChartConfigurations.boundary_eq_ofReal (shapeData 0 x)
      (PairedForestCoarsePositions.parameters hdim x o z)
      (PairedForestCoarsePositions.radius_reflect hdim x o z)
      (PairedForestCoarsePositions.increment_reflect hdim x o z) j
    change PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
      ((PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re : ℂ) at hr
    change (normalizeReal _ _ : ℂ) = RealForestSimpleCluster.normalize _ _
    rw [hr, normalize_real]
    rfl
  · change conj (RealForestSimpleCluster.normalize _ _) = _
    rw [normalize_conj]
    exact congrArg _ (PairedForestCoarsePositions.positions_reflect hdim x o z (Sum.inl (Sum.inl j))).symm

include ho in
theorem shapePosition_real (j : Fin m) :
    RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
      (shapePosition hdim x o z j : ℂ) := by
  have hr := RealForestShapePositions.positions_reflect hdim x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z (Sum.inl (Sum.inr j))
  change RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
    conj (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))) at hr
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using Complex.conj_eq_iff_im.mp hr.symm

theorem doubledVelocity_inside (j : DoubledLabel (n+1) m) (hj : j ∈ (node x o).val) :
    (datum hdim x o ho a b hl hu hab z).doubledVelocity j =
      (RealForestShapePositions.positions hdim x o z j - (shapePosition hdim x o z a : ℂ)) /
        (gap hdim x o a b z : ℂ) := by
  obtain ⟨j,rfl⟩ := pureBoundary_labels 0 x (node x o) ((kind_representative 0 x o).trans ho) j hj
  have hj' := (RealForestCoarsePositions.boundary_mem_node_iff x o
    (RealForestCoarsePositions.pureBoundary_isFixed x o ho) j).mp hj
  change ((PureForestSimpleCluster.velocity hdim x o a b z j) : ℂ) = _
  rw [PureForestSimpleCluster.velocity, if_pos hj', shapePosition_real hdim x o ho z j]
  push_cast
  rfl

theorem datum_linearData_eq_native :
    linearData (datum hdim x o ho a b hl hu hab z).doubledBase
      (datum hdim x o ho a b hl hu hab z).doubledVelocity =
      ForestRadialFaceDRInverse.data hdim x o z := by
  rw [RealForestSingleZeroDR.data_eq_branchData hdim x o (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z]
  apply linearData_eq_of_scaled_differences _ _ _ _
    (anchor hdim x o z).im⁻¹ (gap hdim x o a b z)⁻¹
    (inv_pos.mpr (anchor_pos hdim x o ho z))
    (inv_pos.mpr (gap_pos hdim x o ho a b hl hu hab z))
  · intro e
    rw [doubledBase_eq, doubledBase_eq, normalize_sub]
  · intro e he
    have hins := ((RealForestCoarsePositions.positions_eq_iff hdim x o
      (RealForestCoarsePositions.pureBoundary_isFixed x o ho) z _ _).mp (sub_eq_zero.mp he)).resolve_left
      (fun h ↦ e.property h.symm)
    rw [doubledVelocity_inside hdim x o ho a b hl hu hab z _ hins.1,
      doubledVelocity_inside hdim x o ho a b hl hu hab z _ hins.2]
    simp only [if_pos hins.1, if_pos hins.2, Complex.ofReal_inv]
    ring

theorem insertion_DR_eq_native :
    projectDR (domain hdim x o ho a b hl hu hab z).insertion.val =
      ForestRadialFaceDRInverse.data hdim x o z := by
  convert datum_linearData_eq_native hdim x o ho a b hl hu hab z using 1
  apply Prod.ext
  · funext e
    simp [domain, PureBoundaryClusterDomain.datum, PureBoundaryClusterDomain.insertion,
      PureBoundaryClusterData.compactInsertion, PureBoundaryClusterData.resolvedCoordinates,
      PureBoundaryClusterData.activeDifference, projectDR, linearData, linearPhaseLimit,
      PureBoundaryClusterData.pairBase, PureBoundaryClusterData.pairVelocity]
  · funext e
    simp [domain, PureBoundaryClusterDomain.datum, PureBoundaryClusterDomain.insertion,
      PureBoundaryClusterData.compactInsertion, PureBoundaryClusterData.resolvedCoordinates,
      PureBoundaryClusterData.activeDifference, projectDR, linearData, linearRatioLimit,
      PureBoundaryClusterData.pairBase, PureBoundaryClusterData.pairVelocity]

theorem insertion_eq_native :
    (domain hdim x o ho a b hl hu hab z).insertion = ForestRadialFaceDRInverse.point hdim x o z := by
  apply projectDR_injective_on_compactification 0
  exact insertion_DR_eq_native hdim x o ho a b hl hu hab z

end EnvelopingIsomorphism.Deformation.Kontsevich.PureForestResolvedCoordinates
