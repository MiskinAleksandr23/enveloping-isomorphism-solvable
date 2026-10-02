import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityChart
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSingleZeroDR
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates

/-! Exact full-DR and compactification-point correspondence for the actual
all-interior infinity datum extracted from a strict native forest face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestResolvedCoordinates
open Configuration ExtractedForestParameters ExtractedForestChildShapes ForestRadialFaceClassification ForestRadialClusterLabels
open ForestSingleZeroLinearDR ComplexConjugate InfinityForestSimpleCluster
open RealForestCoarsePositions (node)
open RealForestResolvedCoordinates (normalize_sub normalize_conj)
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .infinity) (q : Fin m)
  (hq : q ∉ boundaryClusterBlock (lower x o) (upper x o))
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem doubledBase_eq (j : DoubledLabel (n+1) m) :
    (datum hdim x o ho q hq hne z).doubledBase j =
      (PairedForestCoarsePositions.positions hdim x o z j -
        (RealForestCoarsePositions.center hdim x o z : ℂ)) / (coarseScale hdim x o q z : ℂ) := by
  rcases j with (j | j) | j
  · rw [RealForestCoarsePositions.positions_inside hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z _
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho j))]
    simp [BoundaryAnchoredInfinityData.doubledBase]
  · have hr := ForestChartConfigurations.boundary_eq_ofReal (shapeData 0 x)
      (PairedForestCoarsePositions.parameters hdim x o z)
      (PairedForestCoarsePositions.radius_reflect hdim x o z)
      (PairedForestCoarsePositions.increment_reflect hdim x o z) j
    change PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
      ((PairedForestCoarsePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re : ℂ) at hr
    change (boundaryBase hdim x o q z j : ℂ) = _
    unfold boundaryBase offset
    rw [hr]
    push_cast
    rfl
  · have hj := (fixed_mem_mirror_iff 0 x _
      (RealForestCoarsePositions.node_fixed x o (RealForestCoarsePositions.infinity_isFixed x o ho)) j).mpr
      ((mem_interiorLabels 0 x _ _).mp (interior_mem x o ho j))
    rw [RealForestCoarsePositions.positions_inside hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z _ hj]
    simp [BoundaryAnchoredInfinityData.doubledBase]

theorem doubledVelocity_inside (j : DoubledLabel (n+1) m) (hj : j ∈ (node x o).val) :
    (datum hdim x o ho q hq hne z).doubledVelocity j =
      RealForestSimpleCluster.normalize (shapeAnchor hdim x o z)
        (RealForestShapePositions.positions hdim x o z j) := by
  rcases j with (j | j) | j
  · rfl
  · have hj' := (RealForestCoarsePositions.boundary_mem_node_iff x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) j).mp hj
    change (boundaryVelocity hdim x o z j : ℂ) = _
    rw [boundaryVelocity, if_pos hj']
    have hr := RealForestShapePositions.positions_reflect hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z (Sum.inl (Sum.inr j))
    change RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
      conj (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))) at hr
    have hre : RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
        ((RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using Complex.conj_eq_iff_im.mp hr.symm
    rw [hre, RealForestSimpleCluster.normalize_real]
    rfl
  · change conj (RealForestSimpleCluster.normalize _ _) = _
    rw [normalize_conj]
    exact congrArg _ (RealForestShapePositions.positions_reflect hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z (Sum.inl (Sum.inl j))).symm

theorem datum_linearData_eq_native :
    linearData (datum hdim x o ho q hq hne z).doubledBase
      (datum hdim x o ho q hq hne z).doubledVelocity =
      ForestRadialFaceDRInverse.data hdim x o z := by
  rw [RealForestSingleZeroDR.data_eq_branchData hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) z]
  apply linearData_eq_of_scaled_differences _ _ _ _
    (coarseScale hdim x o q z)⁻¹ (shapeAnchor hdim x o z).im⁻¹
    (inv_pos.mpr (coarseScale_pos hdim x o ho q hq hne z))
    (inv_pos.mpr (shapeAnchor_pos hdim x o ho z))
  · intro e
    rw [doubledBase_eq, doubledBase_eq]
    simp only [Complex.ofReal_inv]
    ring
  · intro e he
    have hins := ((RealForestCoarsePositions.positions_eq_iff hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z _ _).mp (sub_eq_zero.mp he)).resolve_left
      (fun h ↦ e.property h.symm)
    rw [doubledVelocity_inside hdim x o ho q hq hne z _ hins.1,
      doubledVelocity_inside hdim x o ho q hq hne z _ hins.2, normalize_sub]
    simp only [if_pos hins.1, if_pos hins.2]

theorem insertion_DR_eq_native :
    projectDR (domain hdim x o ho q hq hne z).insertion.val =
      ForestRadialFaceDRInverse.data hdim x o z := by
  change projectDR ((datum hdim x o ho q hq hne z).compactInsertion
    (BoundaryAnchoredInfinityData.admissibleScale_zero _)).val = _
  rw [BoundaryAnchoredInfinityData.compactInsertion_projectDR,
    BoundaryAnchoredInfinityData.resolvedDR_zero]
  exact datum_linearData_eq_native hdim x o ho q hq hne z

theorem insertion_eq_native :
    (domain hdim x o ho q hq hne z).insertion = ForestRadialFaceDRInverse.point hdim x o z := by
  apply projectDR_injective_on_compactification 0
  exact insertion_DR_eq_native hdim x o ho q hq hne z

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestResolvedCoordinates
