import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestSimpleCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestSingleZeroLinearDR

/-! The actual simple real-cluster datum retains every original doubled
pair direction and triple ratio of its native fixed forest face. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestDirectionRatioCoordinates ForestSingleZeroLinearDR ComplexConjugate
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem normalize_conj (w q : ℂ) :
    conj (RealForestSimpleCluster.normalize w q) = RealForestSimpleCluster.normalize w (conj q) := by
  simp [RealForestSimpleCluster.normalize]

theorem normalize_sub (w p q : ℂ) :
    RealForestSimpleCluster.normalize w p - RealForestSimpleCluster.normalize w q =
      ((w.im⁻¹ : ℝ) : ℂ) * (p-q) := by
  simp only [RealForestSimpleCluster.normalize, Complex.ofReal_inv]
  ring

theorem doubledBase_eq (j : DoubledLabel (n+1) m) :
    (datum hdim x o ho a b ha hb hne z).doubledBase j =
      RealForestSimpleCluster.normalize (coarseAnchor hdim x o b z)
        (PairedForestCoarsePositions.positions hdim x o z j) := by
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

theorem doubledVelocity_inside (j : DoubledLabel (n+1) m) (hj : j ∈ (node x o).val) :
    (datum hdim x o ho a b ha hb hne z).doubledVelocity j =
      RealForestSimpleCluster.normalize (shapeAnchor hdim x o a z)
        (RealForestShapePositions.positions hdim x o z j) := by
  rcases j with (j | j) | j
  · change RealForestSimpleCluster.velocity hdim x o a z j = _
    rw [RealForestSimpleCluster.velocity, if_pos ((mem_interiorLabels 0 x _ _).mpr hj)]
  · have hj' := (RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mp hj
    change ((boundaryVelocity hdim x o a z j) : ℂ) = _
    rw [boundaryVelocity, if_pos hj']
    have hr := RealForestShapePositions.positions_reflect hdim x o ho z (Sum.inl (Sum.inr j))
    change RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
      conj (RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))) at hr
    have hre : RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j)) =
        ((RealForestShapePositions.positions hdim x o z (Sum.inl (Sum.inr j))).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using Complex.conj_eq_iff_im.mp hr.symm
    rw [hre, normalize_real]
    rfl
  · have hj' := (mem_interiorLabels 0 x _ _).mpr
      ((fixed_mem_mirror_iff 0 x _ (RealForestCoarsePositions.node_fixed x o ho) j).mp hj)
    change conj (RealForestSimpleCluster.velocity hdim x o a z j) = _
    rw [RealForestSimpleCluster.velocity, if_pos hj', normalize_conj]
    exact congrArg _ (RealForestShapePositions.positions_reflect hdim x o ho z (Sum.inl (Sum.inl j))).symm

def nativeDomain : Domain (tree 0 x) (canonicalLeaf 0 x) :=
  ⟨PairedForestCoarsePositions.parameters hdim x o z,
    PairedForestCoarsePositions.radius_nonneg hdim x o z,
    (PairedForestCoarsePositions.openConditions hdim x o z).1⟩

theorem native_data_eq_resolved : ForestRadialFaceDRInverse.data hdim x o z =
    resolvedCoordinates (tree 0 x) (canonicalLeaf 0 x) (nativeDomain hdim x o z) := by
  rw [ForestRadialFaceDRInverse.data, ForestRadialFaceDRInverse.point_eq_forward]
  change projectDR (ForestChartConfigurations.compactificationInsertion (shapeData 0 x) 0
    (ForestChartOpenImage.toCorner 0 x (ForestRadialFaceDRInverse.parameter hdim x o z))).val = _
  rw [ForestChartConfigurations.compactificationInsertion_projectDR]
  have hp := ForestRadialFaceDRInverse.parameter_eq_realization hdim x o z
  change resolvedCoordinates (tree 0 x) (canonicalLeaf 0 x) _ = _
  congr 1
  exact Subtype.ext hp

/-- Exact full-DR matching for the actual constructed proper-real datum,
proved from the native single-radius collision and positive normalization. -/
theorem datum_linearData_eq_native :
    linearData (datum hdim x o ho a b ha hb hne z).doubledBase
      (datum hdim x o ho a b ha hb hne z).doubledVelocity =
      ForestRadialFaceDRInverse.data hdim x o z := by
  rw [native_data_eq_resolved, resolvedCoordinates_eq_branchData (tree 0 x) (canonicalLeaf 0 x)
    (node x o) (nativeDomain hdim x o z)
    ((RealForestCoarsePositions.radius_zero_iff hdim x o ho z _).mpr rfl)
    (RealForestCoarsePositions.radius_pos_of_ne hdim x o ho z)]
  apply linearData_eq_of_scaled_differences _ _ _ _
    (coarseAnchor hdim x o b z).im⁻¹ (shapeAnchor hdim x o a z).im⁻¹
    (inv_pos.mpr (coarseAnchor_pos hdim x o ho b hb z))
    (inv_pos.mpr (shapeAnchor_pos hdim x o ho a ha z))
  · intro e
    rw [doubledBase_eq, doubledBase_eq, normalize_sub]
    rfl
  · intro e he
    have heq : PairedForestCoarsePositions.positions hdim x o z e.val.2 =
        PairedForestCoarsePositions.positions hdim x o z e.val.1 := sub_eq_zero.mp he
    have hins := ((RealForestCoarsePositions.positions_eq_iff hdim x o ho z _ _).mp heq).resolve_left
      (fun h ↦ e.property h.symm)
    rw [doubledVelocity_inside hdim x o ho a b ha hb hne z _ hins.1,
      doubledVelocity_inside hdim x o ho a b ha hb hne z _ hins.2, normalize_sub]
    simp only [branchVelocity, if_pos ((le_canonicalLeaf_iff 0 x _ _).mpr hins.1),
      if_pos ((le_canonicalLeaf_iff 0 x _ _).mpr hins.2)]
    rfl

theorem insertion_DR_eq_native :
    projectDR (domain hdim x o ho a b ha hb hne z).insertion.val =
      ForestRadialFaceDRInverse.data hdim x o z := by
  convert datum_linearData_eq_native hdim x o ho a b ha hb hne z using 1
  apply Prod.ext
  · funext e
    simp [domain, BoundaryClusterDomain.datum, BoundaryClusterDomain.insertion, BoundaryClusterData.compactInsertion,
      BoundaryClusterData.resolvedCoordinates, BoundaryClusterData.activeDifference,
      projectDR, linearData, linearPhaseLimit, BoundaryClusterData.pairBase, BoundaryClusterData.pairVelocity]
  · funext e
    simp [domain, BoundaryClusterDomain.datum, BoundaryClusterDomain.insertion, BoundaryClusterData.compactInsertion,
      BoundaryClusterData.resolvedCoordinates, BoundaryClusterData.activeDifference,
      projectDR, linearData, linearRatioLimit, BoundaryClusterData.pairBase, BoundaryClusterData.pairVelocity]

/-- The simple face is the actual compactified forest point reanchored at
the chosen outside internal vertex; full DR injectivity proves equality. -/
theorem insertion_eq_anchorHomeomorph :
    (domain hdim x o ho a b ha hb hne z).insertion =
      anchorHomeomorph 0 b (ForestRadialFaceDRInverse.point hdim x o z) := by
  apply projectDR_injective_on_compactification b
  change projectDR (domain hdim x o ho a b ha hb hne z).insertion.val =
    projectDR (anchorHomeomorph 0 b (ForestRadialFaceDRInverse.point hdim x o z)).val
  rw [insertion_DR_eq_native, projectDR_anchorHomeomorph]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestResolvedCoordinates
