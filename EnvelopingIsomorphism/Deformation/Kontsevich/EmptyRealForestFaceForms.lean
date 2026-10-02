import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceForms

/-! Literal full-DR and differential-form matching for actual empty real
forest faces at their physical slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceForms
open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestRadialFaceClassification ForestRadialClusterLabels ForestOrthantRealization
open ForestDirectionRatioCoordinates ForestSingleZeroLinearDR ComplexConjugate
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCoordinates RealForestSimpleCluster
open RealForestResolvedCoordinates (normalize_conj normalize_sub nativeDomain native_data_eq_resolved)
open EmptyRealForestSimpleCluster
open Filter
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (node x o).val)
  (z : ForestRadialFaceLocalization.source hdim x o)

theorem doubledBase_eq (j : DoubledLabel (n+1) m) :
    (datum hdim x o ho a b ha hb hempty z).doubledBase j =
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
    (datum hdim x o ho a b ha hb hempty z).doubledVelocity j =
      RealForestSimpleCluster.normalize (shapeAnchor hdim x o a z)
        (RealForestShapePositions.positions hdim x o z j) := by
  rcases j with (j | j) | j
  · change RealForestSimpleCluster.velocity hdim x o a z j = _
    rw [RealForestSimpleCluster.velocity, if_pos ((mem_interiorLabels 0 x _ _).mpr hj)]
  · exact (hempty j hj).elim
  · have hj' := (mem_interiorLabels 0 x _ _).mpr
      ((fixed_mem_mirror_iff 0 x _ (RealForestCoarsePositions.node_fixed x o ho) j).mp hj)
    change conj (RealForestSimpleCluster.velocity hdim x o a z j) = _
    rw [RealForestSimpleCluster.velocity, if_pos hj', normalize_conj]
    exact congrArg _ (RealForestShapePositions.positions_reflect hdim x o ho z (Sum.inl (Sum.inl j))).symm

theorem datum_linearData_eq_native :
    linearData (datum hdim x o ho a b ha hb hempty z).doubledBase
      (datum hdim x o ho a b ha hb hempty z).doubledVelocity =
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
    rw [doubledVelocity_inside hdim x o ho a b ha hb hempty z _ hins.1,
      doubledVelocity_inside hdim x o ho a b ha hb hempty z _ hins.2, normalize_sub]
    simp only [branchVelocity, if_pos ((le_canonicalLeaf_iff 0 x _ _).mpr hins.1),
      if_pos ((le_canonicalLeaf_iff 0 x _ _).mpr hins.2)]
    rfl

theorem insertion_DR_eq_native :
    projectDR (domain hdim x o ho a b ha hb hempty z).insertion.val =
      ForestRadialFaceDRInverse.data hdim x o z := by
  convert datum_linearData_eq_native hdim x o ho a b ha hb hempty z using 1
  apply Prod.ext
  · funext e
    simp [EmptyRealForestSimpleCluster.domain, BoundaryClusterDomain.datum, BoundaryClusterDomain.insertion, BoundaryClusterData.compactInsertion,
      BoundaryClusterData.resolvedCoordinates, BoundaryClusterData.activeDifference,
      projectDR, linearData, linearPhaseLimit, BoundaryClusterData.pairBase, BoundaryClusterData.pairVelocity]
  · funext e
    simp [EmptyRealForestSimpleCluster.domain, BoundaryClusterDomain.datum, BoundaryClusterDomain.insertion, BoundaryClusterData.compactInsertion,
      BoundaryClusterData.resolvedCoordinates, BoundaryClusterData.activeDifference,
      projectDR, linearData, linearRatioLimit, BoundaryClusterData.pairBase, BoundaryClusterData.pairVelocity]


include hb in
theorem ambient_coordinates_slot :
    BoundaryClusterFaceDR.ambient (slot hdim x o ho a ha hempty z) (slot hdim x o ho a ha hempty z)
      (coordinates hdim x o a b z.val) = ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [BoundaryClusterFaceDR.ambient_eq_data _ _ _
    (EmptyRealForestSimpleCluster.coordinates_mem_source hdim x o ho a b ha hb hempty z)]
  have hfree : BoundaryClusterFaceDR.sourcePoint (slot hdim x o ho a ha hempty z)
      (slot hdim x o ho a ha hempty z) (coordinates hdim x o a b z.val)
      (EmptyRealForestSimpleCluster.coordinates_mem_source hdim x o ho a b ha hb hempty z) =
      freeDomain hdim x o ho a b ha hb hempty z :=
    Subtype.ext (EmptyRealForestSimpleCluster.coordinates_eq_freeDomain hdim x o ho a b ha hb hempty z)
  rw [hfree]
  simp only [EmptyRealForestSimpleCluster.freeDomain, BoundaryClusterFreeDomain.toDomain_toFreeDomain]
  rw [insertion_DR_eq_native, ForestRadialFaceImmersion.forward_data]

theorem resolvedPair_empty_slot {N M : ℕ} {i c : Fin N} {S : Finset (Fin N)}
    (s t : Fin (M+1)) (p : DoubledPair N M)
    (y : BoundaryClusterFreeCoordinates.FaceCoordinates i c S M) :
    BoundaryClusterFaceEdgeForms.resolvedPair s s p y =
      BoundaryClusterFaceEdgeForms.resolvedPair t t p y := by
  have hm (j : DoubledLabel N M) : boundaryClusterCollapses S s s j ↔
      boundaryClusterCollapses S t t j := by
    rcases j with (j | j) | j <;> simp [boundaryClusterCollapses, boundaryClusterBlock_self]
  have hb (j : DoubledLabel N M) : BoundaryClusterFaceDR.base s s y j =
      BoundaryClusterFaceDR.base t t y j := by
    rcases j with (j | j) | j <;>
      simp [BoundaryClusterFaceDR.base, BoundaryClusterFreeCoordinates.boundaryBase, boundaryClusterBlock_self]
  have hv (j : DoubledLabel N M) : BoundaryClusterFaceDR.velocity s s y j =
      BoundaryClusterFaceDR.velocity t t y j := by
    rcases j with (j | j) | j <;>
      simp [BoundaryClusterFaceDR.velocity, BoundaryClusterFreeCoordinates.boundaryVelocity, boundaryClusterBlock_self]
  simp only [BoundaryClusterFaceEdgeForms.resolvedPair, boundaryClusterPairCollapses, hm,
    BoundaryClusterFaceDR.pairBase, BoundaryClusterFaceDR.pairVelocity, hb, hv]

include ho ha hb hempty in
theorem nativePhase_eq_simple (s : Fin (m+1)) (p : DoubledPair (n+1) m) :
    (complexPhase (RealForestFaceForms.nativeUnit hdim x o p z.val) : ℂ) =
      (complexPhase (BoundaryClusterFaceEdgeForms.resolvedPair s s p
        (coordinates hdim x o a b z.val)) : ℂ) := by
  have h := congrArg (fun d : CompactDRCoordinates.Ambient (n+1) m ↦ d.1 p)
    (ambient_coordinates_slot hdim x o ho a b ha hb hempty z)
  change BoundaryClusterFaceDR.direction _ _ p (coordinates hdim x o a b z.val) =
    (complexPhase (RealForestFaceForms.nativeUnit hdim x o p z.val) : ℂ) at h
  rw [BoundaryClusterFaceEdgeForms.direction_eq_phase, resolvedPair_empty_slot _ s] at h
  exact h.symm

include ho ha hb hempty in
theorem nativePairForm_eq_simple (p : DoubledPair (n+1) m) :
    RealForestFaceForms.nativePairForm hdim x o p z.val =
      (BoundaryClusterFaceEdgeForms.pairForm (slot hdim x o ho a ha hempty z)
        (slot hdim x o ho a ha hempty z) p
        (coordinates hdim x o a b z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  let s := slot hdim x o ho a ha hempty z
  have hf := (RealForestFaceForms.contDiff_nativeUnit hdim x o p).contDiffAt (x := z.val)
  have hc := contDiffAt_coordinates hdim x o a b ho ha hb z
  have hs := (BoundaryClusterFaceEdgeForms.contDiff_resolvedPair (i := b) (a := a)
    (S := labelsSet x o) s s p).contDiffAt (x := coordinates hdim x o a b z.val)
  have hsn := BoundaryClusterFaceEdgeForms.resolvedPair_ne_zero s s p _
    (EmptyRealForestSimpleCluster.coordinates_mem_source hdim x o ho a b ha hb hempty z)
  have he : (fun w ↦ (complexPhase (RealForestFaceForms.nativeUnit hdim x o p w) : ℂ)) =ᶠ[𝓝 z.val]
      (fun w ↦ (complexPhase (BoundaryClusterFaceEdgeForms.resolvedPair s s p
        (coordinates hdim x o a b w)) : ℂ)) :=
    eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ nativePhase_eq_simple hdim x o ho a b ha hb hempty ⟨w,hw⟩ s p)
  unfold RealForestFaceForms.nativePairForm BoundaryClusterFaceEdgeForms.pairForm
  rw [angularPullback_eq_of_complexPhase_eventually hf (hs.comp z.val hc)
    (RealForestFaceForms.nativeUnit_ne_zero hdim x o z p) hsn he]
  exact angularPullback_comp_differentiable _ _ z.val
    (hs.differentiableAt (by simp)) (hc.differentiableAt (by simp))

include ho ha hb hempty in
theorem nativeEdgeForm_eq_extended_face (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) :
    RealForestFaceForms.nativeEdgeForm hdim x o j v hv z.val =
      ((BoundaryClusterFreeCoordinates.extendedEdgeForm (slot hdim x o ho a ha hempty z)
        (slot hdim x o ho a ha hempty z) j v
        (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))).compContinuousLinearMap
          BoundaryClusterFreeCoordinates.faceEmbedding).compContinuousLinearMap
            (fderiv ℝ (coordinates hdim x o a b) z.val) := by
  rw [← BoundaryClusterFaceEdgeForms.edgeForm_eq_extended_face _ _ j v hv _
    (EmptyRealForestSimpleCluster.coordinates_mem_source hdim x o ho a b ha hb hempty z)]
  unfold RealForestFaceForms.nativeEdgeForm BoundaryClusterFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_simple hdim x o ho a b ha hb hempty z,
    nativePairForm_eq_simple hdim x o ho a b ha hb hempty z]
  ext w
  rfl

include ho ha hb hempty in
theorem graphForm_eq_simple {q : ℕ} (edges : Fin q → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z.val)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) z.val) =
    (BoundaryGraphFaceFactorization.graphForm
      (l := slot hdim x o ho a ha hempty z) (u := slot hdim x o ho a ha hempty z)
      (fun j ↦ ((edges j).source, (edges j).target))
      (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))).compContinuousLinearMap
        (BoundaryClusterFreeCoordinates.faceEmbedding.comp (fderiv ℝ (coordinates hdim x o a b) z.val)) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o z.val))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o z.val))
        ((fderiv ℝ (faceAmbient hdim x o) z.val) (V i)))) =
    Matrix.det (fun i j ↦ BoundaryGraphFaceFactorization.edgeLinear
      (l := slot hdim x o ho a ha hempty z) (u := slot hdim x o ho a ha hempty z)
      ((edges j).source, (edges j).target)
      (BoundaryClusterFreeCoordinates.faceEmbedding (coordinates hdim x o a b z.val))
      (BoundaryClusterFreeCoordinates.faceEmbedding ((fderiv ℝ (coordinates hdim x o a b) z.val) (V i))))
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply]
  change _ = BoundaryGraphFaceFactorization.formLinear _ _
  rw [BoundaryGraphFaceFactorization.formLinear_apply]
  have hn := RealForestFaceForms.nativeEdgeForm_eq_orthant_edge hdim x o
    (edges j).source (edges j).target (edges j).nonloop z.val
  have hs := nativeEdgeForm_eq_extended_face hdim x o ho a b ha hb hempty z
    (edges j).source (edges j).target (edges j).nonloop
  exact congrArg (fun ω : BoxStokes.Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceForms
