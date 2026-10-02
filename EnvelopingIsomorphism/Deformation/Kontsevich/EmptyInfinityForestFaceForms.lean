import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestSimpleCluster
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityForestFaceForms

/-! The full native DR and graph form on an empty infinity face, with the
physical boundary slot recovered and proved locally constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceForms
open Configuration ExtractedForestParameters ExtractedForestChildShapes ForestRadialFaceClassification ForestRadialClusterLabels
open ForestSingleZeroLinearDR ComplexConjugate
open RealForestCoarsePositions (node)
open RealForestResolvedCoordinates (normalize_sub normalize_conj)
open InfinityForestSimpleCluster (interior_mem shapeAnchor shapeAnchor_pos coarseScale boundaryBase offset)
open EmptyInfinityForestSimpleCluster
open InfinityForestSimpleCoordinates (coordinates)
open RealForestFaceForms
open Filter
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .infinity)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (node x o).val)
  (q : Fin m) (z : ForestRadialFaceLocalization.source hdim x o)

theorem doubledBase_eq (j : DoubledLabel (n+1) m) :
    (datum hdim x o ho hempty q z).doubledBase j =
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
    (datum hdim x o ho hempty q z).doubledVelocity j =
      RealForestSimpleCluster.normalize (shapeAnchor hdim x o z)
        (RealForestShapePositions.positions hdim x o z j) := by
  rcases j with (j | j) | j
  · rfl
  · exact (hempty j hj).elim
  · change conj (RealForestSimpleCluster.normalize _ _) = _
    rw [normalize_conj]
    exact congrArg _ (RealForestShapePositions.positions_reflect hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z (Sum.inl (Sum.inl j))).symm

theorem datum_linearData_eq_native :
    linearData (datum hdim x o ho hempty q z).doubledBase
      (datum hdim x o ho hempty q z).doubledVelocity =
      ForestRadialFaceDRInverse.data hdim x o z := by
  rw [RealForestSingleZeroDR.data_eq_branchData hdim x o (RealForestCoarsePositions.infinity_isFixed x o ho) z]
  apply linearData_eq_of_scaled_differences _ _ _ _
    (coarseScale hdim x o q z)⁻¹ (shapeAnchor hdim x o z).im⁻¹
    (inv_pos.mpr (coarseScale_pos hdim x o ho hempty q z))
    (inv_pos.mpr (shapeAnchor_pos hdim x o ho z))
  · intro e
    rw [doubledBase_eq, doubledBase_eq]
    simp only [Complex.ofReal_inv]
    ring
  · intro e he
    have hins := ((RealForestCoarsePositions.positions_eq_iff hdim x o
      (RealForestCoarsePositions.infinity_isFixed x o ho) z _ _).mp (sub_eq_zero.mp he)).resolve_left
      (fun h ↦ e.property h.symm)
    rw [doubledVelocity_inside hdim x o ho hempty q z _ hins.1,
      doubledVelocity_inside hdim x o ho hempty q z _ hins.2, normalize_sub]
    simp only [if_pos hins.1, if_pos hins.2]

theorem insertion_DR_eq_native :
    projectDR (domain hdim x o ho hempty q z).insertion.val =
      ForestRadialFaceDRInverse.data hdim x o z := by
  change projectDR ((datum hdim x o ho hempty q z).compactInsertion
    (BoundaryAnchoredInfinityData.admissibleScale_zero _)).val = _
  rw [BoundaryAnchoredInfinityData.compactInsertion_projectDR,
    BoundaryAnchoredInfinityData.resolvedDR_zero]
  exact datum_linearData_eq_native hdim x o ho hempty q z

theorem ambient_coordinates_slot :
    InfinityBoundaryFaceDR.ambient (slot hdim x o ho hempty z) (slot hdim x o ho hempty z)
      (coordinates hdim x o q z.val) = ForestRadialFaceImmersion.forward hdim x o z.val := by
  rw [InfinityBoundaryFaceDR.ambient_eq_data _ _ _ (coordinates_mem_source hdim x o ho hempty q z)]
  have hfree : BoundaryAnchoredInfinityFreeCoordinates.faceDomain (coordinates hdim x o q z.val)
      (coordinates_mem_source hdim x o ho hempty q z) = freeDomain hdim x o ho hempty q z :=
    Subtype.ext (coordinates_eq_freeDomain hdim x o ho hempty q z)
  rw [hfree]
  simp only [EmptyInfinityForestSimpleCluster.freeDomain, BoundaryAnchoredInfinityFreeDomain.toDomain_toFreeDomain]
  rw [insertion_DR_eq_native, ForestRadialFaceImmersion.forward_data]

theorem nativePhase_eq_simple (p : DoubledPair (n+1) m) :
    (complexPhase (nativeUnit hdim x o p z.val) : ℂ) =
      (complexPhase (InfinityBoundaryFaceEdgeForms.resolvedPair
        (slot hdim x o ho hempty z) (slot hdim x o ho hempty z) p
        (coordinates hdim x o q z.val)) : ℂ) := by
  have h := congrArg (fun d : CompactDRCoordinates.Ambient (n+1) m ↦ d.1 p)
    (ambient_coordinates_slot hdim x o ho hempty q z)
  change InfinityBoundaryFaceEdgeForms.resolvedPair (slot hdim x o ho hempty z)
      (slot hdim x o ho hempty z) p (coordinates hdim x o q z.val) /
    (‖InfinityBoundaryFaceEdgeForms.resolvedPair (slot hdim x o ho hempty z)
      (slot hdim x o ho hempty z) p (coordinates hdim x o q z.val)‖ : ℂ) =
      (complexPhase (nativeUnit hdim x o p z.val) : ℂ) at h
  rw [← complexPhase_coe (InfinityBoundaryFaceEdgeForms.resolvedPair_ne_zero _ _ p _
    (coordinates_mem_source hdim x o ho hempty q z))] at h
  exact h.symm

theorem nativePairForm_eq_simple (p : DoubledPair (n+1) m) :
    nativePairForm hdim x o p z.val =
      (InfinityBoundaryFaceEdgeForms.pairForm (slot hdim x o ho hempty z)
        (slot hdim x o ho hempty z) p (coordinates hdim x o q z.val)).compContinuousLinearMap
          (fderiv ℝ (coordinates hdim x o q) z.val) := by
  let s := slot hdim x o ho hempty z
  have hf := (contDiff_nativeUnit hdim x o p).contDiffAt (x := z.val)
  have hc := contDiffAt_coordinates hdim x o ho hempty q z
  have hs := (InfinityBoundaryFaceEdgeForms.contDiff_resolvedPair (a := (0 : Fin (n+1))) (o := q)
    s s p).contDiffAt (x := coordinates hdim x o q z.val)
  have hsn := InfinityBoundaryFaceEdgeForms.resolvedPair_ne_zero s s p _
    (coordinates_mem_source hdim x o ho hempty q z)
  have he : (fun w ↦ (complexPhase (nativeUnit hdim x o p w) : ℂ)) =ᶠ[𝓝 z.val]
      (fun w ↦ (complexPhase (InfinityBoundaryFaceEdgeForms.resolvedPair s s p
        (coordinates hdim x o q w)) : ℂ)) := by
    filter_upwards [(ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property,
      eventually_slot_eq hdim x o ho hempty z] with w hw hs
    have h := nativePhase_eq_simple hdim x o ho hempty q ⟨w,hw⟩ p
    rw [hs hw] at h
    exact h
  unfold nativePairForm InfinityBoundaryFaceEdgeForms.pairForm
  rw [angularPullback_eq_of_complexPhase_eventually hf (hs.comp z.val hc)
    (nativeUnit_ne_zero hdim x o z p) hsn he]
  exact angularPullback_comp_differentiable _ _ z.val
    (hs.differentiableAt (by simp)) (hc.differentiableAt (by simp))

theorem nativeEdgeForm_eq_extended_face (j : Fin (n+1)) (v : Fin (n+1) ⊕ Fin m)
    (hv : v ≠ Sum.inl j) : nativeEdgeForm hdim x o j v hv z.val =
      ((BoundaryAnchoredInfinityFreeCoordinates.extendedEdgeForm (slot hdim x o ho hempty z)
        (slot hdim x o ho hempty z) j v
        (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))).compContinuousLinearMap
          BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding).compContinuousLinearMap
            (fderiv ℝ (coordinates hdim x o q) z.val) := by
  rw [← InfinityBoundaryFaceEdgeForms.edgeForm_eq_extended_face _ _ j v hv _
    (coordinates_mem_source hdim x o ho hempty q z)]
  unfold nativeEdgeForm InfinityBoundaryFaceEdgeForms.edgeForm
  rw [nativePairForm_eq_simple hdim x o ho hempty q z, nativePairForm_eq_simple hdim x o ho hempty q z]
  ext w
  rfl

theorem graphForm_eq_simple {k : ℕ} (edges : Fin k → ForestGraphTopForms.Edge (n+1) m) :
    (ForestOrthantGraphForms.graphForm 0 x edges (faceAmbient hdim x o z.val)).compContinuousLinearMap
      (fderiv ℝ (faceAmbient hdim x o) z.val) =
    (InfinityBoundaryGraphFactorization.graphForm
      (l := slot hdim x o ho hempty z) (u := slot hdim x o ho hempty z)
      (fun j ↦ ((edges j).source,(edges j).target))
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))).compContinuousLinearMap
        (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding.comp (fderiv ℝ (coordinates hdim x o q) z.val)) := by
  ext V
  change Matrix.det (fun i j ↦ ForestGraphTopForms.edgeLinear (shapeData 0 x) (edges j)
    (ForestOrthantGraphForms.reflectedRealization 0 x (faceAmbient hdim x o z.val))
      ((fderiv ℝ (ForestOrthantGraphForms.reflectedRealization 0 x) (faceAmbient hdim x o z.val))
        ((fderiv ℝ (faceAmbient hdim x o) z.val) (V i)))) =
    Matrix.det (fun i j ↦ InfinityBoundaryGraphFactorization.edgeLinear
      (l := slot hdim x o ho hempty z) (u := slot hdim x o ho hempty z)
      ((edges j).source,(edges j).target)
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding (coordinates hdim x o q z.val))
      (BoundaryAnchoredInfinityFreeCoordinates.faceEmbedding ((fderiv ℝ (coordinates hdim x o q) z.val) (V i))))
  congr 1
  funext i j
  rw [ForestGraphTopForms.edgeLinear_apply, InfinityBoundaryGraphFactorization.edgeLinear_apply]
  have hn := nativeEdgeForm_eq_orthant_edge hdim x o (edges j).source (edges j).target (edges j).nonloop z.val
  have hs := nativeEdgeForm_eq_extended_face hdim x o ho hempty q z (edges j).source (edges j).target (edges j).nonloop
  exact congrArg (fun ω : BoxStokes.Coord r [⋀^Fin 1]→L[ℝ] ℝ ↦ ω (fun _ ↦ V i)) (hn.symm.trans hs)

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyInfinityForestFaceForms
