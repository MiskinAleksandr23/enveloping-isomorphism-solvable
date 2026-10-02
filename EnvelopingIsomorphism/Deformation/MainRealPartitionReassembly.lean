import EnvelopingIsomorphism.Deformation.MainRealSupportOrbit
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphCanonicalFibreMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly

/-! The original finite ambient partition on an actual ordered real-cluster
face. Cutoffs are evaluated at the genuine compactified collision, reanchored
at the ambient anchor. Their integrals reassemble before graph factorization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainRealPartitionReassembly
open Kontsevich Configuration MeasureTheory Set
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphOrderedIntegrals
open BoundaryGraphGraftReconstruction BoundaryGraphValenceSelection BoundaryGraphExtractedOrders
open BoundaryGraphCanonicalFibreMatching
open scoped Classical BigOperators

variable {n m : ℕ} {i a k : Fin (n+1)} {S : Finset (Fin (n+1))} {l u : Fin (m+1)}

abbrev RealSpace := RealShape (a := a) (S := S) (l := l) (u := u) ×
  RealCoarse (i := i) (S := S) (l := l) (u := u)
abbrev FaceRegion : Set (RealSpace (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  GeometricWeights.realDomain (shapeN a S) (shapeM l u) ×ˢ
    GeometricWeights.realDomain (coarseN i S) (outsideM l u + 1)

theorem measurableSet_faceRegion : MeasurableSet (FaceRegion (i := i) (a := a) (S := S) (l := l) (u := u)) :=
  (GeometricWeights.measurableSet_realDomain _ _).prod (GeometricWeights.measurableSet_realDomain _ _)

variable (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)

def freePoint (z : FaceRegion (i := i) (a := a) (S := S) (l := l) (u := u)) :
    BoundaryClusterFreeDomain i a S m l u :=
  BoundaryClusterFaceDR.sourcePoint l u (orderedRealFace hlu z.val)
    ((orderedRealFace_open_iff ha hi hlu z.val).mpr z.property)

theorem continuous_freePoint : Continuous (freePoint ha hi hlu) := by
  apply Continuous.subtype_mk
  exact BoundaryClusterFreeCoordinates.faceEmbedding.continuous.comp
    (((orderedSplitFace hlu).symm.continuous.comp
      (((GraphForms.realCoordinates _ _).toContinuousLinearEquiv.symm.continuous.comp continuous_fst).prodMk
        ((GraphForms.realCoordinates _ _).toContinuousLinearEquiv.symm.continuous.comp continuous_snd))).comp continuous_subtype_val)

def facePoint (z : FaceRegion (i := i) (a := a) (S := S) (l := l) (u := u)) : Compactification k m :=
  anchorHomeomorph i k (freePoint ha hi hlu z).toDomain.insertion

theorem continuous_facePoint : Continuous (facePoint (k := k) ha hi hlu) :=
  (anchorHomeomorph i k).continuous.comp
    (BoundaryClusterDomain.continuous_insertion.comp
      (BoundaryClusterFreeDomain.continuous_toDomain.comp (continuous_freePoint ha hi hlu)))

theorem facePoint_eq_boundaryPoint (z : FaceRegion (i := i) (a := a) (S := S) (l := l) (u := u)) :
    facePoint (k := k) ha hi hlu z = anchorHomeomorph i k (freePoint ha hi hlu z).datum.boundaryPoint := rfl

variable {J : Type*} [Fintype J] (ρ : InteriorFacePartitionReassembly.Partition J k m)

def weightOnFace (j : J) (z : FaceRegion (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ :=
  CompactDRAmbientPartition.cutoff k (ρ j) (facePoint ha hi hlu z)

def weight (j : J) (z : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u)) : ℝ :=
  if hz : z ∈ FaceRegion then weightOnFace ha hi hlu ρ j ⟨z,hz⟩ else 0

theorem weight_eq (j : J) (z : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u))
    (hz : z ∈ FaceRegion) : weight ha hi hlu ρ j z =
      CompactDRAmbientPartition.cutoff k (ρ j) (facePoint ha hi hlu ⟨z,hz⟩) := by
  simp only [weight, dif_pos hz, weightOnFace]

theorem continuous_weightOnFace (j : J) : Continuous (weightOnFace ha hi hlu ρ j) :=
  (ρ j).property.continuous.comp ((CompactDRCoordinates.continuous_embedding k).comp
    (continuous_facePoint ha hi hlu))

theorem measurable_weight (j : J) : Measurable (weight ha hi hlu ρ j) :=
  Measurable.dite (continuous_weightOnFace ha hi hlu ρ j).measurable measurable_const measurableSet_faceRegion

theorem weight_nonneg (j : J) (z : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u)) :
    0 ≤ weight ha hi hlu ρ j z := by
  unfold weight
  split_ifs
  · exact ρ.nonneg j _
  · exact le_rfl

theorem weight_le_one (j : J) (z : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u)) :
    weight ha hi hlu ρ j z ≤ 1 := by
  unfold weight
  split_ifs
  · exact ρ.le_one j _
  · norm_num

theorem sum_weight (z : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u)) (hz : z ∈ FaceRegion) :
    ∑ j, weight ha hi hlu ρ j z = 1 := by
  simp_rw [weight_eq ha hi hlu ρ _ z hz, CompactDRAmbientPartition.cutoff]
  simpa only [finsum_eq_sum_of_fintype] using
    ρ.sum_eq_one (mem_range_self (facePoint (k := k) ha hi hlu ⟨z,hz⟩))

theorem integrableOn_weight_mul (f : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u) → ℝ)
    (hf : IntegrableOn f FaceRegion (volume.prod volume)) (j : J) :
    IntegrableOn (fun z => weight ha hi hlu ρ j z * f z) FaceRegion (volume.prod volume) :=
  hf.bdd_mul (measurable_weight ha hi hlu ρ j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg ha hi hlu ρ j z)]
      exact weight_le_one ha hi hlu ρ j z)

/-- The actual finite cutoff sum recovers the whole physical integral. -/
theorem sum_integral_weight_mul (f : RealSpace (i := i) (a := a) (S := S) (l := l) (u := u) → ℝ)
    (hf : IntegrableOn f FaceRegion (volume.prod volume)) :
    (∑ j, ∫ z in FaceRegion, weight ha hi hlu ρ j z * f z ∂volume.prod volume) =
      ∫ z in FaceRegion, f z ∂volume.prod volume := by
  rw [← integral_finsetSum _ (fun j _ => integrableOn_weight_mul ha hi hlu ρ f hf j)]
  apply setIntegral_congr_fun measurableSet_faceRegion
  intro z hz
  dsimp only
  rw [← Finset.sum_mul, sum_weight ha hi hlu ρ z hz, one_mul]

variable (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → BoundaryGraphFaceFactorization.Edge (n+1) m)
    (hcount : Fintype.card {j // (edges j).1 ∈ S} = shapeDegree a S l u)
    (hnout : ∀ j, (edges j).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges j).2))
    (hloop : ∀ j, (edges j).2 ≠ Sum.inl (edges j).1)

include ha hi hcount hnout hloop in
/-- Absolute convergence comes from the actual two smaller graph densities. -/
theorem integrableOn_orderedRealDensity :
    IntegrableOn (orderedRealDensity edges hlu) FaceRegion (volume.prod volume) := by
  have hp : IntegrableOn (fun z =>
      GeometricWeights.realDensity (orderedShapeEdges edges hcount hnout) z.1 *
      GeometricWeights.realDensity (orderedCoarseEdges edges hcount hlu) z.2)
      FaceRegion (volume.prod volume) := by
    change Integrable _ ((volume.prod volume).restrict _)
    rw [← Measure.prod_restrict]
    exact (ForestGraphIntegrability.absolutelyIntegrable _).mul_prod
      (ForestGraphIntegrability.absolutelyIntegrable _)
  apply (integrableOn_congr_fun (fun z hz =>
    orderedRealDensity_eq_product edges hcount hnout ha hi hlu hloop z hz)
    measurableSet_faceRegion).mpr
  exact hp.const_mul _

include hcount hnout hloop in
/-- Each chart's weighted density is integrable; the partition sum recovers
the entire physical real-face integral, with no convergence premise. -/
theorem sum_integral_weighted_orderedRealDensity :
    (∑ j, ∫ z in FaceRegion,
      weight ha hi hlu ρ j z * orderedRealDensity edges hlu z ∂volume.prod volume) =
      ∫ z in FaceRegion, orderedRealDensity edges hlu z ∂volume.prod volume :=
  sum_integral_weight_mul ha hi hlu ρ _
    (integrableOn_orderedRealDensity ha hi hlu edges hcount hnout hloop)

/-- Exact normalized finite weighted reassembly into the genuine extracted
graft profile. Every original cutoff and every edge-order sign is retained. -/
theorem normalized_sum_integral_eq_signed_graftProfile {q : Fin (n+1) → ℕ}
    (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hc : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)
    (hlt : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlt).CoarseDistinct (centerSlot hlt.le)) :
    (∏ v : Fin (n+1), ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∑ j, ∫ z in FaceRegion,
        weight ha hi hlt.le ρ j z * orderedRealDensity (graphEdges Γ order) hlt.le z ∂volume.prod volume) =
      fibreSign Γ ha hi order hc hlt *
        GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
          (outerCoefficient Γ ha hi order hc) (innerCoefficient Γ ha hi order hc hlt)
          (orderedGraph Γ ha hi hlt) := by
  rw [sum_integral_weighted_orderedRealDensity ha hi hlt.le ρ (graphEdges Γ order) hc
    (fun j hj => hn (order j) hj) (graphEdges_noLoops Γ order)]
  exact normalized_integral_eq_signed_graftProfile Γ ha hi order hc hlt hn hd

end EnvelopingIsomorphism.Deformation.MainRealPartitionReassembly
