import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeOrientation

/-! Native Lebesgue and outward-radius versions of the actual weighted
graft-fibre identity. Measure and orientation transport are proved, not inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeMatching
open scoped Classical BigOperators
open MeasureTheory
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphOrderedIntegrals
open BoundaryGraphNativeTransport BoundaryGraphNativeOrientation BoundaryGraphCanonicalFibreMatching
open KontsevichGraph.General
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)} {q : Fin n → ℕ}
variable (Γ : Graph q m) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ S} = shapeDegree a S l u)

theorem normalized_native_integral_eq_signed_graftProfile (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      (∫ x in nativeDomain, nativeRealDensity (graphEdges Γ order) x) =
      fibreSign Γ ha hi order hcount hlu *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  rw [integral_native_eq_ordered ha hi (le_of_lt hlu)]
  exact normalized_integral_eq_signed_graftProfile Γ ha hi order hcount hlu hn hd

theorem normalized_outward_integral_eq_signed_graftProfile (hlu : l < u)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hi hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      outwardNativeIntegral (graphEdges Γ order) =
      (-((-1 : ℝ) ^ (shapeDegree a S l u + coarseDegree i S l u)) * fibreSign Γ ha hi order hcount hlu) *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  unfold outwardNativeIntegral
  simp_rw [facePullback_nativeAmbientForm]
  have h := normalized_native_integral_eq_signed_graftProfile Γ ha hi order hcount hlu hn hd
  calc
    _ = -((-1 : ℝ) ^ (shapeDegree a S l u + coarseDegree i S l u)) *
        ((∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
          ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
          (∫ x in nativeDomain, nativeRealDensity (graphEdges Γ order) x)) := by ring
    _ = _ := by rw [h]; ring

/-- All structural hypotheses and both convergence proofs follow from the
actual nonzero face density and the proved global L1 theorem. -/
theorem normalized_outward_integral_eq_signed_graftProfile_of_nonzero (hlu : l < u)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    let hcount := BoundaryGraphDimensionVanishing.internal_count_eq_of_nativeFaceDensity_ne_zero (graphEdges Γ order)
      (graphEdges_noLoops Γ order) y hy hne
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ (shapeDegree a S l u + coarseDegree i S l u))⁻¹ *
      outwardNativeIntegral (graphEdges Γ order) =
      (-((-1 : ℝ) ^ (shapeDegree a S l u + coarseDegree i S l u)) * fibreSign Γ ha hi order hcount hlu) *
        GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
          (outerCoefficient Γ ha hi order hcount) (innerCoefficient Γ ha hi order hcount hlu)
          (orderedGraph Γ ha hi hlu) := by
  exact normalized_outward_integral_eq_signed_graftProfile Γ ha hi order _ hlu
    (BoundaryGraphAdmissibility.graph_noOutgoing_of_nativeFaceDensity_ne_zero Γ order y hy hne)
    (orderedGraph_coarseDistinct Γ ha hi hlu
      (BoundaryGraphAdmissibility.graph_coarseTarget_injective_of_nativeFaceDensity_ne_zero Γ order y hy hne))

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphNativeMatching
