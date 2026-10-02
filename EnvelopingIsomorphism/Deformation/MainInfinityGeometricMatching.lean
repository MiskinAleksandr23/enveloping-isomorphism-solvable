import EnvelopingIsomorphism.Deformation.MainInfinityPhysicalAssembly
import EnvelopingIsomorphism.Deformation.InfinityBinaryShapeOrderSign
import EnvelopingIsomorphism.Deformation.MainPairedGeometricMatching
import EnvelopingIsomorphism.Deformation.MainNullaryInfinityCoefficients

/-! Evaluation of the original reassembled infinity faces in their actual
binary shape graph and canonical edge order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MainInfinityGeometricMatching
open Kontsevich KontsevichGraph.General MainScalarBoundaryAssembly
open InfinityBoundaryGraphFactorization InfinityBoundaryGraphIntegral InfinityBoundaryGraphMatching
open MainInfinityPhysicalFace MainInfinityPhysicalAssembly MainInfinityOrbitAssembly
open MeasureTheory
open scoped Classical
variable {n : ℕ} (F : MainInfinityPhysicalFace.FaceData)

def order : Fin (Degree (0 : Fin (n+2)) F.l F.u) ≃ Edge (fun _ : Fin (n+2) ↦ 2) :=
  (finCongr (degree_eq (main_dimension n) F)).trans
    (GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)))

theorem originalEdges_eq (H : UniformBinaryGraphs.BinaryGraph (n+2) 3) :
    originalEdges H (order F) = nativeEdges (main_dimension n) F (mainEdges H) := rfl

theorem shapeOrder_sign :
    Equiv.Perm.sign ((shapeOrder (order (n := n) F)).trans
      (GeometricWeights.canonicalOrder (shapeDegree (order F))).symm) = 1 := by
  have h := InfinityBinaryShapeOrderSign.binary_reindex_sign
    (InfinityBoundaryGraphCoordinates.sourceEquiv (a := (0 : Fin (n+2)))).symm
    ((GeometricWeights.binaryEdgeCount (n+1)).trans (degree_eq (main_dimension n) F).symm)
    (shapeDegree (order F))
  exact h

variable (H : UniformBinaryGraphs.BinaryGraph (n+2) 3)
  (hin : ∀ e, boundaryAnchoredInfinityCollapses F.l F.u (Sum.inl (H.target e)))

theorem normalized_integral_eq_canonicalShapeWeight :
    MainPairedGeometricMatching.normalization n *
      (∫ y in region (main_dimension n) F, OrientedFormChangeVariables.density
        (form (main_dimension n) F (mainEdges H)) y) =
      GeometricWeights.canonicalWeight (shapeGraph (a := (0 : Fin (n+2))) H hin)
        (shapeDegree (order F)) := by
  have h := normalized_outwardIntegral_eq_canonicalShapeWeight H hin F.outside F.all_inside F.ordered (order F)
  rw [shapeOrder_sign] at h
  simp only [Units.val_one,Int.cast_one,neg_one_mul] at h
  rw [originalEdges_eq] at h
  rw [integral_eq_neg_outwardIntegral,mul_neg]
  have hn : (∏ v : Fin (n+2), (((fun _ : Fin (n+2) ↦ 2) v).factorial : ℝ)⁻¹) *
      ((2 * Real.pi) ^ Degree (0 : Fin (n+2)) F.l F.u)⁻¹ =
      MainPairedGeometricMatching.normalization n := by
    rw [degree_eq (main_dimension n) F]
    rfl
  rw [hn] at h
  exact neg_eq_iff_eq_neg.mpr h

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2000000 in
omit hin in
theorem integral_eq_zero_of_not_noOutgoing
    (hn : ¬ ∀ e, boundaryAnchoredInfinityCollapses F.l F.u (Sum.inl (H.target e))) :
    (∫ y in region (main_dimension n) F, OrientedFormChangeVariables.density
      (form (main_dimension n) F (mainEdges H)) y) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hd
  rw [density_eq_native,← originalEdges_eq] at hd
  exact hn (graph_noOutgoing_of_nonzero H F.outside F.all_inside (order F)
    ((ForestGlobalGraphStokes.coordinateCast (degree_eq (main_dimension n) F)).symm y) hy hd)

theorem face_shapeM (s : Fin 2) : shapeM (face s).l (face s).u = 2 :=
  (Fintype.card_coe _).trans (face s).card_eq

theorem face_slot (s : Fin 2) :
    MainNullaryGraphCoefficients.slot (face s).ordered (face_shapeM s) = s := by
  apply Fin.ext
  rfl

omit hin F in
theorem normalized_integral_eq_coefficient_of_noOutgoing (s : Fin 2)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses (face s).l (face s).u (Sum.inl (H.target e))) :
    MainPairedGeometricMatching.normalization n *
      (∫ y in region (main_dimension n) (face s), OrientedFormChangeVariables.density
        (form (main_dimension n) (face s) (mainEdges H)) y) =
      GraphBinaryPhysicalSubsetIndex.coefficient H s Finset.univ := by
  rw [normalized_integral_eq_canonicalShapeWeight (face s) H hin]
  have h := MainNullaryInfinityCoefficients.coefficient_full_eq_canonicalShapeWeight
    (a := (0 : Fin (n+2))) (face s).ordered (face_shapeM s) H hin (shapeDegree (order (face s)))
  rw [face_slot] at h
  exact h.symm

omit hin F in
theorem normalized_integral_eq_coefficient (s : Fin 2) :
    MainPairedGeometricMatching.normalization n *
      (∫ y in region (main_dimension n) (face s), OrientedFormChangeVariables.density
        (form (main_dimension n) (face s) (mainEdges H)) y) =
      GraphBinaryPhysicalSubsetIndex.coefficient H s Finset.univ := by
  by_cases hin : ∀ e, boundaryAnchoredInfinityCollapses (face s).l (face s).u (Sum.inl (H.target e))
  · exact normalized_integral_eq_coefficient_of_noOutgoing H s hin
  · rw [integral_eq_zero_of_not_noOutgoing (face s) H hin,mul_zero]
    have h := MainNullaryInfinityCoefficients.coefficient_full_of_not_noOutgoing
      (a := (0 : Fin (n+2))) (face s).ordered (face_shapeM s) H hin
    rw [face_slot] at h
    exact h.symm

theorem face_sign (s : Fin 2) :
    BoundaryAnchoredInfinityData.referenceSign (face s).l (face s).q * (-1 : ℝ)^(face s).q.val =
      (-1 : ℝ)^s.val := by
  fin_cases s <;> norm_num [face,MainPurePhysicalAssembly.face,BoundaryAnchoredInfinityData.referenceSign]

omit hin F H in
theorem cluster_matching {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) (s : Fin 2) :
    MainPairedGeometricMatching.normalization n * clusterValue (ofMain P) (face s) =
      (-1 : ℝ)^s.val * GraphBinaryPhysicalSubsetIndex.coefficient H s Finset.univ := by
  rw [clusterValue_eq_integral,face_sign]
  calc
    _ = (-1 : ℝ)^s.val * (MainPairedGeometricMatching.normalization n *
      ∫ y in region (main_dimension n) (face s), OrientedFormChangeVariables.density
        (form (main_dimension n) (face s) (mainEdges H)) y) := by ring
    _ = _ := by rw [normalized_integral_eq_coefficient]

omit hin F H in
/-- The actual original finite Stokes infinity contribution equals the two
full-subset graph coefficients, with their computed opposite signs. -/
theorem infinity_native_matching {H : UniformBinaryGraphs.BinaryGraph (n+2) 3}
    (P : MainPartition H) :
    MainPairedGeometricMatching.normalization n * nativeKindBoundary P .infinity =
      GraphBinaryPhysicalSubsetIndex.coefficient H 0 Finset.univ -
        GraphBinaryPhysicalSubsetIndex.coefficient H 1 Finset.univ := by
  rw [nativeKind_infinity_eq_clusters,mul_add,cluster_matching,cluster_matching]
  norm_num
  ring

end EnvelopingIsomorphism.Deformation.MainInfinityGeometricMatching
