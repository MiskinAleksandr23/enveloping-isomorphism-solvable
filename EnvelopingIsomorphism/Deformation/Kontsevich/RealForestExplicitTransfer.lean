import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestPhysicalParity

/-! Proper-real native transfer with its physical coordinate sign evaluated.
The genuine graft endpoint retains the independent actual edge/chamber sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestExplicitTransfer
open Configuration ForestRadialFaceClassification BoxStokes RealForestNormalScale
open RealForestCoarsePositions (labelsSet)
open RealForestSimpleCluster (lower upper)
open RealForestPhysicalFactor RealForestPhysicalParity OrientedFormChangeVariables
open scoped Classical BigOperators
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (ho : RealForestCoarsePositions.IsFixed x o)

include ho ha hb in
theorem native_face_orientation (z : ForestRadialFaceLocalization.source hdim x o)
    (hz : PairedForestOverlapJacobian.SmallFace hdim x o z) (ε : ℝ)
    (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|) :
    ε * (-((-1 : ℝ) ^ (axis hdim x o).val)) *
      RealForestFaceChangeVariables.jacobian hdim x o a b ha hb z.val =
      -((-1 : ℝ)^r) * |RealForestFaceChangeVariables.jacobian hdim x o a b ha hb z.val| := by
  simpa only [physicalSign_eq] using
    RealForestCoorientation.native_face_orientation hdim x o a b ha hb ho z hz ε hε

include ho ha hb in
theorem signed_weighted_graph_integral
    (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
    (s : Set (Coord r)) (hs : MeasurableSet s)
    (hsub : s ⊆ ForestRadialFaceLocalization.source hdim x o)
    (hsmall : ∀ w (hw : w ∈ s), PairedForestOverlapJacobian.SmallFace hdim x o ⟨w,hsub hw⟩)
    (ε : ℝ) (hε : ∀ y ∈ ForestGlobalGraphStokes.positiveRegion hdim x,
      ε * jacobian (ForestGlobalGraphStokes.chart hdim x) y = |jacobian (ForestGlobalGraphStokes.chart hdim x) y|)
    (κ : Coord r → ℝ) (edges : Fin r → ForestGraphTopForms.Edge (n+1) m) :
    (ε * (-((-1 : ℝ) ^ (axis hdim x o).val))) *
      (∫ w in s, κ w * density (RealForestFaceChangeVariables.nativeForm hdim x o edges) w) =
    -((-1 : ℝ)^r) *
      (∫ y in RealForestFaceChangeVariables.map hdim x o a b ha hb '' s,
        κ (RealForestFaceChangeVariables.inverseReal hdim x o a b ha hb y) *
          density (RealForestFaceChangeVariables.simpleForm hdim x o a b ha hb edges) y) := by
  simpa only [physicalSign_eq] using
    RealForestCoorientation.signed_weighted_graph_integral hdim x o a b ha hb ho hne s hs hsub hsmall ε hε κ edges

open BoundaryGraphFaceFactorization BoundaryGraphGraftReconstruction BoundaryGraphOrderedCoordinates
open BoundaryGraphCanonicalFibreMatching BoundaryGraphValenceSelection

include ha hb in
/-- The physical factor multiplies the literal radius-first graft formula.
Every actual graph row and chamber permutation remains in fibreSign. -/
theorem normalized_genuine_graft {q : Fin (n+1) → ℕ}
    (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (shapeDegree a (labelsSet x o) (lower x o) (upper x o) +
      coarseDegree b (labelsSet x o) (lower x o) (upper x o)) ≃ KontsevichGraph.General.Edge q)
    (hcount : Fintype.card {j // (graphEdges Γ order j).1 ∈ labelsSet x o} =
      shapeDegree a (labelsSet x o) (lower x o) (upper x o))
    (hlu : lower x o < upper x o)
    (hn : ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ labelsSet x o →
      boundaryClusterCollapses (labelsSet x o) (lower x o) (upper x o) (Sum.inl (Γ.target e)))
    (hd : (orderedGraph Γ ha hb hlu).CoarseDistinct (centerSlot (le_of_lt hlu))) :
    physicalSign hdim x o a b ha hb *
      ((∏ v : Fin (n+1), ((q v).factorial : ℝ)⁻¹) *
        ((2 * Real.pi) ^ (shapeDegree a (labelsSet x o) (lower x o) (upper x o) +
          coarseDegree b (labelsSet x o) (lower x o) (upper x o)))⁻¹ *
        BoundaryGraphRadiusFirstTransport.outwardRadiusFirstIntegral (graphEdges Γ order)) =
    -((-1 : ℝ)^r) * fibreSign Γ ha hb order hcount hlu *
      GraphGeneralWeightedGraft.graftProfile (centerSlot (le_of_lt hlu))
        (outerCoefficient Γ ha hb order hcount) (innerCoefficient Γ ha hb order hcount hlu)
        (orderedGraph Γ ha hb hlu) := by
  rw [physicalSign_eq,
    BoundaryGraphRadiusFirstTransport.normalized_radiusFirst_integral_eq_signed_graftProfile Γ ha hb order hcount hlu hn hd]
  ring

/-- The main three-boundary-point face dimension is even. -/
theorem main_radius_sign {N R : ℕ} (hd : GraphForms.dimension N 3 = R+1) : (-1 : ℝ)^R = 1 := by
  have hR : R = 2 * (N+1) := by simp only [GraphForms.dimension] at hd; omega
  rw [hR, pow_mul]
  norm_num

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestExplicitTransfer
