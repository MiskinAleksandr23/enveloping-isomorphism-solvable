import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing

/-! Incorrect nonempty boundary block valence annihilates the actual native
proper-real forest form, including its original cutoff and radial integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.RealForestValenceVanishing
open Configuration ForestRadialFaceClassification ForestOrthantRealization
open RealForestCoarsePositions (node labelsSet)
open RealForestSimpleCluster (lower upper)
open BoundaryGraphFaceFactorization BoundaryGraphValenceSelection
open EmptyRealForestFaceVanishing (forestEdges originalEdges originalEdges_noLoops originalEdges_forestEdge)
open ForestGlobalGraphStokes ForestRadialFaceLocalization BoxStokes CompactOrthantStokes
open scoped Classical

theorem simple_form_zero_of_valence_ne {N M R : ℕ} {i a : Fin N}
    {S : Finset (Fin N)} (l u : Fin (M+1))
    (hdegree : shapeDegree a S l u + coarseDegree i S l u = R)
    (q : Fin N → ℕ) (Γ : KontsevichGraph.General.Graph q M)
    (order : Fin R ≃ KontsevichGraph.General.Edge q) (ha : a ∈ S)
    (hcount : (∑ v ∈ S, q v) ≠ 2 * (S.card - 1) + (boundaryClusterBlock l u).card)
    (y : BoundaryClusterFreeCoordinates.FaceCoordinates i a S M)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    (graphForm (l := l) (u := u) (graphEdges Γ order)
      (BoundaryClusterFreeCoordinates.faceEmbedding y)).compContinuousLinearMap
        BoundaryClusterFreeCoordinates.faceEmbedding = 0 := by
  subst R
  apply BoundaryGraphDimensionVanishing.graphForm_nativeFace_eq_zero_of_internal_count_ne
    (graphEdges Γ order) _ (graphEdges_noLoops Γ order) y hy
  rw [card_graphEdges_source, shapeDegree_eq_source_card ha]
  exact hcount

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty)
  (z : ForestRadialFaceLocalization.source hdim x o)

include ho ha hb hne in
theorem nativeForm_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1) +
      (boundaryClusterBlock (lower x o) (upper x o)).card) :
    RealForestFaceChangeVariables.nativeForm hdim x o (forestEdges Γ order) z.val = 0 := by
  have hd : shapeDegree a (labelsSet x o) (lower x o) (upper x o) +
      coarseDegree b (labelsSet x o) (lower x o) (upper x o) = r := by
    rw [face_degree_eq ha hb]
    dsimp [GraphForms.dimension] at hdim
    omega
  have hs := simple_form_zero_of_valence_ne (lower x o) (upper x o) hd q Γ order ha hcount
    (RealForestSimpleCoordinates.coordinates hdim x o a b z.val)
    (RealForestSimpleCoordinates.coordinates_mem_source hdim x o a b ho ha hb hne z)
  rw [RealForestFaceChangeVariables.nativeForm,
    RealForestFaceForms.graphForm_eq_simple hdim x o a b ho ha hb hne z]
  ext V
  exact congrArg (fun ω ↦ ω (fun j ↦
    (fderiv ℝ (RealForestSimpleCoordinates.coordinates hdim x o a b) z.val) (V j))) hs

include ho ha hb hne in
theorem local_density_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1) +
      (boundaryClusterBlock (lower x o) (upper x o)).card)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ z.val = 0 := by
  apply EmptyRealForestFaceVanishing.local_density_eq_zero_of_nativeForm_eq_zero hdim x o z ρ _ _ κ hmatch
  rw [originalEdges_forestEdge]
  exact nativeForm_eq_zero_of_valence_ne hdim x o ho a b ha hb hne z q Γ order hcount

include ho ha hb hne in
theorem contribution_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1) +
      (boundaryClusterBlock (lower x o) (upper x o)).card)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  rw [contribution_eq_integral_source hdim x o ρ _ _ κ hmatch]
  have hz : (∫ z in source hdim x o,
      facePullback (localForm hdim x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ)
        (axis hdim x o) 0 z (standardBasis r)) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro w hw
    exact local_density_eq_zero_of_valence_ne hdim x o ho a b ha hb hne ⟨w,hw⟩
      q Γ order hcount ρ κ hmatch
  rw [hz, smul_zero]

include ho ha hb hne in
theorem binary_contribution_eq_zero
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin (n+1) ↦ 2) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (fun _ : Fin (n+1) ↦ 2))
    (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ 2)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  apply contribution_eq_zero_of_valence_ne hdim x o ho a b ha hb hne _ Γ order _ ρ κ hmatch
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  omega

include ho ha hb hne in
theorem mixed_contribution_eq_zero (v : Fin (n+1))
    (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 v) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 v))
    (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ if v ∈ labelsSet x o then 1 else 2)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  apply contribution_eq_zero_of_valence_ne hdim x o ho a b ha hb hne _ Γ order _ ρ κ hmatch
  rw [sum_single_vector_arity]
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  split_ifs at hblock ⊢ <;> omega

/-- The actual proper-real classification supplies both anchors. Empty
blocks are handled by the separate genuine empty-face coordinate theorem. -/
theorem binary_properReal_contribution_eq_zero
    (hproper : kind 0 x o = .properReal)
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin (n+1) ↦ 2) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (fun _ : Fin (n+1) ↦ 2))
    (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ 2)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  obtain ⟨a,b,ha,hb⟩ := ForestRadialClusterLabels.properReal_anchors 0 x (node x o)
    ((kind_representative 0 x o).trans hproper)
  have ho := RealForestCoarsePositions.properReal_isFixed x o hproper
  by_cases hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty
  · exact binary_contribution_eq_zero hdim x o ho a b ha hb hne Γ order hblock ρ κ hmatch
  · apply EmptyRealForestFaceVanishing.binary_contribution_eq_zero hdim x o ho a b ha hb _ Γ order ρ κ hmatch
    intro j hj
    exact hne ⟨j, (RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mp hj⟩

theorem mixed_properReal_contribution_eq_zero
    (hproper : kind 0 x o = .properReal) (v : Fin (n+1))
    (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 v) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 v))
    (hblock : (boundaryClusterBlock (lower x o) (upper x o)).card ≠ if v ∈ labelsSet x o then 1 else 2)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  obtain ⟨a,b,ha,hb⟩ := ForestRadialClusterLabels.properReal_anchors 0 x (node x o)
    ((kind_representative 0 x o).trans hproper)
  have ho := RealForestCoarsePositions.properReal_isFixed x o hproper
  by_cases hne : (boundaryClusterBlock (lower x o) (upper x o)).Nonempty
  · exact mixed_contribution_eq_zero hdim x o ho a b ha hb hne v Γ order hblock ρ κ hmatch
  · apply EmptyRealForestFaceVanishing.mixed_contribution_eq_zero hdim x o ho a b ha hb _ v Γ order ρ κ hmatch
    intro j hj
    exact hne ⟨j, (RealForestCoarsePositions.boundary_mem_node_iff x o ho j).mp hj⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.RealForestValenceVanishing
