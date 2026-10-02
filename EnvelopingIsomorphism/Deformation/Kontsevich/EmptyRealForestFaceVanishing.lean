import EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceForms
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphValenceSelection
import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestFaceChangeVariables
import EnvelopingIsomorphism.Deformation.Kontsevich.NativePairedFaceIntegration

/-! Empty real clusters vanish in the literal native forest graph form.
The physical slot and all coordinate pullbacks are constructed from the
actual strict forest face; no nonempty boundary block is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing
open Configuration ForestRadialFaceClassification ForestOrthantRealization
open RealForestCoarsePositions (node labelsSet)
open BoundaryGraphFaceFactorization BoundaryGraphValenceSelection
open EmptyRealForestSimpleCluster
open ForestGlobalGraphStokes ForestRadialFaceLocalization BoxStokes CompactOrthantStokes
open scoped Classical

theorem simple_form_zero_of_valence_ne {N M R : ℕ} {i a : Fin N}
    {S : Finset (Fin N)} (s : Fin (M+1))
    (hdegree : shapeDegree a S s s + coarseDegree i S s s = R)
    (q : Fin N → ℕ) (Γ : KontsevichGraph.General.Graph q M)
    (order : Fin R ≃ KontsevichGraph.General.Edge q) (ha : a ∈ S)
    (hcount : (∑ v ∈ S, q v) ≠ 2 * (S.card - 1))
    (y : BoundaryClusterFreeCoordinates.FaceCoordinates i a S M)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions s s) :
    (graphForm (l := s) (u := s) (graphEdges Γ order)
      (BoundaryClusterFreeCoordinates.faceEmbedding y)).compContinuousLinearMap
        BoundaryClusterFreeCoordinates.faceEmbedding = 0 := by
  subst R
  apply BoundaryGraphDimensionVanishing.graphForm_nativeFace_eq_zero_of_internal_count_ne
    (graphEdges Γ order) _ (graphEdges_noLoops Γ order) y hy
  rw [card_graphEdges_source, shapeDegree_eq_source_card ha,
    boundaryClusterBlock_self, Finset.card_empty, add_zero]
  exact hcount

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
  (x : Compactification (0 : Fin (n+1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : RealForestCoarsePositions.IsFixed x o) (a b : Fin (n+1))
  (ha : a ∈ labelsSet x o) (hb : b ∉ labelsSet x o)
  (hempty : ∀ j : Fin m, Sum.inl (Sum.inr j) ∉ (node x o).val)
  (z : ForestRadialFaceLocalization.source hdim x o)

def forestEdges {q : Fin (n+1) → ℕ} (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) :
    Fin r → ForestGraphTopForms.Edge (n+1) m :=
  fun j ↦ ⟨(order j).1, Γ.target (order j), Γ.noLoops _ _⟩

include ho ha hb hempty in
theorem nativeForm_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1)) :
    RealForestFaceChangeVariables.nativeForm hdim x o (forestEdges Γ order) z.val = 0 := by
  let s := slot hdim x o ho a ha hempty z
  have hd : shapeDegree a (labelsSet x o) s s + coarseDegree b (labelsSet x o) s s = r := by
    rw [face_degree_eq ha hb]
    dsimp [GraphForms.dimension] at hdim
    omega
  have hs := simple_form_zero_of_valence_ne s hd q Γ order ha hcount
    (RealForestSimpleCoordinates.coordinates hdim x o a b z.val)
    (coordinates_mem_source hdim x o ho a b ha hb hempty z)
  rw [RealForestFaceChangeVariables.nativeForm,
    EmptyRealForestFaceForms.graphForm_eq_simple hdim x o ho a b ha hb hempty z]
  ext V
  exact congrArg (fun ω ↦ ω (fun j ↦
    (fderiv ℝ (RealForestSimpleCoordinates.coordinates hdim x o a b) z.val) (V j))) hs

include ho ha hb hempty in
theorem binary_nativeForm_eq_zero
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin (n+1) ↦ 2) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (fun _ : Fin (n+1) ↦ 2)) :
    RealForestFaceChangeVariables.nativeForm hdim x o (forestEdges Γ order) z.val = 0 := by
  apply nativeForm_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty z _ Γ order
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  omega

include ho ha hb hempty in
theorem mixed_nativeForm_eq_zero (v : Fin (n+1))
    (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 v) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 v)) :
    RealForestFaceChangeVariables.nativeForm hdim x o (forestEdges Γ order) z.val = 0 := by
  apply nativeForm_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty z _ Γ order
  rw [sum_single_vector_arity]
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  split_ifs <;> omega

def originalEdges {q : Fin (n+1) → ℕ} (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) : Fin r → GraphForms.Edge n m :=
  fun j ↦ ⟨(order j).1, Γ.target (order j)⟩

theorem originalEdges_noLoops {q : Fin (n+1) → ℕ} (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) (j : Fin r) :
    (originalEdges Γ order j).target ≠ Sum.inl (originalEdges Γ order j).source := Γ.noLoops _ _

theorem originalEdges_forestEdge {q : Fin (n+1) → ℕ} (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) :
    (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (originalEdges Γ order j)
      (originalEdges_noLoops Γ order j)) = forestEdges Γ order := by
  funext j
  simp [ForestPositiveGraphForms.forestEdge, originalEdges, forestEdges, Equiv.swap_self]

theorem local_density_eq_zero_of_nativeForm_eq_zero
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ) (hmatch : LocalizationAgreement x ρ edges hloop κ)
    (hzero : RealForestFaceChangeVariables.nativeForm hdim x o
      (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) z.val = 0) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ z.val = 0 := by
  have hi := ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x
    (faceAmbient hdim x o z.val) (faceAmbient_nonneg hdim x o z.val z.property.1)
  have hm := hmatch (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z.val))
  rw [hi, ChartCutoffSupport.zeroPullback_source _ _ z.property.2] at hm
  have hD := ((sourceCoordinates hdim x).symm.hasFDerivAt.comp z.val
    (hasFDerivAt_faceEmbedding (axis hdim x o) 0 z.val)).fderiv
  change fderiv ℝ (faceAmbient hdim x o) z.val = _ at hD
  rw [RealForestFaceChangeVariables.nativeForm, hD] at hzero
  simp only [NativePairedFaceIntegration.nativeDensity, facePullback, localForm,
    linearForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, fderiv_faceEmbedding]
  change ForestOrthantLocalization.localized 0 x ρ
    (fun j ↦ ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ
      (faceAmbient hdim x o z.val) _ = 0
  rw [hm]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hz := congrArg (fun ω ↦ ω (standardBasis r)) hzero
  change _ * ((ForestOrthantGraphForms.graphForm 0 x _ (faceAmbient hdim x o z.val)).compContinuousLinearMap
      ((sourceCoordinates hdim x).symm.toContinuousLinearMap.comp (faceTangent (axis hdim x o)))
        (standardBasis r)) = 0
  rw [hz]
  simp

include ho ha hb hempty in
theorem local_density_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1))
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    NativePairedFaceIntegration.nativeDensity hdim x o ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ z.val = 0 := by
  apply local_density_eq_zero_of_nativeForm_eq_zero hdim x o z ρ _ _ κ hmatch
  rw [originalEdges_forestEdge]
  exact nativeForm_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty z q Γ order hcount

include ho ha hb hempty in
theorem contribution_eq_zero_of_valence_ne
    (q : Fin (n+1) → ℕ) (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q)
    (hcount : (∑ v ∈ labelsSet x o, q v) ≠ 2 * ((labelsSet x o).card - 1))
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
    exact local_density_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty ⟨w,hw⟩
      q Γ order hcount ρ κ hmatch
  rw [hz, smul_zero]

include ho ha hb hempty in
theorem binary_contribution_eq_zero
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin (n+1) ↦ 2) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (fun _ : Fin (n+1) ↦ 2))
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  apply contribution_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty _ Γ order _ ρ κ hmatch
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  omega

include ho ha hb hempty in
theorem mixed_contribution_eq_zero (v : Fin (n+1))
    (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 v) m)
    (order : Fin r ≃ KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 v))
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (κ : Ambient 0 x → ℝ)
    (hmatch : LocalizationAgreement x ρ (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) :
    contribution hdim x (localForm hdim x ρ
      (originalEdges Γ order) (originalEdges_noLoops Γ order) κ) o = 0 := by
  apply contribution_eq_zero_of_valence_ne hdim x o ho a b ha hb hempty _ Γ order _ ρ κ hmatch
  rw [sum_single_vector_arity]
  have hS := Finset.card_pos.mpr (show (labelsSet x o).Nonempty from ⟨a, ha⟩)
  split_ifs <;> omega

end EnvelopingIsomorphism.Deformation.Kontsevich.EmptyRealForestFaceVanishing
