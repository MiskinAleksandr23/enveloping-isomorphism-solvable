import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveGraphForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.UnorientedFormIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantLocalization
import EnvelopingIsomorphism.Deformation.Kontsevich.FiniteForestOrthantPartition
import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestDimension
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormDegeneracy
import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedFormChangeVariables
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Absolute integrability from the actual compactly supported forest pieces.
Change of variables uses absolute Jacobians and no orientation assumption. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability

open Configuration ForestOrthantRealization ForestOrthantLocalization ForestOrthantGraphForms
open MeasureTheory Set
open scoped Classical Topology ContDiff

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

abbrev Dimension := GraphForms.dimension n m
abbrev RealCoordinates (n m : ℕ) := Fin (GraphForms.dimension n m) → ℝ

theorem ambient_finrank : Module.finrank ℝ (Ambient i x) = GraphForms.dimension n m := by
  have h := ExtractedForestDimension.total_dimension_add_two i x
  simp only [Ambient, Module.finrank_prod, Module.finrank_fin_fun]
  change ExtractedForestShapeCoordinates.radialCount i x +
    (ExtractedForestShapeCoordinates.circleCount i x + ExtractedForestShapeCoordinates.realCount i x) = n * 2 + m
  omega

/-- A genuine continuous real-linear coordinate equivalence of the proved
dimension; its orientation is deliberately unrestricted. -/
def sourceCoordinates : Ambient i x ≃L[ℝ] RealCoordinates n m :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [ambient_finrank, Module.finrank_fin_fun])

def nativeCoordinates : GraphForms.Coordinates n m ≃L[ℝ] RealCoordinates n m :=
  (GraphForms.realCoordinates n m).toContinuousLinearEquiv

theorem nativeCoordinates_symm_basis (j : Fin (GraphForms.dimension n m)) :
    (nativeCoordinates (n := n) (m := m)).symm (BoxStokes.standardBasis _ j) = GraphForms.realBasis n m j := by
  apply (GraphForms.realCoordinates n m).injective
  change (GraphForms.realCoordinates n m) ((GraphForms.realCoordinates n m).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [GraphForms.realCoordinates, BoxStokes.standardBasis]
  funext a
  simp [Pi.single_apply, eq_comm]

def nativeForm (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (y : RealCoordinates n m) : RealCoordinates n m [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ :=
  (GraphForms.topForm edges ((nativeCoordinates (n := n) (m := m)).symm y)).compContinuousLinearMap
    (nativeCoordinates (n := n) (m := m)).symm.toContinuousLinearMap

theorem density_nativeForm (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (y : RealCoordinates n m) : OrientedFormChangeVariables.density (nativeForm edges) y =
      GeometricWeights.realDensity edges y := by
  change GraphForms.topForm edges ((nativeCoordinates (n := n) (m := m)).symm y)
    (fun j => (nativeCoordinates (n := n) (m := m)).symm (BoxStokes.standardBasis _ j)) = _
  simp only [nativeCoordinates_symm_basis]
  rfl

def originalDR (q : GraphForms.Coordinates n m) : Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ :=
  CompactDRCoordinates.realCoordinates (n + 1) m (CompactDRCoordinates.dataEmbedding
    (MarkedDRIdentification.ofPositions (ForestPositiveChartSmooth.doubledRaw i q)))

theorem originalDR_eq_embedding (q : GraphForms.CoordinateDomain n m) :
    originalDR i q.val = CompactDRCoordinates.embedding i (ForestPositiveChartSmooth.originalEmbedding i q) := by
  unfold originalDR
  rw [ForestPositiveChartSmooth.doubledRaw_eq]
  rfl

def originalCutoff (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (y : RealCoordinates n m) : ℝ := ρ (originalDR i ((nativeCoordinates (n := n) (m := m)).symm y))

def originalPiece (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (y : RealCoordinates n m) : ℝ := originalCutoff i ρ y * GeometricWeights.realDensity edges y

def pieceForm (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (y : RealCoordinates n m) : RealCoordinates n m [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ :=
  originalCutoff i ρ y • nativeForm edges y

theorem density_pieceForm (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (y : RealCoordinates n m) : OrientedFormChangeVariables.density (pieceForm i edges ρ) y = originalPiece i edges ρ y := by
  change originalCutoff i ρ y * OrientedFormChangeVariables.density (nativeForm edges) y = _
  rw [density_nativeForm]
  rfl

def sourceDensity (η : Ambient i x → Ambient i x [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ)
    (z : RealCoordinates n m) : ℝ :=
  η ((sourceCoordinates i x).symm z)
    (fun j => (sourceCoordinates i x).symm (BoxStokes.standardBasis _ j))

theorem integrable_sourceDensity
    (η : Ambient i x → Ambient i x [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ)
    (hη : Continuous η) (hcpt : HasCompactSupport η) : Integrable (sourceDensity i x η) := by
  have hev : Continuous (fun form : Ambient i x [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ =>
      form (fun j => (sourceCoordinates i x).symm (BoxStokes.standardBasis _ j))) := continuous_eval_const _
  exact (hev.comp (hη.comp (sourceCoordinates i x).symm.continuous)).integrable_of_hasCompactSupport
    ((hcpt.comp_homeomorph (sourceCoordinates i x).symm.toHomeomorph).comp_left rfl)

/-- The compact smooth form is actually constructed from the ambient
partition cutoff; its scalar density is then Lebesgue integrable. -/
theorem exists_integrable_localized
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ)
    (hsub : tsupport (CompactDRAmbientPartition.cutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target) :
    ∃ κ : Ambient i x → ℝ,
      Integrable (sourceDensity i x (localized i x ρ
        (fun j => ForestPositiveGraphForms.forestEdge i (edges j) (hloop j)) κ)) ∧
      ∀ z : ForestOrthantCharts.Model i x,
        localized i x ρ (fun j => ForestPositiveGraphForms.forestEdge i (edges j) (hloop j)) κ (includeOrthant i x z) =
          ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart i x) (CompactDRAmbientPartition.cutoff i ρ) z •
            graphForm i x (fun j => ForestPositiveGraphForms.forestEdge i (edges j) (hloop j)) (includeOrthant i x z) := by
  obtain ⟨κ, hκ, hcptκ, hform, hcpt, heq⟩ := exists_localized_graphForm i x ρ
    (fun j => ForestPositiveGraphForms.forestEdge i (edges j) (hloop j)) hρ hsub
  exact ⟨κ, integrable_sourceDensity i x _ hform.continuous hcpt, heq⟩

def coordinateChart : OpenPartialHomeomorph (RealCoordinates n m) (RealCoordinates n m) :=
  ((sourceCoordinates i x).symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (ForestPositiveChartSmooth.positiveChart i x)).trans
      (nativeCoordinates (n := n) (m := m)).toHomeomorph.toOpenPartialHomeomorph

theorem coordinateChart_apply (z : RealCoordinates n m) : coordinateChart i x z =
    nativeCoordinates (ForestPositiveChartSmooth.forwardCoordinates i x ((sourceCoordinates i x).symm z)) := rfl

theorem coordinateChart_source : (coordinateChart i x).source =
    (sourceCoordinates i x).symm ⁻¹' ForestPositiveChartSmooth.Source i x := by
  simp [coordinateChart, ForestPositiveChartSmooth.positiveChart]

theorem coordinateChart_target : (coordinateChart i x).target =
    (nativeCoordinates (n := n) (m := m)).symm ⁻¹' ForestPositiveChartSmooth.Target i x := by
  simp [coordinateChart, ForestPositiveChartSmooth.positiveChart]

theorem contDiffAt_coordinateChart (z : RealCoordinates n m) (hz : z ∈ (coordinateChart i x).source) :
    ContDiffAt ℝ 1 (coordinateChart i x) z := by
  have hs : (sourceCoordinates i x).symm z ∈ ForestPositiveChartSmooth.Source i x := by simpa only [coordinateChart_source, Set.mem_preimage] using hz
  exact nativeCoordinates.contDiff.contDiffAt.comp z
    ((ForestPositiveChartSmooth.contDiffAt_forwardCoordinates_source i x _ hs).comp z
      (sourceCoordinates i x).symm.contDiff.contDiffAt)

theorem coordinateChart_target_subset : (coordinateChart i x).target ⊆ GeometricWeights.realDomain n m := by
  intro y hy
  rw [coordinateChart_target] at hy
  obtain ⟨q, hq, heq⟩ := hy
  change GraphForms.Admissible ((nativeCoordinates (n := n) (m := m)).symm y)
  rw [← heq]
  exact q.property

theorem originalPiece_zero_off_target
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hsub : tsupport (CompactDRAmbientPartition.cutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target)
    (y : RealCoordinates n m) (hy : y ∈ GeometricWeights.realDomain n m) (hnot : y ∉ (coordinateChart i x).target) :
    originalPiece i edges ρ y = 0 := by
  have hzero : originalCutoff i ρ y = 0 := by
    by_contra hzero
    let q : GraphForms.CoordinateDomain n m := ⟨(nativeCoordinates (n := n) (m := m)).symm y, hy⟩
    have hg : CompactDRAmbientPartition.cutoff i ρ (ForestPositiveChartSmooth.originalEmbedding i q) ≠ 0 := by
      change ρ (CompactDRCoordinates.embedding i (ForestPositiveChartSmooth.originalEmbedding i q)) ≠ 0
      rw [← originalDR_eq_embedding i q]
      exact hzero
    apply hnot
    rw [coordinateChart_target]
    exact ⟨q, hsub (subset_tsupport _ hg), rfl⟩
  simp [originalPiece, hzero]

theorem originalCutoff_forward
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (z : Ambient i x) (hz : z ∈ ForestPositiveChartSmooth.Source i x) :
    originalCutoff i ρ (nativeCoordinates (ForestPositiveChartSmooth.forwardCoordinates i x z)) =
      CompactDRAmbientPartition.cutoff i ρ (ForestOrthantCharts.chart i x (ForestPositiveChartSmooth.ofAmbient i x z)) := by
  unfold originalCutoff
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [originalDR_eq_embedding i ⟨_, ForestPositiveChartSmooth.forwardCoordinates_admissible i x z hz⟩,
    ForestPositiveChartSmooth.originalEmbedding_forwardCoordinates i x z hz]
  rfl

theorem fderiv_coordinateChart (z : RealCoordinates n m) (hz : z ∈ (coordinateChart i x).source) :
    fderiv ℝ (coordinateChart i x) z = nativeCoordinates.toContinuousLinearMap.comp
      ((fderiv ℝ (ForestPositiveChartSmooth.forwardCoordinates i x) ((sourceCoordinates i x).symm z)).comp
        (sourceCoordinates i x).symm.toContinuousLinearMap) := by
  have hs : (sourceCoordinates i x).symm z ∈ ForestPositiveChartSmooth.Source i x := by simpa only [coordinateChart_source, Set.mem_preimage] using hz
  exact (nativeCoordinates.hasFDerivAt.comp z
    (((ForestPositiveChartSmooth.contDiffAt_forwardCoordinates_source (ν := 1) i x _ hs).differentiableAt
      (by simp)).hasFDerivAt.comp z (sourceCoordinates i x).symm.hasFDerivAt)).fderiv

theorem density_pullback_piece
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (y : RealCoordinates n m) (hy : y ∈ (coordinateChart i x).source) :
    OrientedFormChangeVariables.density (OrientedFormChangeVariables.pullback (coordinateChart i x)
      (pieceForm i edges ρ)) y =
      CompactDRAmbientPartition.cutoff i ρ
        (ForestOrthantCharts.chart i x (ForestPositiveChartSmooth.ofAmbient i x ((sourceCoordinates i x).symm y))) *
        graphForm i x (fun j => ForestPositiveGraphForms.forestEdge i (edges j) (hloop j))
          ((sourceCoordinates i x).symm y)
          (fun j => (sourceCoordinates i x).symm (BoxStokes.standardBasis _ j)) := by
  have hs : (sourceCoordinates i x).symm y ∈ ForestPositiveChartSmooth.Source i x := by simpa only [coordinateChart_source, Set.mem_preimage] using hy
  have hinclude := ForestPositiveChartSmooth.includeOrthant_ofAmbient i x ((sourceCoordinates i x).symm y)
    (fun j => (hs.1 j).le)
  have hreg := regular_source i x _ hs.2
  rw [hinclude] at hreg
  have hform := ForestPositiveGraphForms.graphForm_eq_native i x edges hloop _ hreg
    (fun v _ => ForestPositiveChartSmooth.realization_pos i x _ hs v)
    (ForestPositiveChartSmooth.anchorPoint_im_pos i x _ hs)
  change originalCutoff i ρ (coordinateChart i x y) *
    GraphForms.topForm edges (nativeCoordinates.symm (coordinateChart i x y))
      (fun j => nativeCoordinates.symm (fderiv ℝ (coordinateChart i x) y (BoxStokes.standardBasis _ j))) = _
  rw [coordinateChart_apply, ContinuousLinearEquiv.symm_apply_apply, originalCutoff_forward i x ρ _ hs,
    fderiv_coordinateChart i x y hy, hform]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

theorem originalPiece_integrable
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ)
    (hsub : tsupport (CompactDRAmbientPartition.cutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target) :
    IntegrableOn (originalPiece i edges ρ) (GeometricWeights.realDomain n m) := by
  obtain ⟨κ, hκ, heq⟩ := exists_integrable_localized i x edges hloop ρ hρ hsub
  have hpull : IntegrableOn (OrientedFormChangeVariables.density
      (OrientedFormChangeVariables.pullback (coordinateChart i x) (pieceForm i edges ρ)))
      (coordinateChart i x).source := by
    apply (integrableOn_congr_fun _ (coordinateChart i x).open_source.measurableSet).mpr hκ.integrableOn
    intro y hy
    have hs : (sourceCoordinates i x).symm y ∈ ForestPositiveChartSmooth.Source i x := by simpa only [coordinateChart_source, Set.mem_preimage] using hy
    have hinclude := ForestPositiveChartSmooth.includeOrthant_ofAmbient i x ((sourceCoordinates i x).symm y)
      (fun j => (hs.1 j).le)
    have he := congrArg (fun form : Ambient i x [⋀^Fin (GraphForms.dimension n m)]→L[ℝ] ℝ =>
      form (fun j => (sourceCoordinates i x).symm (BoxStokes.standardBasis _ j)))
        (heq (ForestPositiveChartSmooth.ofAmbient i x ((sourceCoordinates i x).symm y)))
    rw [hinclude, ChartCutoffSupport.zeroPullback_source _ _ hs.2] at he
    rw [density_pullback_piece i x edges hloop ρ y hy]
    exact he.symm
  have himage : coordinateChart i x '' (coordinateChart i x).source ⊆ GeometricWeights.realDomain n m := by
    rw [(coordinateChart i x).image_source_eq_target]
    exact coordinateChart_target_subset i x
  have hzero : ∀ y ∈ GeometricWeights.realDomain n m \ (coordinateChart i x '' (coordinateChart i x).source),
      OrientedFormChangeVariables.density (pieceForm i edges ρ) y = 0 := by
    intro y hy
    rw [density_pieceForm]
    apply originalPiece_zero_off_target i x edges ρ hsub y hy.1
    simpa only [(coordinateChart i x).image_source_eq_target] using hy.2
  have h := (UnorientedFormIntegrability.integrableOn_domain_iff_pullback (coordinateChart i x)
    (coordinateChart i x).source (GeometricWeights.realDomain n m) (coordinateChart i x).open_source.measurableSet
    (GeometricWeights.measurableSet_realDomain n m) (contDiffAt_coordinateChart i x)
    (coordinateChart i x).injOn himage (pieceForm i edges ρ) hzero).mpr hpull
  have hd : OrientedFormChangeVariables.density (pieceForm i edges ρ) = originalPiece i edges ρ :=
    funext (density_pieceForm i edges ρ)
  rw [hd] at h
  exact h

theorem sum_originalCutoff {J : Type*} [Fintype J]
    (ρ : J → (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hsum : ∀ q : Compactification i m, ∑ j, CompactDRAmbientPartition.cutoff i (ρ j) q = 1)
    (y : RealCoordinates n m) (hy : y ∈ GeometricWeights.realDomain n m) :
    ∑ j, originalCutoff i (ρ j) y = 1 := by
  let q : GraphForms.CoordinateDomain n m := ⟨(nativeCoordinates (n := n) (m := m)).symm y, hy⟩
  have he (j : J) : originalCutoff i (ρ j) y =
      CompactDRAmbientPartition.cutoff i (ρ j) (ForestPositiveChartSmooth.originalEmbedding i q) := by
    unfold originalCutoff CompactDRAmbientPartition.cutoff
    rw [originalDR_eq_embedding i q]
  simpa only [he] using hsum (ForestPositiveChartSmooth.originalEmbedding i q)

theorem sum_originalPiece {J : Type*} [Fintype J]
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (ρ : J → (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hsum : ∀ q : Compactification i m, ∑ j, CompactDRAmbientPartition.cutoff i (ρ j) q = 1)
    (y : RealCoordinates n m) (hy : y ∈ GeometricWeights.realDomain n m) :
    ∑ j, originalPiece i edges (ρ j) y = GeometricWeights.realDensity edges y := by
  simp only [originalPiece, ← Finset.sum_mul, sum_originalCutoff i ρ hsum y hy, one_mul]

/-- Genuine absolute convergence of every nonloop top-degree original graph
weight, derived from the finite actual forest cover, constructed compact
local forms, and unsigned change of variables. -/
theorem absolutelyIntegrable_nonloop
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) : GeometricWeights.AbsolutelyIntegrable edges := by
  let i : Fin (n + 1) := 0
  obtain ⟨s, ρ, hcover, hsm, hcpt, hsub, hsum⟩ := FiniteForestOrthantPartition.exists_finite_ambient_partition (m := m) i
  have hpieces (j : s) : IntegrableOn (originalPiece i edges (ρ j)) (GeometricWeights.realDomain n m) :=
    originalPiece_integrable i j.val edges hloop (ρ j) (hsm j) (hsub j)
  have hi : IntegrableOn (fun y => ∑ j : s, originalPiece i edges (ρ j) y) (GeometricWeights.realDomain n m) :=
    integrable_finsetSum _ (fun j _ => hpieces j)
  apply (integrableOn_congr_fun (fun y hy => (sum_originalPiece i edges (fun j : s => ρ j) hsum y hy).symm)
    (GeometricWeights.measurableSet_realDomain n m)).mpr hi

/-- Every actual top-degree edge list is absolutely integrable. Self loops
are handled by the existing literal zero-form theorem. -/
theorem absolutelyIntegrable
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m) : GeometricWeights.AbsolutelyIntegrable edges := by
  by_cases hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source
  · exact absolutelyIntegrable_nonloop edges hloop
  · push Not at hloop
    obtain ⟨j, hj⟩ := hloop
    exact GeometricWeights.absolutelyIntegrable_of_selfLoop edges j hj

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability
