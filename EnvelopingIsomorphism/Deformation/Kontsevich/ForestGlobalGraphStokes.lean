import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLocalizedDerivative
import EnvelopingIsomorphism.Deformation.Kontsevich.FiniteOrientedForestPartition
import EnvelopingIsomorphism.Deformation.Kontsevich.OrientedOrthantAssembly

/-! Global graph Stokes assembled from the actual finite ambient partition,
compact small forest graph forms, and derived chart orientations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestGlobalGraphStokes

open Set Filter MeasureTheory ContinuousAlternatingMap
open BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open ForestOrthantRealization ForestPositiveChartSmooth ForestChartOrientation
open scoped Topology Classical ContDiff Manifold

/-- Reindex coordinate axes by the proved equality of dimensions. -/
def coordinateCast {a b : ℕ} (h : a = b) : Coord a ≃L[ℝ] Coord b :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : Fin b => ℝ) (finCongr h)).toContinuousLinearEquiv

theorem coordinateCast_apply {a b : ℕ} (h : a = b) (z : Coord a) (j : Fin a) :
    coordinateCast h z (finCongr h j) = z j := by
  simp [coordinateCast, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

section LinearForms

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

def linearForm (L : E ≃L[ℝ] F) (η : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    F → F [⋀^Fin k]→L[ℝ] ℝ :=
  fun z => (η (L.symm z)).compContinuousLinearMap L.symm.toContinuousLinearMap

theorem contDiff_linearForm (L : E ≃L[ℝ] F) (η : E → E [⋀^Fin k]→L[ℝ] ℝ)
    {ν : ℕ∞ω} (hη : ContDiff ℝ ν η) : ContDiff ℝ ν (linearForm L η) := by
  let A : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM L.symm.toContinuousLinearMap
  change ContDiff ℝ ν (A ∘ η ∘ L.symm)
  exact A.contDiff.comp (hη.comp L.symm.contDiff)

theorem hasCompactSupport_linearForm (L : E ≃L[ℝ] F)
    (η : E → E [⋀^Fin k]→L[ℝ] ℝ) (hη : HasCompactSupport η) :
    HasCompactSupport (linearForm L η) := by
  let A : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM L.symm.toContinuousLinearMap
  exact (hη.comp_homeomorph L.symm.toHomeomorph).comp_left (g := A) (map_zero A)

theorem tsupport_linearForm_subset (L : E ≃L[ℝ] F)
    (η : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    tsupport (linearForm L η) ⊆ L.symm ⁻¹' tsupport η := by
  let A : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) :=
    compContinuousLinearMapCLM L.symm.toContinuousLinearMap
  exact (tsupport_comp_subset (map_zero A) _).trans
    (tsupport_comp_subset_preimage η L.symm.continuous)

theorem extDeriv_linearForm (L : E ≃L[ℝ] F) (η : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (z : F) (hη : DifferentiableAt ℝ η (L.symm z)) :
    extDeriv (linearForm L η) z =
      (extDeriv η (L.symm z)).compContinuousLinearMap L.symm.toContinuousLinearMap := by
  unfold linearForm
  have h := extDeriv_pullback hη (L.symm.contDiff (n := ⊤)).contDiffAt (by simp)
  simpa only [ContinuousLinearEquiv.fderiv] using h

end LinearForms

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)

/-- The same original-coordinate basis is used for every chart in the finite family. -/
def nativeCoordinates : GraphForms.Coordinates n m ≃L[ℝ] Coord (r + 1) :=
  (ForestGraphIntegrability.nativeCoordinates (n := n) (m := m)).trans (coordinateCast hdim)

def nativeDomain : Set (Coord (r + 1)) :=
  (nativeCoordinates hdim).symm ⁻¹' GraphForms.admissibleSet n m

theorem isOpen_nativeDomain : IsOpen (nativeDomain hdim) :=
  (GraphForms.isOpen_admissibleSet n m).preimage (nativeCoordinates hdim).symm.continuous

variable (x : Compactification (0 : Fin (n + 1)) m)

def sourceCoordinates : Ambient 0 x ≃L[ℝ] Coord (r + 1) :=
  (ForestOrthantStokes.flatCoordinates 0 x).trans
    (coordinateCast ((ForestOrthantStokes.coordinateCount_eq 0 x).trans hdim))

def radialIndex (j : Fin (ForestOrthantCharts.R 0 x)) : Fin (r + 1) :=
  finCongr ((ForestOrthantStokes.coordinateCount_eq 0 x).trans hdim)
    (ForestOrthantStokes.radialIndex 0 x j)

def radialIndices : Finset (Fin (r + 1)) := Finset.univ.image (radialIndex hdim x)

theorem sourceCoordinates_radial (z : Ambient 0 x) (j : Fin (ForestOrthantCharts.R 0 x)) :
    sourceCoordinates hdim x z (radialIndex hdim x j) = z.1 j := by
  change coordinateCast _ (ForestOrthantStokes.flatCoordinates 0 x z) (finCongr _ _) = _
  rw [coordinateCast_apply, ForestOrthantStokes.flatCoordinates_radial]

theorem sourceCoordinates_mem_strictOrthant (z : Ambient 0 x) :
    sourceCoordinates hdim x z ∈ strictOrthant (radialIndices hdim x) ↔ ∀ j, 0 < z.1 j := by
  simp only [strictOrthant, mem_setOf_eq, radialIndices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hz j
    simpa only [sourceCoordinates_radial] using hz (radialIndex hdim x j) ⟨j, rfl⟩
  · rintro hz _ ⟨j, rfl⟩
    simpa only [sourceCoordinates_radial] using hz j

def chart : OpenPartialHomeomorph (Coord (r + 1)) (Coord (r + 1)) :=
  ((sourceCoordinates hdim x).symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (positiveChart 0 x)).trans (nativeCoordinates hdim).toHomeomorph.toOpenPartialHomeomorph

theorem chart_apply (z : Coord (r + 1)) : chart hdim x z =
    nativeCoordinates hdim (forwardCoordinates 0 x ((sourceCoordinates hdim x).symm z)) := rfl

theorem chart_source : (chart hdim x).source = (sourceCoordinates hdim x).symm ⁻¹' Source 0 x := by
  simp [chart, positiveChart]

theorem chart_target : (chart hdim x).target = (nativeCoordinates hdim).symm ⁻¹' Target 0 x := by
  simp [chart, positiveChart]

def positiveRegion : Set (Coord (r + 1)) :=
  (sourceCoordinates hdim x).symm ⁻¹' positiveBall 0 x

theorem positiveRegion_subset_source : positiveRegion hdim x ⊆ (chart hdim x).source := by
  intro z hz
  rw [chart_source]
  exact positiveBall_subset_Source 0 x hz

theorem isOpen_positiveRegion : IsOpen (positiveRegion hdim x) :=
  (isOpen_positiveBall 0 x).preimage (sourceCoordinates hdim x).symm.continuous

theorem isPreconnected_positiveRegion : IsPreconnected (positiveRegion hdim x) :=
  ((convex_positiveBall 0 x).linear_preimage (sourceCoordinates hdim x).symm.toLinearMap).isPreconnected

theorem isConnected_positiveRegion : IsConnected (positiveRegion hdim x) := by
  refine ⟨?_, isPreconnected_positiveRegion hdim x⟩
  obtain ⟨z, hz⟩ := positiveBall_nonempty 0 x
  refine ⟨sourceCoordinates hdim x z, ?_⟩
  change (sourceCoordinates hdim x).symm (sourceCoordinates hdim x z) ∈ positiveBall 0 x
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz

theorem positiveRegion_subset_strictOrthant :
    positiveRegion hdim x ⊆ strictOrthant (radialIndices hdim x) := by
  intro z hz
  have h := (sourceCoordinates_mem_strictOrthant hdim x ((sourceCoordinates hdim x).symm z)).mpr hz.2
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem contDiffAt_chart (z : Coord (r + 1)) (hz : z ∈ (chart hdim x).source)
    {ν : ℕ∞ω} : ContDiffAt ℝ ν (chart hdim x) z := by
  have hs : (sourceCoordinates hdim x).symm z ∈ Source 0 x := by
    simpa only [chart_source, mem_preimage] using hz
  exact (nativeCoordinates hdim).contDiff.contDiffAt.comp z
    ((contDiffAt_forwardCoordinates_source 0 x _ hs).comp z
      (sourceCoordinates hdim x).symm.contDiff.contDiffAt)

theorem contDiffAt_chart_symm (y : Coord (r + 1)) (hy : y ∈ (chart hdim x).target)
    {ν : ℕ∞ω} : ContDiffAt ℝ ν (chart hdim x).symm y := by
  have ht : (nativeCoordinates hdim).symm y ∈ Target 0 x := by
    simpa only [chart_target, mem_preimage] using hy
  exact (sourceCoordinates hdim x).contDiff.contDiffAt.comp y
    ((contDiffAt_inverseCoordinates_target 0 x _ ht).comp y (nativeCoordinates hdim).symm.contDiff.contDiffAt)

theorem chart_image_subset_nativeDomain : chart hdim x '' positiveRegion hdim x ⊆ nativeDomain hdim := by
  rintro y ⟨z, hz, rfl⟩
  change GraphForms.Admissible ((nativeCoordinates hdim).symm (chart hdim x z))
  rw [chart_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact forwardCoordinates_admissible 0 x _ (positiveBall_subset_Source 0 x hz)

theorem mem_chart_image_of_smallTarget (q : GraphForms.CoordinateDomain n m)
    (hq : originalEmbedding 0 q ∈ (smallChart 0 x).target) :
    nativeCoordinates hdim q.val ∈ chart hdim x '' positiveRegion hdim x := by
  let z := sourceCoordinates hdim x (inverseCoordinates 0 x q.val)
  refine ⟨z, ?_, ?_⟩
  · change (sourceCoordinates hdim x).symm (sourceCoordinates hdim x _) ∈ positiveBall 0 x
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact inverse_mem_positiveBall 0 x q hq
  · rw [chart_apply]
    change nativeCoordinates hdim (forwardCoordinates 0 x
      ((sourceCoordinates hdim x).symm (sourceCoordinates hdim x (inverseCoordinates 0 x q.val)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply, forward_inverseCoordinates 0 x q hq.1]

theorem fderiv_chart (z : Coord (r + 1)) (hz : z ∈ (chart hdim x).source) :
    fderiv ℝ (chart hdim x) z = (nativeCoordinates hdim).toContinuousLinearMap.comp
      ((fderiv ℝ (forwardCoordinates 0 x) ((sourceCoordinates hdim x).symm z)).comp
        (sourceCoordinates hdim x).symm.toContinuousLinearMap) := by
  have hs : (sourceCoordinates hdim x).symm z ∈ Source 0 x := by
    simpa only [chart_source, mem_preimage] using hz
  exact ((nativeCoordinates hdim).hasFDerivAt.comp z
    (((contDiffAt_forwardCoordinates_source (ν := 1) 0 x _ hs).differentiableAt (by simp)).hasFDerivAt.comp z
      (sourceCoordinates hdim x).symm.hasFDerivAt)).fderiv

def localForm (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ) : Form r :=
  linearForm (sourceCoordinates hdim x) (ForestOrthantLocalization.localized 0 x ρ
    (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ)

def nativeForm (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m) : Form r :=
  linearForm (nativeCoordinates hdim) (ForestLocalizedDerivative.originalPiece ρ edges)

theorem extDeriv_nativeForm (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (y : Coord (r + 1)) (hy : y ∈ nativeDomain hdim) :
    extDeriv (nativeForm hdim ρ edges) y =
      (extDeriv (ForestLocalizedDerivative.originalPiece ρ edges)
        ((nativeCoordinates hdim).symm y)).compContinuousLinearMap
          (nativeCoordinates hdim).symm.toContinuousLinearMap :=
  extDeriv_linearForm _ _ y ((ForestLocalizedDerivative.contDiffAt_originalPiece ρ hρ edges hloop _ hy).differentiableAt (by simp))

theorem extDeriv_localForm_match
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ)
    (hη : ContDiff ℝ ∞ (ForestOrthantLocalization.localized 0 x ρ
      (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ))
    (heq : ∀ z : ForestOrthantCharts.Model 0 x,
      ForestOrthantLocalization.localized 0 x ρ
        (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ (includeOrthant 0 x z) =
        ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x)
          (CompactDRAmbientPartition.cutoff 0 ρ) z • ForestOrthantGraphForms.graphForm 0 x
            (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) (includeOrthant 0 x z)) :
    EqOn (extDeriv (localForm hdim x ρ edges hloop κ))
      (OrientedFormChangeVariables.pullback (chart hdim x) (extDeriv (nativeForm hdim ρ edges)))
        (positiveRegion hdim x) := by
  intro z hz
  have hs := positiveRegion_subset_source hdim x hz
  have hs' := positiveBall_subset_Source 0 x hz
  have hn := chart_image_subset_nativeDomain hdim x (mem_image_of_mem _ hz)
  rw [localForm, extDeriv_linearForm _ _ z (hη.differentiable (by simp) _)]
  rw [ForestLocalizedDerivative.extDeriv_localized_eq_native_pullback x ρ hρ edges hloop κ heq _ hs']
  unfold OrientedFormChangeVariables.pullback
  rw [extDeriv_nativeForm hdim ρ hρ edges hloop _ hn, fderiv_chart hdim x z hs, chart_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem localForm_support (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ)
    (hsupp : tsupport (ForestOrthantLocalization.localized 0 x ρ
      (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ) ⊆
        Metric.ball (ForestChartOrientation.center 0 x) (radius 0 x)) :
    tsupport (localForm hdim x ρ edges hloop κ) ∩ strictOrthant (radialIndices hdim x) ⊆
      positiveRegion hdim x := by
  intro z hz
  refine ⟨hsupp (tsupport_linearForm_subset _ _ hz.1), ?_⟩
  apply (sourceCoordinates_mem_strictOrthant hdim x ((sourceCoordinates hdim x).symm z)).mp
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz.2

theorem extDeriv_nativeForm_zero_off_image
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hnonneg : ∀ z, 0 ≤ ρ z) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (hsub : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (smallChart 0 x).target)
    (y : Coord (r + 1)) (hy : y ∈ nativeDomain hdim \ (chart hdim x '' positiveRegion hdim x)) :
    OrientedFormChangeVariables.density (extDeriv (nativeForm hdim ρ edges)) y = 0 := by
  let q : GraphForms.CoordinateDomain n m := ⟨(nativeCoordinates hdim).symm y, hy.1⟩
  have hnot : originalEmbedding 0 q ∉ (smallChart 0 x).target := by
    intro hq
    have h := mem_chart_image_of_smallTarget hdim x q hq
    exact hy.2 (by simpa only [q, ContinuousLinearEquiv.apply_symm_apply] using h)
  have hzero : OriginalPartitionCancellation.pullCutoff ρ q.val = 0 := by
    rw [OriginalPartitionCancellation.pullCutoff_eq_global ρ q,
      ← ForestLocalizedDerivative.originalEmbedding_zero q]
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hnot (hsub h)
  have hd := ForestLocalizedDerivative.extDeriv_originalPiece_eq_zero_of_cutoff_zero
    ρ hρ hnonneg edges hloop q.val q.property hzero
  unfold OrientedFormChangeVariables.density
  rw [extDeriv_nativeForm hdim ρ hρ edges hloop y hy.1]
  change (extDeriv (ForestLocalizedDerivative.originalPiece ρ edges) q.val)
    (fun j => (nativeCoordinates hdim).symm (standardBasis (r + 1) j)) = 0
  rw [hd]
  rfl

theorem sum_extDeriv_nativeForm {J : Type*} [Fintype J]
    (ρ : OriginalPartitionCancellation.Partition J n m)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (y : Coord (r + 1)) (hy : y ∈ nativeDomain hdim) :
    ∑ j, extDeriv (nativeForm hdim (ρ j) edges) y = 0 := by
  have h := OriginalPartitionCancellation.sum_extDeriv_graphPieces_zero ρ edges hloop hy
  apply ContinuousAlternatingMap.ext
  intro v
  have hv := congrArg (fun A => A (fun j => (nativeCoordinates hdim).symm (v j))) h
  change (∑ j, extDeriv (OriginalPartitionCancellation.localized
    (OriginalPartitionCancellation.pullCutoff (ρ j)) (GraphForms.topForm edges))
      ((nativeCoordinates hdim).symm y)) (fun j => (nativeCoordinates hdim).symm (v j)) = 0 at hv
  simp only [ContinuousAlternatingMap.sum_apply] at hv ⊢
  change (∑ j, extDeriv (nativeForm hdim (ρ j) edges) y v) = 0
  rw [← hv]
  apply Finset.sum_congr rfl
  intro j _
  rw [extDeriv_nativeForm hdim (ρ j) (CompactSmoothPartition.partition_contDiff ρ j) edges hloop y hy]
  rfl

/-- The finite partition, compact local graph forms, and their genuine
orientations are constructed. For every nonloop graph of degree dimension
minus one, the sum of actual oriented lower-face integrals is zero. -/
theorem exists_boundary_cancellation
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) :
    ∃ (s : Finset (Compactification (0 : Fin (n + 1)) m))
      (ρ : OriginalPartitionCancellation.Partition s n m)
      (κ : ∀ j : s, Ambient 0 j.val → ℝ) (ε : s → ℝ),
      (∀ y : Compactification (0 : Fin (n + 1)) m,
        ∃ j : s, y ∈ (smallChart 0 j.val).target) ∧
      (∀ j : s, tsupport (CompactDRAmbientPartition.cutoff 0 (ρ j)) ⊆ (smallChart 0 j.val).target) ∧
      (∀ j : s, ContDiff ℝ ∞ (κ j) ∧ HasCompactSupport (κ j)) ∧
      (∀ j : s, ContDiff ℝ 1 (localForm hdim j.val (ρ j) edges hloop (κ j)) ∧
        HasCompactSupport (localForm hdim j.val (ρ j) edges hloop (κ j))) ∧
      (∀ j : s, ∀ z : ForestOrthantCharts.Model 0 j.val,
        ForestOrthantLocalization.localized 0 j.val (ρ j)
          (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) (κ j)
            (includeOrthant 0 j.val z) =
          ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 j.val)
            (CompactDRAmbientPartition.cutoff 0 (ρ j)) z •
              ForestOrthantGraphForms.graphForm 0 j.val
                (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a))
                  (includeOrthant 0 j.val z)) ∧
      (∀ j : s, ε j = 1 ∨ ε j = -1) ∧
      (∀ j : s, ∀ z ∈ positiveRegion hdim j.val,
        ε j * OrientedFormChangeVariables.jacobian (chart hdim j.val) z =
          |OrientedFormChangeVariables.jacobian (chart hdim j.val) z|) ∧
      (∀ j : s, IntegrableOn (OrientedFormChangeVariables.density
        (extDeriv (nativeForm hdim (ρ j) edges))) (nativeDomain hdim)) ∧
      ∑ j : s, ε j * OrientedOrthantAssembly.lowerFaces
        (localForm hdim j.val (ρ j) edges hloop (κ j)) (radialIndices hdim j.val) = 0 := by
  obtain ⟨s, ρ, _, hcover, hρsm, _, hsub, _, _, _, _⟩ :=
    FiniteOrientedForestPartition.exists_finite_oriented_partition (m := m) (0 : Fin (n + 1))
  choose κ hκ hcκ hη hcη hsη hsdη heq using fun j : s =>
    ForestSmallLocalization.exists_localized_graphForm 0 j.val (ρ j) (hρsm j)
      (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) (hsub j)
  have hθ (j : s) : ContDiff ℝ 1 (localForm hdim j.val (ρ j) edges hloop (κ j)) :=
    contDiff_linearForm _ _ ((hη j).of_le (by simp))
  have hcθ (j : s) : HasCompactSupport (localForm hdim j.val (ρ j) edges hloop (κ j)) :=
    hasCompactSupport_linearForm _ _ (hcη j)
  obtain ⟨ε, hε, hsign, hL1, hboundary⟩ :=
    OrientedOrthantAssembly.exists_finite_signed_boundary_cancellation
      (fun j : s => chart hdim j.val)
      (fun j z hz => (contDiffAt_chart hdim j.val z hz).contDiffWithinAt)
      (fun j y hy => (contDiffAt_chart_symm hdim j.val y hy).contDiffWithinAt)
      (fun j : s => positiveRegion hdim j.val) (nativeDomain hdim)
      (fun j => (isOpen_positiveRegion hdim j.val).measurableSet) (isOpen_nativeDomain hdim).measurableSet
      (fun j => positiveRegion_subset_source hdim j.val)
      (fun j => isPreconnected_positiveRegion hdim j.val)
      (fun j => chart_image_subset_nativeDomain hdim j.val)
      (fun j => radialIndices hdim j.val) (fun j => positiveRegion_subset_strictOrthant hdim j.val)
      (fun j => localForm hdim j.val (ρ j) edges hloop (κ j))
      (fun j => nativeForm hdim (ρ j) edges) hθ hcθ
      (fun j => localForm_support hdim j.val (ρ j) edges hloop (κ j) (hsη j))
      (fun j => extDeriv_localForm_match hdim j.val (ρ j) (hρsm j) edges hloop (κ j) (hη j) (heq j))
      (fun j => extDeriv_nativeForm_zero_off_image hdim j.val (ρ j) (hρsm j)
        (ρ.nonneg j) edges hloop (hsub j))
      (sum_extDeriv_nativeForm hdim ρ edges hloop)
  exact ⟨s, ρ, κ, ε, hcover, hsub, fun j => ⟨hκ j, hcκ j⟩,
    fun j => ⟨hθ j, hcθ j⟩, heq, hε, hsign, hL1, hboundary⟩

/-- The dimension-minus-one specialization retains the full constructed
partition, local graph forms, orientation certificates, and boundary sum. -/
theorem exists_boundary_cancellation_pred
    (hpos : 0 < GraphForms.dimension n m)
    (edges : Fin (GraphForms.dimension n m - 1) → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) :
    let hdegree : GraphForms.dimension n m = (GraphForms.dimension n m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)).symm
    ∃ (s : Finset (Compactification (0 : Fin (n + 1)) m))
      (ρ : OriginalPartitionCancellation.Partition s n m)
      (κ : ∀ j : s, Ambient 0 j.val → ℝ) (ε : s → ℝ),
      (∀ y : Compactification (0 : Fin (n + 1)) m,
        ∃ j : s, y ∈ (smallChart 0 j.val).target) ∧
      (∀ j : s, tsupport (CompactDRAmbientPartition.cutoff 0 (ρ j)) ⊆ (smallChart 0 j.val).target) ∧
      (∀ j : s, ContDiff ℝ ∞ (κ j) ∧ HasCompactSupport (κ j)) ∧
      (∀ j : s, ContDiff ℝ 1 (localForm hdegree j.val (ρ j) edges hloop (κ j)) ∧
        HasCompactSupport (localForm hdegree j.val (ρ j) edges hloop (κ j))) ∧
      (∀ j : s, ∀ z : ForestOrthantCharts.Model 0 j.val,
        ForestOrthantLocalization.localized 0 j.val (ρ j)
          (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) (κ j)
            (includeOrthant 0 j.val z) =
          ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 j.val)
            (CompactDRAmbientPartition.cutoff 0 (ρ j)) z •
              ForestOrthantGraphForms.graphForm 0 j.val
                (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a))
                  (includeOrthant 0 j.val z)) ∧
      (∀ j : s, ε j = 1 ∨ ε j = -1) ∧
      (∀ j : s, ∀ z ∈ positiveRegion hdegree j.val,
        ε j * OrientedFormChangeVariables.jacobian (chart hdegree j.val) z =
          |OrientedFormChangeVariables.jacobian (chart hdegree j.val) z|) ∧
      (∀ j : s, IntegrableOn (OrientedFormChangeVariables.density
        (extDeriv (nativeForm hdegree (ρ j) edges))) (nativeDomain hdegree)) ∧
      ∑ j : s, ε j * OrientedOrthantAssembly.lowerFaces
        (localForm hdegree j.val (ρ j) edges hloop (κ j)) (radialIndices hdegree j.val) = 0 := by
  dsimp only
  exact exists_boundary_cancellation _ edges hloop

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestGlobalGraphStokes
