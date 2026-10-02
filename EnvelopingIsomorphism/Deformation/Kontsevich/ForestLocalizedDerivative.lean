import EnvelopingIsomorphism.Deformation.Kontsevich.ForestFlatChartOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.OriginalPartitionCancellation
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestSmallLocalization
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The exterior derivative of each genuinely compact forest graph piece
matches the actual original cutoff graph derivative on the positive source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestLocalizedDerivative

open Set Filter ContinuousAlternatingMap ForestOrthantRealization
open ForestPositiveChartSmooth ForestOrthantLocalization ForestOrthantGraphForms
open ForestGraphIntegrability
open scoped Topology Classical ContDiff

variable {n m : ℕ}

theorem originalEmbedding_zero (q : GraphForms.CoordinateDomain n m) :
    originalEmbedding 0 q = OriginalDRSmooth.originalPoint q := by
  unfold originalEmbedding OriginalDRSmooth.originalPoint
  apply congrArg (compactificationEmbedding (0 : Fin (n + 1)))
  apply Subtype.ext
  apply Configuration.ext
  · funext j
    simp [toNormalized, Configuration.relabelInterior, GraphForms.toNormalized]
  · rfl

theorem originalDR_zero_eq_real (q : GraphForms.CoordinateDomain n m) :
    originalDR 0 q.val = OriginalDRSmooth.real q.val := by
  rw [originalDR_eq_embedding, originalEmbedding_zero, OriginalDRSmooth.real_eq_embedding]

variable (x : Compactification (0 : Fin (n + 1)) m)

abbrev NativeForm (r : ℕ) := GraphForms.Coordinates n m →
  GraphForms.Coordinates n m [⋀^Fin r]→L[ℝ] ℝ

def originalPiece {r : ℕ} (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m) : NativeForm (n := n) (m := m) r :=
  OriginalPartitionCancellation.localized (OriginalPartitionCancellation.pullCutoff ρ)
    (GraphForms.topForm edges)

theorem contDiffAt_originalPiece {r : ℕ} (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (q : GraphForms.Coordinates n m) (hq : GraphForms.Admissible q) :
    ContDiffAt ℝ ∞ (originalPiece ρ edges) q :=
  (OriginalPartitionCancellation.contDiffAt_pullCutoff ρ hρ hq).smul
    ((GraphForms.contDiffAt_topForm edges hloop hq).of_le le_top)

theorem originalCutoff_forward_eq (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (z : Ambient 0 x) (hz : z ∈ Source 0 x) :
    OriginalPartitionCancellation.pullCutoff ρ (forwardCoordinates 0 x z) =
      CompactDRAmbientPartition.cutoff 0 ρ
        (ForestOrthantCharts.chart 0 x (ofAmbient 0 x z)) := by
  have h := originalCutoff_forward 0 x ρ z hz
  unfold originalCutoff at h
  rw [ContinuousLinearEquiv.symm_apply_apply,
    originalDR_zero_eq_real ⟨_, forwardCoordinates_admissible 0 x z hz⟩] at h
  exact h

/-- Nonnegative actual partition cutoffs have zero derivative wherever they
vanish. This gives the required zero extension of the native derivative piece. -/
theorem extDeriv_originalPiece_eq_zero_of_cutoff_zero {r : ℕ}
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hnonneg : ∀ z, 0 ≤ ρ z) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (q : GraphForms.Coordinates n m) (hq : GraphForms.Admissible q)
    (hzero : OriginalPartitionCancellation.pullCutoff ρ q = 0) :
    extDeriv (originalPiece ρ edges) q = 0 := by
  have hmin : IsLocalMin (OriginalPartitionCancellation.pullCutoff ρ) q := by
    filter_upwards [] with y
    rw [hzero]
    exact hnonneg _
  have hd := hmin.fderiv_eq_zero
  rw [originalPiece, OriginalPartitionCancellation.extDeriv_localized _ _ q
    ((OriginalPartitionCancellation.contDiffAt_pullCutoff ρ hρ hq).differentiableAt (by simp))
    ((GraphForms.contDiffAt_topForm edges hloop hq).differentiableAt (by simp))]
  simp [hzero, OriginalPartitionCancellation.cutoffTerm, hd]
  exact map_zero (alternatizeUncurryFinCLM ℝ _ ℝ)

theorem extDeriv_originalPiece_zero_off_smallTarget {r : ℕ}
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hnonneg : ∀ z, 0 ≤ ρ z) (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (hsub : tsupport (globalCutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
    (y : RealCoordinates n m) (hy : y ∈ GeometricWeights.realDomain n m)
    (hnot : y ∉ ForestChartOrientation.smallTarget 0 x) :
    extDeriv (originalPiece ρ edges) (nativeCoordinates.symm y) = 0 := by
  apply extDeriv_originalPiece_eq_zero_of_cutoff_zero ρ hρ hnonneg edges hloop _ hy
  have h := ForestChartOrientation.originalCutoff_zero_off_smallTarget 0 x ρ hsub y hy hnot
  unfold originalCutoff at h
  change ρ (originalDR 0 ((GraphForms.realCoordinates n m).symm y)) = 0 at h
  rwa [originalDR_zero_eq_real ⟨_, hy⟩] at h

theorem localized_eq_native_pullback {r : ℕ}
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ)
    (heq : ∀ z : ForestOrthantCharts.Model 0 x,
      localized 0 x ρ (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ
        (includeOrthant 0 x z) =
          ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x)
            (CompactDRAmbientPartition.cutoff 0 ρ) z •
              graphForm 0 x (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))
                (includeOrthant 0 x z))
    (z : Ambient 0 x) (hz : z ∈ Source 0 x) :
    localized 0 x ρ (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ z =
      (originalPiece ρ edges (forwardCoordinates 0 x z)).compContinuousLinearMap
        (fderiv ℝ (forwardCoordinates 0 x) z) := by
  have hincl := includeOrthant_ofAmbient 0 x z (fun j => (hz.1 j).le)
  have h := heq (ofAmbient 0 x z)
  rw [hincl, ChartCutoffSupport.zeroPullback_source _ _ hz.2] at h
  rw [h, ← originalCutoff_forward_eq x ρ z hz]
  have hreg := regular_source 0 x _ hz.2
  rw [hincl] at hreg
  rw [ForestPositiveGraphForms.graphForm_eq_native 0 x edges hloop z hreg
    (fun v _ => realization_pos 0 x z hz v) (anchorPoint_im_pos 0 x z hz)]
  rfl

/-- The source is open, so equality of the actual graph pieces on it gives
equality of their actual exterior derivatives, by the smooth pullback rule. -/
theorem extDeriv_localized_eq_native_pullback {r : ℕ}
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (κ : Ambient 0 x → ℝ)
    (heq : ∀ z : ForestOrthantCharts.Model 0 x,
      localized 0 x ρ (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ
        (includeOrthant 0 x z) =
          ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x)
            (CompactDRAmbientPartition.cutoff 0 ρ) z •
              graphForm 0 x (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))
                (includeOrthant 0 x z))
    (z : Ambient 0 x) (hz : z ∈ Source 0 x) :
    extDeriv (localized 0 x ρ
      (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ) z =
        (extDeriv (originalPiece ρ edges) (forwardCoordinates 0 x z)).compContinuousLinearMap
          (fderiv ℝ (forwardCoordinates 0 x) z) := by
  have hevent := Filter.eventuallyEq_of_mem ((isOpen_Source 0 x).mem_nhds hz)
    (fun y hy => localized_eq_native_pullback x ρ edges hloop κ heq y hy)
  rw [hevent.extDeriv_eq]
  exact extDeriv_pullback
    ((contDiffAt_originalPiece ρ hρ edges hloop _ (forwardCoordinates_admissible 0 x z hz)).differentiableAt (by simp))
    (contDiffAt_forwardCoordinates_source (ν := ⊤) 0 x z hz) (by simp)

/-- Actual compact local graph forms and their derivative matching are
constructed together, with support in the chosen connected source ball. -/
theorem exists_small_localized_derivative_match {r : ℕ}
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    (hsub : tsupport (globalCutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target) :
    ∃ κ : Ambient 0 x → ℝ,
      ContDiff ℝ ∞ (localized 0 x ρ
        (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ) ∧
      HasCompactSupport (localized 0 x ρ
        (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ) ∧
      tsupport (extDeriv (localized 0 x ρ
        (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ)) ⊆
          Metric.ball (ForestChartOrientation.center 0 x) (ForestChartOrientation.radius 0 x) ∧
      (∀ z : ForestOrthantCharts.Model 0 x,
        localized 0 x ρ (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ
          (includeOrthant 0 x z) =
            ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x) (globalCutoff 0 ρ) z •
              graphForm 0 x (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j))
                (includeOrthant 0 x z)) ∧
      ∀ z ∈ Source 0 x,
        extDeriv (localized 0 x ρ
          (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) κ) z =
            (extDeriv (originalPiece ρ edges) (forwardCoordinates 0 x z)).compContinuousLinearMap
              (fderiv ℝ (forwardCoordinates 0 x) z) := by
  obtain ⟨κ, _, _, hη, hcη, _, hsdη, heq⟩ := ForestSmallLocalization.exists_localized_graphForm 0 x
    ρ hρ (fun j => ForestPositiveGraphForms.forestEdge 0 (edges j) (hloop j)) hsub
  exact ⟨κ, hη, hcη, hsdη, heq,
    extDeriv_localized_eq_native_pullback x ρ hρ edges hloop κ heq⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestLocalizedDerivative
