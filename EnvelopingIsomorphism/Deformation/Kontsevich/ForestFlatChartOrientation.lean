import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantStokes
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOrientation

/-! Orientation of the positive forest chart in the very same radial-first
coordinates used by its genuine orthant lower-face integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestFlatChartOrientation

open Set MeasureTheory ForestOrthantRealization ForestPositiveChartSmooth
open ForestGraphIntegrability OrientedFormChangeVariables ForestChartOrientation
open scoped Topology Classical ContDiff

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

def coordinates : Ambient i x ≃L[ℝ] RealCoordinates n m :=
  cast (congrArg (fun d => Ambient i x ≃L[ℝ] BoxStokes.Coord d)
    (ForestOrthantStokes.coordinateCount_eq i x)) (ForestOrthantStokes.flatCoordinates i x)

def chart : OpenPartialHomeomorph (RealCoordinates n m) (RealCoordinates n m) :=
  ((coordinates i x).symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (positiveChart i x)).trans nativeCoordinates.toHomeomorph.toOpenPartialHomeomorph

theorem chart_apply (z : RealCoordinates n m) : chart i x z =
    nativeCoordinates (forwardCoordinates i x ((coordinates i x).symm z)) := rfl

theorem chart_source : (chart i x).source = (coordinates i x).symm ⁻¹' Source i x := by
  simp [chart, positiveChart]

theorem chart_target : (chart i x).target = nativeCoordinates.symm ⁻¹' Target i x := by
  simp [chart, positiveChart]

def positiveRegion : Set (RealCoordinates n m) := (coordinates i x).symm ⁻¹' positiveBall i x

theorem positiveRegion_subset : positiveRegion i x ⊆ (chart i x).source := by
  intro z hz
  rw [chart_source]
  exact positiveBall_subset_Source i x hz

theorem isOpen_positiveRegion : IsOpen (positiveRegion i x) :=
  (isOpen_positiveBall i x).preimage (coordinates i x).symm.continuous

theorem convex_positiveRegion : Convex ℝ (positiveRegion i x) :=
  (convex_positiveBall i x).linear_preimage (coordinates i x).symm.toLinearMap

theorem isConnected_positiveRegion : IsConnected (positiveRegion i x) := by
  refine ⟨?_, (convex_positiveRegion i x).isPreconnected⟩
  obtain ⟨z, hz⟩ := positiveBall_nonempty i x
  refine ⟨coordinates i x z, ?_⟩
  change (coordinates i x).symm (coordinates i x z) ∈ positiveBall i x
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz

theorem contDiffAt_chart (z : RealCoordinates n m) (hz : z ∈ (chart i x).source)
    {ν : ℕ∞ω} : ContDiffAt ℝ ν (chart i x) z := by
  have hs : (coordinates i x).symm z ∈ Source i x := by
    simpa only [chart_source, mem_preimage] using hz
  exact nativeCoordinates.contDiff.contDiffAt.comp z
    ((contDiffAt_forwardCoordinates_source i x _ hs).comp z
      (coordinates i x).symm.contDiff.contDiffAt)

theorem contDiffAt_chart_symm (y : RealCoordinates n m) (hy : y ∈ (chart i x).target)
    {ν : ℕ∞ω} : ContDiffAt ℝ ν (chart i x).symm y := by
  have ht : nativeCoordinates.symm y ∈ Target i x := by
    simpa only [chart_target, mem_preimage] using hy
  exact (coordinates i x).contDiff.contDiffAt.comp y
    ((contDiffAt_inverseCoordinates_target i x _ ht).comp y nativeCoordinates.symm.contDiff.contDiffAt)

theorem chart_image_positiveRegion : chart i x '' positiveRegion i x = smallTarget i x := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [smallTarget, mem_preimage, chart_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨⟨_, forwardCoordinates_admissible i x _ (positiveBall_subset_Source i x hz)⟩,
      originalEmbedding_forward_mem_smallTarget i x _ hz, rfl⟩
  · rintro y ⟨q, hq, heq⟩
    let z := coordinates i x (inverseCoordinates i x q.val)
    have hz : z ∈ positiveRegion i x := by
      change (coordinates i x).symm (coordinates i x _) ∈ positiveBall i x
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact inverse_mem_positiveBall i x q hq
    refine ⟨z, hz, ?_⟩
    rw [chart_apply]
    change nativeCoordinates (forwardCoordinates i x
      ((coordinates i x).symm (coordinates i x (inverseCoordinates i x q.val)))) = y
    rw [ContinuousLinearEquiv.symm_apply_apply, forward_inverseCoordinates i x q hq.1, heq,
      ContinuousLinearEquiv.apply_symm_apply]

/-- Orientation is derived in the actual lower-face coordinate basis. The
target integral is over the genuine smaller original-configuration target. -/
theorem exists_orientation : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    (∀ z ∈ positiveRegion i x, ε * jacobian (chart i x) z = |jacobian (chart i x) z|) ∧
    ∀ η : TopForm (GraphForms.dimension n m),
      ε * (∫ z in positiveRegion i x, density (pullback (chart i x) η) z) =
        ∫ y in smallTarget i x, density η y := by
  have h := SignedFormChangeVariables.exists_signed_integral_identity (chart i x)
    (fun z hz => (contDiffAt_chart i x z hz).contDiffWithinAt)
    (fun y hy => (contDiffAt_chart_symm i x y hy).contDiffWithinAt)
    (positiveRegion i x) (isOpen_positiveRegion i x).measurableSet
    (positiveRegion_subset i x) (isConnected_positiveRegion i x).isPreconnected
  simpa only [chart_image_positiveRegion] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestFlatChartOrientation
