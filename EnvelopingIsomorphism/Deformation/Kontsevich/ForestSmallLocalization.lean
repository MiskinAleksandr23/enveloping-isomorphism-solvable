import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOrientation
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactSupportBoxes

/-! Actual compact graph forms supported inside the smaller convex source
ball. This support property applies to their exterior derivatives as well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestSmallLocalization

open Set ForestOrthantRealization ForestOrthantLocalization ForestChartOrientation
open scoped Topology Classical ContDiff

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

theorem pulledSupport_subset_ball
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hsub : tsupport (globalCutoff i ρ) ⊆ (smallChart i x).target) :
    (includeOrthant i x) '' ChartCutoffSupport.pulledSupport
      (ForestOrthantCharts.chart i x) (globalCutoff i ρ) ⊆ Metric.ball (center i x) (radius i x) := by
  rintro z ⟨p, ⟨q, hq, rfl⟩, rfl⟩
  exact (hsub hq).2

/-- A second actual ambient cutoff shrinks the already constructed smooth
graph form, while remaining one on its entire pulled global support. -/
theorem exists_localized_graphForm {r : ℕ}
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ)
    (edges : Fin r → ForestGraphTopForms.Edge (n + 1) m)
    (hsub : tsupport (globalCutoff i ρ) ⊆ (smallChart i x).target) :
    ∃ κ : Ambient i x → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      ContDiff ℝ ∞ (localized i x ρ edges κ) ∧ HasCompactSupport (localized i x ρ edges κ) ∧
      tsupport (localized i x ρ edges κ) ⊆ Metric.ball (center i x) (radius i x) ∧
      tsupport (extDeriv (localized i x ρ edges κ)) ⊆ Metric.ball (center i x) (radius i x) ∧
      ∀ z : ForestOrthantCharts.Model i x, localized i x ρ edges κ (includeOrthant i x z) =
        ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart i x) (globalCutoff i ρ) z •
          ForestOrthantGraphForms.graphForm i x edges (includeOrthant i x z) := by
  have hsubOld := hsub.trans (smallChart_target_subset i x)
  obtain ⟨κ₁, hκ₁, hcκ₁, hη₁, hcη₁, heq₁⟩ :=
    ForestOrthantLocalization.exists_localized_graphForm i x ρ edges hρ hsubOld
  let K := (includeOrthant i x) '' ChartCutoffSupport.pulledSupport
    (ForestOrthantCharts.chart i x) (globalCutoff i ρ)
  have hK : IsCompact K := (ChartCutoffSupport.isCompact_pulledSupport _ _ hsubOld).image
    (continuous_includeOrthant i x)
  obtain ⟨κ₂, hκ₂, hcκ₂, hsκ₂, hone⟩ := exists_smooth_cutoff i x K
    (Metric.ball (center i x) (radius i x)) hK Metric.isOpen_ball (pulledSupport_subset_ball i x ρ hsub)
  let κ := fun z => κ₂ z * κ₁ z
  have hηeq : localized i x ρ edges κ = fun z => κ₂ z • localized i x ρ edges κ₁ z := by
    funext z
    simp only [localized, κ, smul_smul, mul_assoc]
  have hsη : tsupport (localized i x ρ edges κ) ⊆ Metric.ball (center i x) (radius i x) := by
    rw [hηeq]
    exact (tsupport_smul_subset_left _ _).trans hsκ₂
  refine ⟨κ, hκ₂.mul hκ₁, hcκ₂.mul_right, ?_, ?_, hsη,
    (CompactSupportBoxes.tsupport_extDeriv_subset _).trans hsη, ?_⟩
  · rw [hηeq]
    exact hκ₂.smul hη₁
  · rw [hηeq]
    exact hcκ₂.smul_right
  · intro z
    simp only [hηeq, heq₁ z]
    by_cases hz : ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart i x) (globalCutoff i ρ) z = 0
    · simp only [hz, zero_smul, smul_zero]
    · have hp := ChartCutoffSupport.support_zeroPullback_subset
        (ForestOrthantCharts.chart i x) (globalCutoff i ρ) hz
      rw [hone (Set.mem_image_of_mem _ hp), one_smul]

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestSmallLocalization
