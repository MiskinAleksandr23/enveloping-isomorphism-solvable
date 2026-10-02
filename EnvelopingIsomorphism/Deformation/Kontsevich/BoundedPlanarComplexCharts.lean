import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarComplexForestCharts
import Mathlib.Analysis.Normed.Group.Bounded

/-! Quantitative compact bounds for the actual holomorphic forest units, their
reciprocals, and first derivatives on smaller closed complex chart balls. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundedPlanarComplexCharts

open Configuration InteriorFiberAngleSplit PlanarComplexForestCharts
open scoped Classical Topology

variable {N : ℕ} (a : Point N) (x : Compactification a 0) (hx : PlanarClusterFiber.IsFiber a x)

def unitLocus : Set (Coordinates a x hx) :=
  ComplexForestFreeShapes.parameters (upperTree a x hx) (marks a x hx) ⁻¹'
    ComplexForestNormalizedCharts.unitLocus (upperTree a x hx) (leaf a x hx)

theorem centerFree_ne_zero (v : ComplexForestFreeShapes.Free (upperTree a x hx) (marks a x hx)) :
    centerFree a x hx v ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr ((nativeChild_injective a x hx v.1).ne v.2.property.1))
    (childDenominator_ne_zero a x hx v.1)

def freeLocus : Set (Coordinates a x hx) := {z | ∀ v, z.2 v ≠ 0}

theorem isOpen_freeLocus : IsOpen (freeLocus a x hx) := by
  have he : freeLocus a x hx = ⋂ v, {z : Coordinates a x hx | z.2 v ≠ 0} := by
    ext z; simp [freeLocus]
  rw [he]
  exact isOpen_iInter_of_finite fun v ↦ isOpen_ne_fun ((continuous_apply v).comp continuous_snd) continuous_const

theorem bounded_closed_neighborhood : ∃ ε : ℝ, 0 < ε ∧
    Metric.closedBall (0, centerFree a x hx) ε ⊆ unitLocus a x hx ∧
    Metric.closedBall (0, centerFree a x hx) ε ⊆ freeLocus a x hx ∧
    ∀ j k b c : Point N, j ≠ k → b ≠ c →
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.closedBall (0, centerFree a x hx) ε,
        ‖unit a x hx j k b c z‖ ≤ C ∧ ‖(unit a x hx j k b c z)⁻¹‖ ≤ C ∧
          ‖fderiv ℂ (unit a x hx j k b c) z‖ ≤ C := by
  obtain ⟨r₀, hr₀, hball₀⟩ := bounded_corner_neighborhood a x hx
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp (isOpen_freeLocus a x hx)
    (0, centerFree a x hx) (centerFree_ne_zero a x hx)
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hball : Metric.ball (0, centerFree a x hx) r ⊆ unitLocus a x hx :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball₀
  have hfree : Metric.closedBall (0, centerFree a x hx) (r / 2) ⊆ freeLocus a x hx :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith [min_le_right r₀ r₁])).trans hball₁
  have hsub : Metric.closedBall (0, centerFree a x hx) (r / 2) ⊆ unitLocus a x hx :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨r / 2, half_pos hr, hsub, hfree, fun j k b c hjk hbc ↦ ?_⟩
  have han : AnalyticOnNhd ℂ (unit a x hx j k b c) (unitLocus a x hx) :=
    ComplexForestFreeShapes.analyticOnNhd_unit _ _ _ j k b c hjk hbc
  have hne : ∀ z ∈ unitLocus a x hx, unit a x hx j k b c z ≠ 0 :=
    fun z hz ↦ ComplexForestNormalizedCharts.unit_ne_zero _ _ hz j k b c hjk hbc
  have hc := isCompact_closedBall ((0, centerFree a x hx) : Coordinates a x hx) (r / 2)
  obtain ⟨C₀, hC₀⟩ := hc.exists_bound_of_continuousOn (han.continuousOn.mono hsub)
  have hi : ContinuousOn (fun z ↦ (unit a x hx j k b c z)⁻¹)
      (Metric.closedBall (0, centerFree a x hx) (r / 2)) :=
    fun z hz ↦ ((han z (hsub hz)).inv (hne z (hsub hz))).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hc.exists_bound_of_continuousOn hi
  have hd : ContinuousOn (fderiv ℂ (unit a x hx j k b c))
      (Metric.closedBall (0, centerFree a x hx) (r / 2)) := fun z hz ↦
    ((han z (hsub hz)).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn hd
  refine ⟨|C₀| + |C₁| + |C₂| + 1, by positivity, fun z hz ↦ ?_⟩
  have h₀ := (hC₀ z hz).trans (le_abs_self C₀)
  have h₁ := (hC₁ z hz).trans (le_abs_self C₁)
  have h₂ := (hC₂ z hz).trans (le_abs_self C₂)
  have ha₀ := abs_nonneg C₀
  have ha₁ := abs_nonneg C₁
  have ha₂ := abs_nonneg C₂
  exact ⟨by linarith, by linarith, by linarith⟩

def radius : ℝ := (bounded_closed_neighborhood a x hx).choose

theorem radius_pos : 0 < radius a x hx := (bounded_closed_neighborhood a x hx).choose_spec.1

def ball : Set (Coordinates a x hx) := Metric.ball (0, centerFree a x hx) (radius a x hx)

theorem ball_subset_unitLocus : ball a x hx ⊆ unitLocus a x hx :=
  Metric.ball_subset_closedBall.trans (bounded_closed_neighborhood a x hx).choose_spec.2.1

theorem ball_subset_freeLocus : ball a x hx ⊆ freeLocus a x hx :=
  Metric.ball_subset_closedBall.trans (bounded_closed_neighborhood a x hx).choose_spec.2.2.1

theorem uniform_unit_bounds (j k b c : Point N) (hjk : j ≠ k) (hbc : b ≠ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ball a x hx,
      ‖unit a x hx j k b c z‖ ≤ C ∧ ‖(unit a x hx j k b c z)⁻¹‖ ≤ C ∧
        ‖fderiv ℂ (unit a x hx j k b c) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (bounded_closed_neighborhood a x hx).choose_spec.2.2.2 j k b c hjk hbc
  exact ⟨C, hC, fun z hz ↦ hb z (Metric.ball_subset_closedBall hz)⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundedPlanarComplexCharts
