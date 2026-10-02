import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.SignedFormChangeVariables
import Mathlib.Analysis.Convex.Topology

/-! Actual forest charts shrunk around their corner centers. Their positive
sources are convex, so the Jacobian has a single derived sign on each piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOrientation

open Set MeasureTheory ForestOrthantRealization ForestPositiveChartSmooth
open ForestGraphIntegrability OrientedFormChangeVariables
open ForestOrthantLocalization
open scoped Topology Classical ContDiff

variable {n m : ℕ} (i : Fin (n + 1)) (x : Compactification i m)

def center : Ambient i x := includeOrthant i x ((ForestOrthantCharts.chart i x).symm x)

theorem center_mem_source_preimage :
    center i x ∈ (ofAmbient i x) ⁻¹' (ForestOrthantCharts.chart i x).source := by
  change ofAmbient i x (includeOrthant i x ((ForestOrthantCharts.chart i x).symm x)) ∈
    (ForestOrthantCharts.chart i x).source
  rw [ofAmbient_includeOrthant]
  exact (ForestOrthantCharts.chart i x).map_target (ForestOrthantCharts.mem_chart_target i x)

/-- A ball in the actual ambient free coordinates lies in the original
corner chart domain after retraction to the orthant. -/
theorem exists_radius : ∃ r : ℝ, 0 < r ∧ Metric.ball (center i x) r ⊆
    (ofAmbient i x) ⁻¹' (ForestOrthantCharts.chart i x).source := by
  exact Metric.isOpen_iff.mp
    ((ForestOrthantCharts.chart i x).open_source.preimage (continuous_ofAmbient i x))
    _ (center_mem_source_preimage i x)

def radius : ℝ := (exists_radius i x).choose

theorem radius_pos : 0 < radius i x := (exists_radius i x).choose_spec.1

theorem ball_subset : Metric.ball (center i x) (radius i x) ⊆
    (ofAmbient i x) ⁻¹' (ForestOrthantCharts.chart i x).source :=
  (exists_radius i x).choose_spec.2

def cornerBall : Set (ForestOrthantCharts.Model i x) :=
  (includeOrthant i x) ⁻¹' Metric.ball (center i x) (radius i x)

theorem isOpen_cornerBall : IsOpen (cornerBall i x) :=
  Metric.isOpen_ball.preimage (continuous_includeOrthant i x)

def smallChart : OpenPartialHomeomorph (ForestOrthantCharts.Model i x) (Compactification i m) :=
  (ForestOrthantCharts.chart i x).restrOpen (cornerBall i x) (isOpen_cornerBall i x)

theorem smallChart_source : (smallChart i x).source = cornerBall i x := by
  change (ForestOrthantCharts.chart i x).source ∩ cornerBall i x = cornerBall i x
  apply inter_eq_right.mpr
  intro z hz
  have h := ball_subset i x hz
  simpa only [mem_preimage, ofAmbient_includeOrthant] using h

theorem mem_smallChart_target : x ∈ (smallChart i x).target := by
  refine ⟨ForestOrthantCharts.mem_chart_target i x, ?_⟩
  exact Metric.mem_ball_self (radius_pos i x)

theorem smallChart_target_subset : (smallChart i x).target ⊆ (ForestOrthantCharts.chart i x).target :=
  inter_subset_left

def positiveBall : Set (Ambient i x) :=
  Metric.ball (center i x) (radius i x) ∩ {z | ∀ j, 0 < z.1 j}

theorem positiveBall_subset_Source : positiveBall i x ⊆ Source i x :=
  fun _ hz => ⟨hz.2, ball_subset i x hz.1⟩

theorem convex_positiveBall : Convex ℝ (positiveBall i x) := by
  apply (convex_ball (center i x) (radius i x)).inter
  intro z hz w hw a b ha hb hab j
  exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hz j) (hw j) ha hb hab

theorem positiveBall_nonempty : (positiveBall i x).Nonempty := by
  let z : Ambient i x :=
    (fun j => (center i x).1 j + radius i x / 2, (center i x).2)
  have hr : 0 < radius i x / 2 := half_pos (radius_pos i x)
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    apply lt_of_le_of_lt (b := radius i x / 2) _ (half_lt_self (radius_pos i x))
    rw [Prod.norm_def, max_le_iff]
    constructor
    · apply (pi_norm_le_iff_of_nonneg hr.le).mpr
      intro j
      simp only [z, Prod.fst_sub, Pi.sub_apply, add_sub_cancel_left, Real.norm_eq_abs,
        abs_of_pos hr, le_refl]
    · simpa only [z, Prod.snd_sub, sub_self, norm_zero] using hr.le
  · intro j
    have hc : 0 ≤ (center i x).1 j := ((ForestOrthantCharts.chart i x).symm x).1 j |>.coe_nonneg
    exact add_pos_of_nonneg_of_pos hc hr

theorem isConnected_positiveBall : IsConnected (positiveBall i x) :=
  ⟨positiveBall_nonempty i x, (convex_positiveBall i x).isPreconnected⟩

def realPositiveBall : Set (RealCoordinates n m) :=
  (sourceCoordinates i x).symm ⁻¹' positiveBall i x

theorem realPositiveBall_subset : realPositiveBall i x ⊆ (coordinateChart i x).source := by
  intro z hz
  rw [coordinateChart_source]
  exact positiveBall_subset_Source i x hz

theorem convex_realPositiveBall : Convex ℝ (realPositiveBall i x) :=
  (convex_positiveBall i x).linear_preimage (sourceCoordinates i x).symm.toLinearMap

theorem isOpen_positiveBall : IsOpen (positiveBall i x) := by
  apply Metric.isOpen_ball.inter
  simp only [setOf_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const
    ((continuous_apply j).comp continuous_fst))

theorem isOpen_realPositiveBall : IsOpen (realPositiveBall i x) :=
  (isOpen_positiveBall i x).preimage (sourceCoordinates i x).symm.continuous

theorem contDiffOn_coordinateChart : ContDiffOn ℝ 1 (coordinateChart i x) (coordinateChart i x).source :=
  fun z hz => (contDiffAt_coordinateChart i x z hz).contDiffWithinAt

theorem contDiffAt_coordinateChart_symm (y : RealCoordinates n m)
    (hy : y ∈ (coordinateChart i x).target) :
    ContDiffAt ℝ 1 (coordinateChart i x).symm y := by
  have ht : nativeCoordinates.symm y ∈ Target i x := by
    simpa only [coordinateChart_target, mem_preimage] using hy
  exact (sourceCoordinates i x).contDiff.contDiffAt.comp y
    ((contDiffAt_inverseCoordinates_target i x _ ht).comp y
      nativeCoordinates.symm.contDiff.contDiffAt)

theorem contDiffOn_coordinateChart_symm :
    ContDiffOn ℝ 1 (coordinateChart i x).symm (coordinateChart i x).target :=
  fun y hy => (contDiffAt_coordinateChart_symm i x y hy).contDiffWithinAt

def smallTarget : Set (RealCoordinates n m) := nativeCoordinates.symm ⁻¹'
  (Subtype.val '' {q : GraphForms.CoordinateDomain n m |
    originalEmbedding i q ∈ (smallChart i x).target})

theorem inverse_mem_positiveBall (q : GraphForms.CoordinateDomain n m)
    (hq : originalEmbedding i q ∈ (smallChart i x).target) :
    inverseCoordinates i x q.val ∈ positiveBall i x := by
  refine ⟨?_, inverseCoordinates_radius_pos i x q hq.1⟩
  rw [inverseCoordinates_eq_chart_symm i x q hq.1]
  exact hq.2

theorem originalEmbedding_forward_mem_smallTarget (z : Ambient i x)
    (hz : z ∈ positiveBall i x) :
    originalEmbedding i ⟨forwardCoordinates i x z,
      forwardCoordinates_admissible i x z (positiveBall_subset_Source i x hz)⟩ ∈
        (smallChart i x).target := by
  have hs := positiveBall_subset_Source i x hz
  rw [originalEmbedding_forwardCoordinates i x z hs]
  apply (smallChart i x).map_source
  rw [smallChart_source]
  change includeOrthant i x (ofAmbient i x z) ∈ Metric.ball (center i x) (radius i x)
  rw [includeOrthant_ofAmbient i x z (fun j => (hz.2 j).le)]
  exact hz.1

/-- The signed integration region is precisely the original configurations
lying in the smaller corner chart; it is not an abstract replacement domain. -/
theorem coordinateChart_image_realPositiveBall :
    coordinateChart i x '' realPositiveBall i x = smallTarget i x := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [smallTarget, mem_preimage, coordinateChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨⟨_, forwardCoordinates_admissible i x _ (positiveBall_subset_Source i x hz)⟩,
      originalEmbedding_forward_mem_smallTarget i x _ hz, rfl⟩
  · rintro y ⟨q, hq, heq⟩
    let z := sourceCoordinates i x (inverseCoordinates i x q.val)
    have hz : z ∈ realPositiveBall i x := by
      change (sourceCoordinates i x).symm (sourceCoordinates i x _) ∈ positiveBall i x
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact inverse_mem_positiveBall i x q hq
    refine ⟨z, hz, ?_⟩
    rw [coordinateChart_apply]
    change nativeCoordinates (forwardCoordinates i x
      ((sourceCoordinates i x).symm (sourceCoordinates i x (inverseCoordinates i x q.val)))) = y
    rw [ContinuousLinearEquiv.symm_apply_apply, forward_inverseCoordinates i x q hq.1, heq,
      ContinuousLinearEquiv.apply_symm_apply]

theorem isOpen_smallTarget : IsOpen (smallTarget i x) := by
  exact (((GraphForms.isOpen_admissibleSet n m).isOpenMap_subtype_val _
    ((smallChart i x).open_target.preimage (continuous_originalEmbedding i))).preimage
      nativeCoordinates.symm.continuous)

theorem smallTarget_subset : smallTarget i x ⊆ GeometricWeights.realDomain n m := by
  rintro y ⟨q, _, heq⟩
  change GraphForms.Admissible (nativeCoordinates.symm y)
  rw [← heq]
  exact q.property

/-- Support subordination is checked on the actual compactification point. -/
theorem originalCutoff_zero_off_smallTarget
    (ρ : (Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ) → ℝ)
    (hsub : tsupport (CompactDRAmbientPartition.cutoff i ρ) ⊆ (smallChart i x).target)
    (y : RealCoordinates n m) (hy : y ∈ GeometricWeights.realDomain n m)
    (hnot : y ∉ smallTarget i x) : originalCutoff i ρ y = 0 := by
  by_contra hzero
  let q : GraphForms.CoordinateDomain n m := ⟨nativeCoordinates.symm y, hy⟩
  have hg : CompactDRAmbientPartition.cutoff i ρ (originalEmbedding i q) ≠ 0 := by
    change ρ (CompactDRCoordinates.embedding i (originalEmbedding i q)) ≠ 0
    rw [← originalDR_eq_embedding i q]
    exact hzero
  exact hnot ⟨q, hsub (subset_tsupport _ hg), rfl⟩

/-- Each actual shrunken forest chart has its own orientation sign, obtained
from convexity of its positive source and the actual smooth inverse. -/
theorem exists_orientation : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    (∀ z ∈ realPositiveBall i x, ε * jacobian (coordinateChart i x) z =
      |jacobian (coordinateChart i x) z|) ∧
    ∀ η : TopForm (GraphForms.dimension n m),
      ε * (∫ z in realPositiveBall i x, density (pullback (coordinateChart i x) η) z) =
        ∫ y in coordinateChart i x '' realPositiveBall i x, density η y :=
  SignedFormChangeVariables.exists_signed_integral_identity (coordinateChart i x)
    (contDiffOn_coordinateChart i x) (contDiffOn_coordinateChart_symm i x)
    (realPositiveBall i x) (isOpen_realPositiveBall i x).measurableSet
    (realPositiveBall_subset i x) (convex_realPositiveBall i x).isPreconnected

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOrientation
