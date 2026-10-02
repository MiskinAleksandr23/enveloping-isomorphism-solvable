import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFiberAngleSplit
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
open InteriorFiberAngleSplit Set Filter
open scoped Topology BigOperators ContDiff

abbrev Triple (N : ℕ) := {t : Point N × Point N × Point N // t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2}

def gamma {N : ℕ} (t : Triple N) (η : Shape N) : ℝ :=
  ‖shapeDifference t.val.1 t.val.2.1 η‖ /
    (‖shapeDifference t.val.1 t.val.2.1 η‖ + ‖shapeDifference t.val.1 t.val.2.2 η‖)

def psi (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

theorem psi_nonneg (s : ℝ) : 0 ≤ psi s := Real.smoothTransition.nonneg _
theorem psi_le_one (s : ℝ) : psi s ≤ 1 := Real.smoothTransition.le_one _
theorem psi_zero {s : ℝ} (hs : s ≤ 1) : psi s = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hs)
theorem psi_one {s : ℝ} (hs : 2 ≤ s) : psi s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem contDiff_psi : ContDiff ℝ ∞ psi :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

def chi {N : ℕ} (ε : ℝ) (η : Shape N) : ℝ := ∏ t : Triple N, psi (gamma t η / ε)

theorem chi_nonneg {N : ℕ} (ε : ℝ) (η : Shape N) : 0 ≤ chi ε η :=
  Finset.prod_nonneg (fun _ _ ↦ psi_nonneg _)
theorem chi_le_one {N : ℕ} (ε : ℝ) (η : Shape N) : chi ε η ≤ 1 :=
  Finset.prod_le_one (fun _ _ ↦ psi_nonneg _) (fun _ _ ↦ psi_le_one _)

theorem gamma_pos {N : ℕ} (t : Triple N) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) : 0 < gamma t η := by
  exact div_pos (norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.1))
    (add_pos (norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.1))
      (norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.2)))

theorem gamma_lt_one {N : ℕ} (t : Triple N) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) : gamma t η < 1 := by
  have hb := norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.1)
  have hc := norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.2)
  exact (div_lt_one (add_pos hb hc)).mpr (by linarith)

theorem contDiffAt_gamma {N : ℕ} (t : Triple N) {η : Shape N}
    (hη : η ∈ shapeConfiguration N) : ContDiffAt ℝ ⊤ (gamma t) η := by
  have hb := (contDiff_normalizedPoint t.val.2.1).sub (contDiff_normalizedPoint t.val.1)
  have hc := (contDiff_normalizedPoint t.val.2.2).sub (contDiff_normalizedPoint t.val.1)
  exact (hb.contDiffAt.norm ℝ (shapeDifference_ne_zero hη t.property.1)).div
    ((hb.contDiffAt.norm ℝ (shapeDifference_ne_zero hη t.property.1)).add
      (hc.contDiffAt.norm ℝ (shapeDifference_ne_zero hη t.property.2)))
    (ne_of_gt (add_pos (norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.1))
      (norm_pos_iff.mpr (shapeDifference_ne_zero hη t.property.2))))

theorem chi_eq_zero_of_gamma_le {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (t : Triple N) (ht : gamma t η ≤ ε) : chi ε η = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  exact psi_zero ((div_le_one hε).mpr ht)

theorem gamma_gt_of_chi_ne_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : chi ε η ≠ 0) (t : Triple N) : ε < gamma t η := by
  exact lt_of_not_ge (fun ht ↦ hη (chi_eq_zero_of_gamma_le hε t ht))


theorem continuousAt_gamma_of_denominator_ne_zero {N : ℕ} (t : Triple N) (η : Shape N)
    (h : ‖shapeDifference t.val.1 t.val.2.1 η‖ +
      ‖shapeDifference t.val.1 t.val.2.2 η‖ ≠ 0) : ContinuousAt (gamma t) η := by
  have hb := ((contDiff_normalizedPoint t.val.2.1).continuous.sub
    (contDiff_normalizedPoint t.val.1).continuous).norm.continuousAt (x := η)
  have hc := ((contDiff_normalizedPoint t.val.2.2).continuous.sub
    (contDiff_normalizedPoint t.val.1).continuous).norm.continuousAt (x := η)
  exact hb.div (hb.add hc) h

theorem exists_reference_ne {N : ℕ} (η : Shape N) (a : Point N) :
    ∃ c : Point N, a ≠ c ∧ shapeDifference a c η ≠ 0 := by
  by_cases ha : normalizedPoint η a = 0
  · refine ⟨1, ?_, ?_⟩
    · intro h
      subst a
      simp at ha
    · simp [shapeDifference, ha]
  · refine ⟨0, ?_, ?_⟩
    · intro h
      subst a
      exact ha (normalizedPoint_anchor η)
    · simpa [shapeDifference] using ha

theorem chi_eventually_zero_of_not_configuration {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : η ∉ shapeConfiguration N) :
    chi ε =ᶠ[𝓝 η] 0 := by
  change ¬ Function.Injective (normalizedPoint η) at hη
  simp only [Function.Injective, not_forall] at hη
  obtain ⟨a, b, hab⟩ := hη
  push Not at hab
  obtain ⟨c, hac, hc⟩ := exists_reference_ne η a
  let t : Triple N := ⟨(a, b, c), hab.2, hac⟩
  have hb : shapeDifference a b η = 0 := sub_eq_zero.mpr hab.1.symm
  have hd : ‖shapeDifference t.val.1 t.val.2.1 η‖ +
      ‖shapeDifference t.val.1 t.val.2.2 η‖ ≠ 0 := by
    simpa [t, hb] using (norm_ne_zero_iff.mpr hc)
  have hg : gamma t η = 0 := by simp [gamma, t, hb]
  have he : ∀ᶠ ζ in 𝓝 η, gamma t ζ < ε :=
    (continuousAt_gamma_of_denominator_ne_zero t η hd).eventually
      (gt_mem_nhds (by simpa [hg] using hε))
  filter_upwards [he] with ζ hζ
  exact chi_eq_zero_of_gamma_le hε t hζ.le

theorem contDiff_chi {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (chi (N := N) ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro η
  by_cases hη : η ∈ shapeConfiguration N
  · apply contDiffAt_prod
    intro t _
    exact contDiff_psi.contDiffAt.comp η
      (((contDiffAt_gamma t hη).of_le (by simp)).div_const ε)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (chi_eventually_zero_of_not_configuration hε hη)


theorem tsupport_chi_subset {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (chi (N := N) ε) ⊆ shapeConfiguration N := by
  intro η hη
  by_contra hn
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (chi_eventually_zero_of_not_configuration hε hn)) hη

theorem gamma_ge_on_tsupport {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : η ∈ tsupport (chi ε)) (t : Triple N) : ε ≤ gamma t η := by
  by_contra h
  have ht : gamma t η < ε := lt_of_not_ge h
  have he : ∀ᶠ ζ in 𝓝 η, gamma t ζ < ε :=
    (contDiffAt_gamma t (tsupport_chi_subset hε hη)).continuousAt.eventually (gt_mem_nhds ht)
  have hz : chi ε =ᶠ[𝓝 η] 0 := by
    filter_upwards [he] with ζ hζ
    exact chi_eq_zero_of_gamma_le hε t hζ.le
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hη

theorem coordinate_bound_of_chi_ne_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {η : Shape N} (hη : chi ε η ≠ 0) (j : Fin N) : ‖η j‖ ≤ ε⁻¹ := by
  let t : Triple N := ⟨(0, 1, j.succ.succ), by simp, by intro h; have hv := congrArg Fin.val h; simp at hv⟩
  have hg := gamma_gt_of_chi_ne_zero hε hη t
  have hform : gamma t η = 1 / (1 + ‖η j‖) := by
    simp [gamma, t, shapeDifference]
  rw [hform] at hg
  have hm := (lt_div_iff₀ (show (0 : ℝ) < 1 + ‖η j‖ by positivity)).mp hg
  rw [← one_div]
  apply (le_div_iff₀ hε).mpr
  nlinarith

theorem tsupport_chi_subset_closedBall {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (chi (N := N) ε) ⊆ Metric.closedBall 0 ε⁻¹ := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro η hη
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hε.le)).mpr
  exact coordinate_bound_of_chi_ne_zero hε hη

theorem hasCompactSupport_chi {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (chi (N := N) ε) :=
  (isCompact_closedBall (0 : Shape N) ε⁻¹).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_chi_subset_closedBall hε)

theorem chi_eventually_one {N : ℕ} {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    (fun ε : ℝ ↦ chi ε η) =ᶠ[𝓝[>] 0] (fun _ ↦ 1) := by
  have ht : ∀ t : Triple N, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      psi (gamma t η / ε) = 1 := by
    intro t
    have hg := gamma_pos t hη
    have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < gamma t η / 2 :=
      (gt_mem_nhds (by linarith : (0 : ℝ) < gamma t η / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε he hε
    apply psi_one
    apply (le_div_iff₀ hε).mpr
    linarith
  filter_upwards [eventually_all.mpr ht] with ε hε
  exact Finset.prod_eq_one (fun t _ ↦ hε t)

/-- At each configuration the cutoff is eventually identically one on a neighborhood. -/
theorem chi_eventually_locally_one {N : ℕ} {η : Shape N}
    (hη : η ∈ shapeConfiguration N) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, chi ε =ᶠ[𝓝 η] (fun _ ↦ 1) := by
  have ht : ∀ t : Triple N, ∀ᶠ ε : ℝ in 𝓝[>] 0, 2 * ε < gamma t η := by
    intro t
    have hg := gamma_pos t hη
    have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < gamma t η / 2 :=
      (gt_mem_nhds (by linarith : (0 : ℝ) < gamma t η / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he] with ε hε
    linarith
  filter_upwards [eventually_all.mpr ht, self_mem_nhdsWithin] with ε hsmall hε
  have hl : ∀ t : Triple N, ∀ᶠ ζ in 𝓝 η, 2 * ε < gamma t ζ := fun t ↦
    (contDiffAt_gamma t hη).continuousAt.eventually (lt_mem_nhds (hsmall t))
  filter_upwards [eventually_all.mpr hl] with ζ hζ
  apply Finset.prod_eq_one
  intro t _
  exact psi_one ((le_div_iff₀ hε).mpr (hζ t).le)

theorem fderiv_chi_eventually_zero {N : ℕ} {η : Shape N}
    (hη : η ∈ shapeConfiguration N) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, fderiv ℝ (chi ε) η = 0 := by
  filter_upwards [chi_eventually_locally_one hη] with ε hε
  rw [hε.fderiv_eq]
  exact fderiv_const_apply 1

theorem tendsto_chi {N : ℕ} {η : Shape N} (hη : η ∈ shapeConfiguration N) :
    Tendsto (fun ε : ℝ ↦ chi ε η) (𝓝[>] 0) (𝓝 1) :=
  tendsto_const_nhds.congr' (chi_eventually_one hη).symm

/-- The explicit finite ratio product gives a genuine smooth compact exhaustion. -/
theorem cutoff_properties {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (chi (N := N) ε) ∧ HasCompactSupport (chi (N := N) ε) ∧
      tsupport (chi (N := N) ε) ⊆ shapeConfiguration N ∧
      (∀ η : Shape N, 0 ≤ chi ε η ∧ chi ε η ≤ 1) :=
  ⟨contDiff_chi hε, hasCompactSupport_chi hε, tsupport_chi_subset hε,
    fun η ↦ ⟨chi_nonneg ε η, chi_le_one ε η⟩⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.RatioCutoff
