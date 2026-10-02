import EnvelopingIsomorphism.Deformation.Kontsevich.ReferenceNormIdentification
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Recover a complex point, including infinity, from its phase and compact norm
ratio. Continuity at the boundary follows from an explicit bound independent
of the phase, using the actual compact neighborhoods of the one-point space.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Filter OnePoint
open scoped Topology

/-- A positive-reference norm ratio as a genuine closed-interval coordinate. -/
def referenceNormRatioIcc {R : ℝ} (hR : 0 < R) (z : ℂ) : Set.Icc (0 : ℝ) 1 :=
  ⟨referenceNormRatio R z,
    div_nonneg (norm_nonneg z) (by positivity),
    (referenceNormRatio_lt_one hR z).le⟩

@[simp] theorem referenceNormRatioIcc_val {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (referenceNormRatioIcc hR z : ℝ) = referenceNormRatio R z := rfl

/-- At the endpoint every phase gives the point at infinity. -/
def onePointRadialIdentification (R : ℝ) (p : Circle × Set.Icc (0 : ℝ) 1) : OnePoint ℂ :=
  if (p.2 : ℝ) = 1 then ∞ else
    ((R : ℂ) * recoverRelativePosition p.1 p.2 : ℂ)

theorem onePointRadialIdentification_of_lt {R : ℝ} (p : Circle × Set.Icc (0 : ℝ) 1)
    (hp : (p.2 : ℝ) < 1) :
    onePointRadialIdentification R p = ((R : ℂ) * recoverRelativePosition p.1 p.2 : ℂ) := by
  simp [onePointRadialIdentification, ne_of_lt hp]

@[simp] theorem onePointRadialIdentification_one (R : ℝ) (θ : Circle) :
    onePointRadialIdentification R (θ, ⟨1, by simp⟩) = ∞ := by
  simp [onePointRadialIdentification]

/-- The radius is independent of the phase. -/
theorem norm_scaled_recoverRelativePosition {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hr1 : r < 1) (θ : Circle) :
    ‖(R : ℂ) * recoverRelativePosition θ r‖ = R * (r / (1 - r)) := by
  have hquot : 0 ≤ r / (1 - r) := div_nonneg hr (sub_pos.mpr hr1).le
  simp only [recoverRelativePosition, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Circle.norm_coe, mul_one, abs_of_nonneg hR, abs_of_nonneg hquot]

/-- The explicit norm bound tends to infinity uniformly over all phases. -/
theorem norm_identification_gt_of_ratio_gt {R B r : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hr1 : r < 1) (hBr : B / (B + R) < r) (θ : Circle) :
    B < ‖(R : ℂ) * recoverRelativePosition θ r‖ := by
  rw [norm_scaled_recoverRelativePosition hR.le hr hr1, ← mul_div_assoc]
  apply (lt_div_iff₀ (sub_pos.mpr hr1)).mpr
  have hcross := (div_lt_iff₀ (add_pos_of_nonneg_of_pos hB hR)).mp hBr
  nlinarith

theorem continuousAt_onePointRadialIdentification_finite (R : ℝ)
    (p : Circle × Set.Icc (0 : ℝ) 1) (hp : (p.2 : ℝ) ≠ 1) :
    ContinuousAt (onePointRadialIdentification R) p := by
  have hr : Continuous (fun q : Circle × Set.Icc (0 : ℝ) 1 ↦ (q.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hθ : Continuous (fun q : Circle × Set.Icc (0 : ℝ) 1 ↦ (q.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hd : 1 - (p.2 : ℝ) ≠ 0 := sub_ne_zero.mpr hp.symm
  have hfinite : ContinuousAt (fun q : Circle × Set.Icc (0 : ℝ) 1 ↦
      (((R : ℂ) * recoverRelativePosition q.1 q.2 : ℂ) : OnePoint ℂ)) p := by
    apply OnePoint.continuous_coe.continuousAt.comp
    exact continuousAt_const.mul
      ((Complex.continuous_ofReal.continuousAt.comp
        (hr.continuousAt.div (continuous_const.sub hr).continuousAt hd)).mul hθ.continuousAt)
  apply hfinite.congr_of_eventuallyEq
  have hn : ∀ᶠ q in 𝓝 p, (q.2 : ℝ) ≠ 1 :=
    (isOpen_ne_fun hr continuous_const).mem_nhds hp
  exact hn.mono (fun q hq ↦ by simp [onePointRadialIdentification, hq])

/-- Continuity at infinity is proved using a phase-independent compact-avoidance
estimate, so it holds even when the direction varies arbitrarily. -/
theorem continuousAt_onePointRadialIdentification_infty {R : ℝ} (hR : 0 < R)
    (p : Circle × Set.Icc (0 : ℝ) 1) (hp : (p.2 : ℝ) = 1) :
    ContinuousAt (onePointRadialIdentification R) p := by
  have hv : onePointRadialIdentification R p = ∞ := by simp [onePointRadialIdentification, hp]
  change Tendsto (onePointRadialIdentification R) (𝓝 p) (𝓝 (onePointRadialIdentification R p))
  rw [hv]
  apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
  rintro K ⟨_hclosed, hcompact⟩
  obtain ⟨B, hB, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  have hthreshold : B / (B + R) < 1 :=
    (div_lt_one (add_pos hB hR)).mpr (by linarith)
  have hr : Continuous (fun q : Circle × Set.Icc (0 : ℝ) 1 ↦ (q.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hevent : ∀ᶠ q in 𝓝 p, B / (B + R) < (q.2 : ℝ) :=
    hr.continuousAt.eventually (Ioi_mem_nhds (by simpa [hp] using hthreshold))
  filter_upwards [hevent] with q hq
  by_cases hq1 : (q.2 : ℝ) = 1
  · simp [onePointRadialIdentification, hq1]
  · left
    refine ⟨(R : ℂ) * recoverRelativePosition q.1 q.2, ?_, ?_⟩
    · intro hK
      have hn := norm_identification_gt_of_ratio_gt hR hB.le q.2.property.1
        (lt_of_le_of_ne q.2.property.2 hq1) hq q.1
      exact (not_lt_of_ge (hbound _ hK)) hn
    · simp [onePointRadialIdentification, hq1]

theorem continuous_onePointRadialIdentification {R : ℝ} (hR : 0 < R) :
    Continuous (onePointRadialIdentification R) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : (p.2 : ℝ) = 1
  · exact continuousAt_onePointRadialIdentification_infty hR p hp
  · exact continuousAt_onePointRadialIdentification_finite R p hp

/-- Every finite complex point is reconstructed from its actual phase and ratio. -/
theorem onePointRadialIdentification_phase_ratio {R : ℝ} (hR : 0 < R) (z : ℂ) :
    onePointRadialIdentification R (complexPhase z, referenceNormRatioIcc hR z) = (z : OnePoint ℂ) := by
  rw [onePointRadialIdentification_of_lt _ (referenceNormRatio_lt_one hR z)]
  exact congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) (recoverRelativePosition_referenceNormRatio hR z)

/-- Translation of the recovered point, extended by the actual one-point homeomorphism. -/
def onePointRadialIdentificationSub (R : ℝ) (a : ℂ) :
    Circle × Set.Icc (0 : ℝ) 1 → OnePoint ℂ :=
  (Homeomorph.addRight (-a)).onePointCongr ∘ onePointRadialIdentification R

theorem continuous_onePointRadialIdentificationSub {R : ℝ} (hR : 0 < R) (a : ℂ) :
    Continuous (onePointRadialIdentificationSub R a) :=
  (Homeomorph.addRight (-a)).onePointCongr.continuous.comp (continuous_onePointRadialIdentification hR)

theorem onePointRadialIdentificationSub_of_lt (R : ℝ) (a : ℂ)
    (p : Circle × Set.Icc (0 : ℝ) 1) (hp : (p.2 : ℝ) < 1) :
    onePointRadialIdentificationSub R a p =
      (((R : ℂ) * recoverRelativePosition p.1 p.2 - a : ℂ) : OnePoint ℂ) := by
  simp [onePointRadialIdentificationSub, onePointRadialIdentification_of_lt p hp,
    Homeomorph.onePointCongr_apply, sub_eq_add_neg]

@[simp] theorem onePointRadialIdentificationSub_one (R : ℝ) (a : ℂ) (θ : Circle) :
    onePointRadialIdentificationSub R a (θ, ⟨1, by simp⟩) = ∞ := by
  simp [onePointRadialIdentificationSub, onePointRadialIdentification, Homeomorph.onePointCongr_apply]

theorem onePointRadialIdentificationSub_phase_ratio {R : ℝ} (hR : 0 < R) (a z : ℂ) :
    onePointRadialIdentificationSub R a (complexPhase z, referenceNormRatioIcc hR z) =
      ((z - a : ℂ) : OnePoint ℂ) := by
  simp [onePointRadialIdentificationSub, onePointRadialIdentification_phase_ratio hR,
    Homeomorph.onePointCongr_apply, sub_eq_add_neg]

end EnvelopingIsomorphism.Deformation.Kontsevich
