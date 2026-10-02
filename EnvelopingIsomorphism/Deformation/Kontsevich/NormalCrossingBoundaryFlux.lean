import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingMajorant
import Mathlib.Analysis.Normed.Group.Indicator

/-! Actual boundary-flux integrals on an angular interval times the remaining
punctured normal polydisc. The estimate is uniform under arbitrary measurable
additional cutoffs; the geometric coefficient bound remains an explicit input.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossing

open MeasureTheory Set Filter
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι]

def boundaryRegion (ε : ι → ℝ) : Set (ℝ × (ι → ℂ)) :=
  Icc 0 (2 * Real.pi) ×ˢ puncturedPolydisc ε

theorem measurableSet_boundaryRegion (ε : ι → ℝ) : MeasurableSet (boundaryRegion ε) :=
  measurableSet_Icc.prod (measurableSet_puncturedPolydisc ε)

def boundaryMajorant (a : ι → ℕ) (p : ℝ × (ι → ℂ)) : ℝ := majorant a p.2

theorem boundaryMajorant_nonneg (a : ι → ℕ) (p : ℝ × (ι → ℂ)) : 0 ≤ boundaryMajorant a p :=
  majorant_nonneg a p.2

theorem integrableOn_boundaryMajorant (a : ι → ℕ) (ε : ι → ℝ) :
    IntegrableOn (boundaryMajorant a) (boundaryRegion ε) := by
  have hθ : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc 0 (2 * Real.pi)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  change Integrable (fun p : ℝ × (ι → ℂ) ↦ majorant a p.2)
    ((volume : Measure (ℝ × (ι → ℂ))).restrict (Icc 0 (2 * Real.pi) ×ˢ puncturedPolydisc ε))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [one_mul] using hθ.mul_prod (integrableOn_majorant a ε)

theorem integral_boundaryMajorant (a : ι → ℕ) (ε : ι → ℝ) :
    (∫ p in boundaryRegion ε, boundaryMajorant a p) =
      (2 * Real.pi) * ∫ z in puncturedPolydisc ε, majorant a z := by
  change (∫ p in Icc 0 (2 * Real.pi) ×ˢ puncturedPolydisc ε, majorant a p.2) = _
  rw [Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (ι → ℂ))) (fun _ : ℝ ↦ (1 : ℝ)) (majorant a)
    (Icc 0 (2 * Real.pi)) (puncturedPolydisc ε)
  simpa only [one_mul, setIntegral_const, Real.volume_real_Icc, sub_zero, smul_eq_mul, mul_one,
    max_eq_left (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using h

/-- The explicit numerical majorant for one boundary flux. -/
def fluxBound (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C r : ℝ) : ℝ :=
  (2 * Real.pi) * C * r * |Real.log r| ^ q * ∫ z in puncturedPolydisc ε, majorant a z

theorem tendsto_fluxBound (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C : ℝ) :
    Tendsto (fluxBound a ε q C) (𝓝[>] 0) (𝓝 0) := by
  have h := ((LogPole.tendsto_radius_mul_abs_log_pow q).const_mul ((2 * Real.pi) * C)).mul_const
    (∫ z in puncturedPolydisc ε, majorant a z)
  convert h using 1
  · funext r
    unfold fluxBound
    ring
  · simp

section Bochner

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A concrete measured coefficient bound gives both genuine integrability and the actual integral bound. -/
theorem boundaryFlux_spec (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C r : ℝ)
    (F : (ℝ × (ι → ℂ)) → V)
    (hF : AEStronglyMeasurable F ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    IntegrableOn F (boundaryRegion ε) ∧
      ‖∫ p in boundaryRegion ε, F p‖ ≤ fluxBound a ε q C r := by
  have hmajor := (integrableOn_boundaryMajorant a ε).const_mul (C * r * |Real.log r| ^ q)
  refine ⟨hmajor.mono' hF hbound, ?_⟩
  have h := norm_integral_le_of_norm_le hmajor hbound
  rw [integral_const_mul, integral_boundaryMajorant] at h
  exact h.trans_eq (by unfold fluxBound; ring)

/-- Pointwise bounds only need to hold on the actual fixed boundary region. -/
theorem boundaryFlux_spec_on (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C r : ℝ)
    (F : (ℝ × (ι → ℂ)) → V)
    (hF : AEStronglyMeasurable F ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ p ∈ boundaryRegion ε, ‖F p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    IntegrableOn F (boundaryRegion ε) ∧
      ‖∫ p in boundaryRegion ε, F p‖ ≤ fluxBound a ε q C r := by
  apply boundaryFlux_spec a ε q C r F hF
  filter_upwards [ae_restrict_mem (measurableSet_boundaryRegion ε)] with p hp
  exact hbound p hp

/-- Every additional measurable cutoff preserves the same bound, independently of its shape. -/
theorem cutoffFlux_spec (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C r : ℝ)
    (S : Set (ℝ × (ι → ℂ))) (hS : MeasurableSet S) (F : (ℝ × (ι → ℂ)) → V)
    (hF : AEStronglyMeasurable F ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    IntegrableOn (S.indicator F) (boundaryRegion ε) ∧
      ‖∫ p in boundaryRegion ε, S.indicator F p‖ ≤ fluxBound a ε q C r := by
  apply boundaryFlux_spec a ε q C r _ (hF.indicator hS)
  filter_upwards [hbound] with p hp
  exact (norm_indicator_le_norm_self (s := S) (f := F) (a := p)).trans hp

/-- For an actual truncation subset the indicator integral is exactly its set integral. -/
theorem cutoffIntegral_eq_setIntegral (ε : ι → ℝ) (S : Set (ℝ × (ι → ℂ)))
    (hS : MeasurableSet S) (hsub : S ⊆ boundaryRegion ε) (F : (ℝ × (ι → ℂ)) → V) :
    (∫ p in boundaryRegion ε, S.indicator F p) = ∫ p in S, F p := by
  rw [setIntegral_indicator hS, Set.inter_eq_right.mpr hsub]

/-- The same estimate for the actual set integral over a measurable truncation subset. -/
theorem cutoffSetFlux_spec (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C r : ℝ)
    (S : Set (ℝ × (ι → ℂ))) (hS : MeasurableSet S) (hsub : S ⊆ boundaryRegion ε)
    (F : (ℝ × (ι → ℂ)) → V)
    (hF : AEStronglyMeasurable F ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    IntegrableOn F S ∧ ‖∫ p in S, F p‖ ≤ fluxBound a ε q C r := by
  refine ⟨(boundaryFlux_spec a ε q C r F hF hbound).1.mono_set hsub, ?_⟩
  have h := (cutoffFlux_spec a ε q C r S hS F hF hbound).2
  rwa [cutoffIntegral_eq_setIntegral ε S hS hsub F] at h

/-- Actual boundary integrals tend to zero from the positive-radius side. -/
theorem tendsto_boundaryFlux (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C : ℝ)
    (F : ℝ → (ℝ × (ι → ℂ)) → V)
    (hF : ∀ r > 0, AEStronglyMeasurable (F r)
      ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ r > 0, ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F r p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    Tendsto (fun r ↦ ∫ p in boundaryRegion ε, F r p) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_fluxBound a ε q C)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (boundaryFlux_spec a ε q C r (F r) (hF r hr) (hbound r hr)).2

/-- The vanishing limit is uniform with respect to every measurable family of remaining cutoffs.
No regularity, nesting, or limit of the cutoff sets is assumed. -/
theorem tendsto_cutoffFlux (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C : ℝ)
    (S : ℝ → Set (ℝ × (ι → ℂ))) (hS : ∀ r > 0, MeasurableSet (S r))
    (F : ℝ → (ℝ × (ι → ℂ)) → V)
    (hF : ∀ r > 0, AEStronglyMeasurable (F r)
      ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ r > 0, ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F r p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    Tendsto (fun r ↦ ∫ p in boundaryRegion ε, (S r).indicator (F r) p) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_fluxBound a ε q C)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (cutoffFlux_spec a ε q C r (S r) (hS r hr) (F r) (hF r hr) (hbound r hr)).2

/-- Actual integrals over arbitrary radius-dependent measurable truncation subsets vanish. -/
theorem tendsto_setIntegral_cutoffs (a : ι → ℕ) (ε : ι → ℝ) (q : ℕ) (C : ℝ)
    (S : ℝ → Set (ℝ × (ι → ℂ))) (hS : ∀ r > 0, MeasurableSet (S r))
    (hsub : ∀ r > 0, S r ⊆ boundaryRegion ε)
    (F : ℝ → (ℝ × (ι → ℂ)) → V)
    (hF : ∀ r > 0, AEStronglyMeasurable (F r)
      ((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)))
    (hbound : ∀ r > 0, ∀ᵐ p ∂((volume : Measure (ℝ × (ι → ℂ))).restrict (boundaryRegion ε)),
      ‖F r p‖ ≤ C * r * |Real.log r| ^ q * boundaryMajorant a p) :
    Tendsto (fun r ↦ ∫ p in S r, F r p) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_fluxBound a ε q C)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (cutoffSetFlux_spec a ε q C r (S r) (hS r hr) (hsub r hr)
    (F r) (hF r hr) (hbound r hr)).2

end Bochner

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossing
