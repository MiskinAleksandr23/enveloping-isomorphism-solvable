import EnvelopingIsomorphism.Deformation.Kontsevich.ForestLeafRadii
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestInsertion

/-! Positive internal radii are dense in the actual reflected radius orthant.
Root and unused leaf radii stay fixed to one during the perturbation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusOrthant

open Set Filter
open scoped Classical Topology

variable (T : RootedTree) [Fintype T] (σ : T ≃o T)

def Admissible (r : T → ℝ) : Prop :=
  r ⊥ = 1 ∧ (∀ u, IsMax u → r u = 1) ∧
    (∀ u, r (σ u) = r u) ∧ ∀ u, 0 ≤ r u

def Positive (r : T → ℝ) : Prop := Admissible T σ r ∧ ∀ u, 0 < r u

def perturb (r : T → ℝ) (ε : ℝ) (u : T) : ℝ :=
  if u = ⊥ ∨ IsMax u then r u else r u + ε

omit [Fintype T] in
@[simp] theorem perturb_zero (r : T → ℝ) : perturb T r 0 = r := by
  funext u
  simp [perturb]

theorem contDiff_perturb (r : T → ℝ) : ContDiff ℝ ⊤ (perturb T r) := by
  apply contDiff_pi.mpr
  intro u
  by_cases hu : u = ⊥ ∨ IsMax u
  · simpa only [perturb, if_pos hu] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => r u))
  · simpa only [perturb, if_neg hu] using
      (contDiff_const.add contDiff_id : ContDiff ℝ ⊤ (fun ε : ℝ => r u + ε))

omit [Fintype T] in
theorem perturb_admissible (r : T → ℝ) (hr : Admissible T σ r)
    {ε : ℝ} (hε : 0 ≤ ε) : Admissible T σ (perturb T r ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [perturb] using hr.1
  · intro u hu
    simpa [perturb, hu] using hr.2.1 u hu
  · intro u
    have hroot : σ u = ⊥ ↔ u = ⊥ := by
      constructor
      · intro h
        apply σ.injective
        simpa only [σ.map_bot] using h
      · rintro rfl
        exact σ.map_bot
    simp only [perturb, hroot, σ.isMax_apply, hr.2.2.1]
  · intro u
    unfold perturb
    split_ifs
    · exact hr.2.2.2 u
    · exact add_nonneg (hr.2.2.2 u) hε

omit [Fintype T] in
theorem perturb_positive (r : T → ℝ) (hr : Admissible T σ r)
    {ε : ℝ} (hε : 0 < ε) : Positive T σ (perturb T r ε) := by
  refine ⟨perturb_admissible T σ r hr hε.le, ?_⟩
  intro u
  by_cases hu : u = ⊥ ∨ IsMax u
  · rw [perturb, if_pos hu]
    rcases hu with rfl | hu
    · rw [hr.1]
      exact zero_lt_one
    · rw [hr.2.1 u hu]
      exact zero_lt_one
  · rw [perturb, if_neg hu]
    exact add_pos_of_nonneg_of_pos (hr.2.2.2 u) hε

/-- Every neighborhood of an admissible corner contains positive reflected
radii, with root and all leaf coordinates unchanged. -/
theorem mem_closure_positive (r : T → ℝ) (hr : Admissible T σ r) :
    r ∈ closure {s | Positive T σ s} := by
  have hlim : Tendsto (perturb T r) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
    simpa only [perturb_zero] using
      ((contDiff_perturb T r).continuous.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact mem_closure_of_tendsto hlim (he.mono fun ε hε => perturb_positive T σ r hr hε)

open ForestMarkedFrames ForestMarkedFrameInverse ComplexConjugate

/-- Stable frame tags are attached to fixed nodes of the reflection. -/
def StableFixed (F : Frames T) : Prop :=
  ∀ v (hv : ¬ IsMax v), match F v hv with
    | .complex _ _ _ _ _ => True
    | .stableHeight _ _ => σ v = v
    | .stableRealPair _ _ _ _ _ => σ v = v

/-- Changing reflected real radii preserves the actual frame equations.
Reality of cumulative stable positions is derived from reflection. -/
theorem normalized_change_radii (F : Frames T) (hF : StableFixed T σ F)
    (r s : T → ℝ) (hs : ∀ u, s (σ u) = s u) (a : T → ℂ)
    (ha : ∀ u, a (σ u) = conj (a u)) (hn : Normalized T F r a) :
    Normalized T F s a := by
  intro v hv
  have hnv := hn v hv
  have hfixed := hF v hv
  cases hf : F v hv with
  | complex b c hb hc hbc =>
    simpa only [hf] using hnv
  | stableHeight b hb =>
    rw [hf] at hnv hfixed
    exact ⟨hnv.1, ReflectedForestInsertion.position_im_eq_zero_of_fixed T σ s hs a ha v hfixed⟩
  | stableRealPair b c hb hc hbc =>
    rw [hf] at hnv hfixed
    exact ⟨hnv.1, hnv.2.1,
      ReflectedForestInsertion.position_im_eq_zero_of_fixed T σ s hs a ha v hfixed⟩

/-- Every open neighborhood of normalized reflected corner parameters contains
genuinely positive normalized parameters with the same child shapes. -/
theorem exists_positive_normalized_in_open (F : Frames T) (hF : StableFixed T σ F)
    (r : T → ℝ) (a : T → ℂ) (hr : Admissible T σ r)
    (ha : ∀ u, a (σ u) = conj (a u)) (hn : Normalized T F r a)
    (U : Set ((T → ℝ) × (T → ℂ))) (hU : IsOpen U) (hx : (r, a) ∈ U) :
    ∃ s, Positive T σ s ∧ Normalized T F s a ∧ (s, a) ∈ U := by
  have hlim : Tendsto (fun ε : ℝ => (perturb T r ε, a)) (𝓝[>] (0 : ℝ)) (𝓝 (r, a)) := by
    have hc := (contDiff_perturb T r).continuous.prodMk (continuous_const (y := a))
    simpa only [perturb_zero] using (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεU⟩ := (he.and (hlim.eventually (hU.mem_nhds hx))).exists
  have hp := perturb_positive T σ r hr hε
  exact ⟨perturb T r ε, hp,
    normalized_change_radii T σ F hF r _ hp.1.2.2.1 a ha hn, hεU⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusOrthant
