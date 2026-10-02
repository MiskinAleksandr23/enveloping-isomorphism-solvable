import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetNormalization

/-! One actual common subsequence supplies nonconstant normalized limits on
every reflected subset, with exact conjugation across all mirror subsets. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetLimits

open Filter Topology ComplexConjugate
open SubsetNormalizedLimits (LargeSubset ShapeFamily isCompact_shapeSpheres)
open ReflectedSubsetNormalization
open scoped Classical

variable {I : Type*} [Fintype I]

def MirrorCompatible (σ : I → I) (hσ : Function.Involutive σ) (q : ShapeFamily I) : Prop :=
  ∀ (A : LargeSubset I) (j : A.val),
    q (reflectLargeSubset σ hσ A) (reflectIndex σ hσ A j) = conj (q A j)

theorem nonconstant_of_mirrorCompatible (σ : I → I) (hσ : Function.Involutive σ) (q : ShapeFamily I)
    (hmir : MirrorCompatible σ hσ q) (A : LargeSubset I)
    (hre : (q A (chosenAnchor σ hσ A)).re = 0)
    (hzero : ¬IsStable σ A → q A (chosenAnchor σ hσ A) = 0) (hnorm : ‖q A‖ = 1) :
    ∃ j k, q A j ≠ q A k := by
  by_cases hA : IsStable σ A
  · by_contra h
    have hc : ∀ j k, q A j = q A k := by simpa using h
    let b := chosenAnchor σ hσ A
    have hRA := reflectLargeSubset_eq_of_stable σ hσ A hA
    have hconst_aux (B : LargeSubset I) (hB : B = A) : ∀ j : B.val, q B j = q A b := by
      subst B
      exact fun j => hc j b
    have hconst := hconst_aux (reflectLargeSubset σ hσ A) hRA
    have he : conj (q A b) = q A b := (hmir A b).symm.trans (hconst (reflectIndex σ hσ A b))
    have hb : q A b = 0 := Complex.ext hre (Complex.conj_eq_iff_im.mp he)
    have hz : q A = 0 := funext fun j => (hc j b).trans hb
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · exact NormalizedClusterLimits.nonconstant_of_normalized (chosenAnchor σ hσ A) (q A) (hzero hA) hnorm

/-- A single finite-product compactness argument constructs all reflected limits
simultaneously. Neither their existence nor their mirror compatibility is an input. -/
theorem exists_common_reflected_limits (σ : I → I) (hσ : Function.Involutive σ)
    (p : ℕ → I → ℂ) (hp : ∀ k, Function.Injective (p k))
    (hmirror : ∀ k j, p k (σ j) = conj (p k j)) :
    ∃ (φ : ℕ → ℕ) (q : ShapeFamily I), StrictMono φ ∧
      (∀ A : LargeSubset I,
        Tendsto (fun k => normalizedOn σ hσ A (p (φ k))) atTop (𝓝 (q A))) ∧
      MirrorCompatible σ hσ q ∧
      (∀ A : LargeSubset I, (q A (chosenAnchor σ hσ A)).re = 0) ∧
      (∀ A : LargeSubset I, ¬IsStable σ A → q A (chosenAnchor σ hσ A) = 0) ∧
      (∀ A : LargeSubset I, ‖q A‖ = 1) ∧
      (∀ A : LargeSubset I, ∃ j k, q A j ≠ q A k) := by
  obtain ⟨q, hq, φ, hφ, hlim⟩ := (isCompact_shapeSpheres (I := I)).tendsto_subseq
    (fun (k : ℕ) (A : LargeSubset I) => normalizedOn_mem_sphere σ hσ A (p k) (hp k))
  have hA (A : LargeSubset I) :
      Tendsto (fun k => normalizedOn σ hσ A (p (φ k))) atTop (𝓝 (q A)) :=
    (continuous_apply A).tendsto q |>.comp hlim
  have hmir : MirrorCompatible σ hσ q := by
    intro A j
    have hl := (continuous_apply (reflectIndex σ hσ A j)).tendsto
      (q (reflectLargeSubset σ hσ A)) |>.comp (hA (reflectLargeSubset σ hσ A))
    have hr := (Complex.continuous_conj.comp (continuous_apply j)).tendsto (q A) |>.comp (hA A)
    apply tendsto_nhds_unique hl
    convert hr using 1
    · funext k
      exact normalizedOn_mirror σ hσ A (p (φ k)) (hmirror (φ k)) j
    · rfl
  have hre (A : LargeSubset I) : (q A (chosenAnchor σ hσ A)).re = 0 := by
    have h := (Complex.continuous_re.comp (continuous_apply (chosenAnchor σ hσ A))).tendsto (q A) |>.comp (hA A)
    have hz : Tendsto (fun k => (normalizedOn σ hσ A (p (φ k)) (chosenAnchor σ hσ A)).re)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [normalizedOn_anchor_re] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique h hz
  have hzero (A : LargeSubset I) (hstable : ¬IsStable σ A) : q A (chosenAnchor σ hσ A) = 0 := by
    have h := (continuous_apply (chosenAnchor σ hσ A)).tendsto (q A) |>.comp (hA A)
    have hz : Tendsto (fun k => normalizedOn σ hσ A (p (φ k)) (chosenAnchor σ hσ A)) atTop (𝓝 (0 : ℂ)) := by
      simpa only [normalizedOn_anchor_eq_zero σ hσ A _ hstable] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique h hz
  have hnorm (A : LargeSubset I) : ‖q A‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hq A
  exact ⟨φ, q, hφ, hA, hmir, hre, hzero, hnorm,
    fun A => nonconstant_of_mirrorCompatible σ hσ q hmir A (hre A) (hzero A) (hnorm A)⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetLimits
