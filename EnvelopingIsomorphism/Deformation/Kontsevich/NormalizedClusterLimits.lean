import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Sequences

/-! Actual normalized subsequence limits for finite complex configurations.
The normalization uses complex translation and a positive real radius. This is
an interior-cluster recursion ingredient; no real-axis or reflection claim is made. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedClusterLimits

open Filter Topology
open scoped Classical

variable {I : Type*} [Fintype I]

/-- Center a finite configuration at the selected label. -/
def centered (a : I) (p : I → ℂ) : I → ℂ := fun i ↦ p i - p a

/-- The genuine finite Pi supremum radius about the selected label. -/
def radius (a : I) (p : I → ℂ) : ℝ := ‖centered a p‖

/-- Normalize by positive real dilation; the zero-radius convention is never
used for the injective nontrivial configurations in the extraction theorem. -/
def normalized (a : I) (p : I → ℂ) : I → ℂ := (radius a p)⁻¹ • centered a p

@[simp] theorem normalized_anchor (a : I) (p : I → ℂ) : normalized a p a = 0 := by
  simp [normalized, centered]

theorem radius_nonneg (a : I) (p : I → ℂ) : 0 ≤ radius a p := norm_nonneg _

theorem radius_pos_of_injective [Nontrivial I] (a : I) (p : I → ℂ)
    (hp : Function.Injective p) : 0 < radius a p := by
  apply norm_pos_iff.mpr
  intro h
  obtain ⟨b, hb⟩ := exists_ne a
  have he : p b - p a = 0 := congrFun h b
  exact hb (hp (sub_eq_zero.mp he))

theorem norm_normalized (a : I) (p : I → ℂ) (hp : 0 < radius a p) :
    ‖normalized a p‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hp))]
  exact inv_mul_cancel₀ (ne_of_gt hp)

/-- Exact normalized pair differences; the center disappears. -/
theorem normalized_sub (a i j : I) (p : I → ℂ) :
    normalized a p i - normalized a p j = (radius a p)⁻¹ • (p i - p j) := by
  simp only [normalized, centered, Pi.smul_apply, ← smul_sub]
  congr 1
  abel

/-- Pair distances are divided by precisely the actual parent radius. -/
theorem dist_normalized (a i j : I) (p : I → ℂ) :
    dist (normalized a p i) (normalized a p j) = dist (p i) (p j) / radius a p := by
  rw [dist_eq_norm, normalized_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg a p)), dist_eq_norm]
  exact (div_eq_inv_mul _ _).symm

/-- Every injective nontrivial configuration gives a point on the actual compact unit sphere. -/
theorem normalized_mem_sphere [Nontrivial I] (a : I) (p : I → ℂ)
    (hp : Function.Injective p) : normalized a p ∈ Metric.sphere (0 : I → ℂ) 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using
    norm_normalized a p (radius_pos_of_injective a p hp)

/-- Compactness constructs a convergent subsequence; no normalized limit is assumed. -/
theorem exists_normalized_subsequence [Nontrivial I]
    (a : I) (p : ℕ → I → ℂ) (hp : ∀ n, Function.Injective (p n)) :
    ∃ (q : I → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q) ∧ q a = 0 ∧ ‖q‖ = 1 := by
  obtain ⟨q, hq, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : I → ℂ) 1).tendsto_subseq
      (fun n ↦ normalized_mem_sphere a (p n) (hp n))
  refine ⟨q, φ, hφ, hlim, ?_, ?_⟩
  · have ha := (continuous_apply a).tendsto q |>.comp hlim
    have hz : Tendsto (fun n ↦ normalized a (p (φ n)) a) atTop (𝓝 (0 : ℂ)) := by
      simpa only [normalized_anchor] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique ha hz
  · simpa only [Metric.mem_sphere, dist_zero_right] using hq

/-- A unit-norm configuration with an anchored zero cannot be constant. -/
theorem nonconstant_of_normalized (a : I) (q : I → ℂ) (ha : q a = 0) (hq : ‖q‖ = 1) :
    ∃ i j, q i ≠ q j := by
  by_contra h
  have hc : ∀ i j, q i = q j := by simpa using h
  have hz : q = 0 := funext fun i ↦ (hc i a).trans ha
  rw [hz, norm_zero] at hq
  exact zero_ne_one hq

/-- The genuine child supremum radius on the selected finite labels. -/
def childRadius (S : Finset I) (b : I) (p : I → ℂ) : ℝ := ‖fun i : S ↦ p i - p b‖

omit [Fintype I] in
/-- The child radius is the same radius construction on the actual subtype of labels. -/
theorem radius_restrict (S : Finset I) (b : S) (p : I → ℂ) :
    radius b (fun i : S ↦ p i) = childRadius S b p := rfl

omit [Fintype I] in
/-- Restricting the sequence to a child preserves its actual pointwise injectivity. -/
theorem injective_restrict (S : Finset I) (p : I → ℂ) (hp : Function.Injective p) :
    Function.Injective (fun i : S ↦ p i) := hp.comp Subtype.val_injective

omit [Fintype I] in
theorem childRadius_pos_of_injective (S : Finset I) (b : I) (p : I → ℂ)
    (hp : Function.Injective p) (hS : 1 < S.card) : 0 < childRadius S b p := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hS
  have hi' : p i - p b = 0 := congrFun hz ⟨i, hi⟩
  have hj' : p j - p b = 0 := congrFun hz ⟨j, hj⟩
  exact hij (hp ((sub_eq_zero.mp hi').trans (sub_eq_zero.mp hj').symm))

/-- The actual normalized child vectors are scaled original child vectors;
the parent's centering cancels exactly. -/
theorem centered_child_normalized (S : Finset I) (a b : I) (p : I → ℂ) :
    (fun i : S ↦ normalized a p i - normalized a p b) =
      (radius a p)⁻¹ • (fun i : S ↦ p i - p b) := by
  funext i
  simp only [normalized, centered, Pi.smul_apply, ← smul_sub]
  congr 1
  abel

/-- Exact radius ratio, before passage to any limit. -/
theorem childRadius_div_radius (S : Finset I) (a b : I) (p : I → ℂ) :
    childRadius S b p / radius a p =
      ‖fun i : S ↦ normalized a p i - normalized a p b‖ := by
  rw [centered_child_normalized, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg a p))]
  exact div_eq_inv_mul _ _

/-- Constant normalized limits on a finite child set force its actual radius
ratio to zero along exactly the same subsequence. -/
theorem child_ratio_tendsto_zero
    (S : Finset I) (a b : I) (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : I → ℂ)
    (hlim : Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q))
    (hS : ∀ i ∈ S, q i = q b) :
    Tendsto (fun n ↦ childRadius S b (p (φ n)) / radius a (p (φ n))) atTop (𝓝 0) := by
  have hcont : Continuous (fun x : I → ℂ ↦ (fun i : S ↦ x i - x b)) :=
    continuous_pi fun i ↦ (continuous_apply i.val).sub (continuous_apply b)
  have ht := (hcont.tendsto q).comp hlim |>.norm
  have hz : (fun i : S ↦ q i - q b) = 0 := funext fun i ↦ sub_eq_zero.mpr (hS i i.property)
  simp only [hz, norm_zero] at ht
  simpa only [childRadius_div_radius, Function.comp_def] using ht

/-- The actual equivalence-class fiber of the normalized limiting positions. -/
def fiber (q : I → ℂ) (b : I) : Finset I := Finset.univ.filter (fun i ↦ q i = q b)

@[simp] theorem mem_fiber (q : I → ℂ) (b i : I) : i ∈ fiber q b ↔ q i = q b := by
  simp [fiber]

@[simp] theorem anchor_mem_fiber (q : I → ℂ) (b : I) : b ∈ fiber q b := by simp

/-- Every fiber of a nonconstant limit is strictly smaller than the parent label set. -/
theorem fiber_card_lt (q : I → ℂ) (h : ∃ i j, q i ≠ q j) (b : I) :
    (fiber q b).card < Fintype.card I := by
  have hne : fiber q b ≠ Finset.univ := by
    intro he
    obtain ⟨i, j, hij⟩ := h
    have hi : i ∈ fiber q b := he ▸ Finset.mem_univ i
    have hj : j ∈ fiber q b := he ▸ Finset.mem_univ j
    exact hij ((mem_fiber q b i).mp hi |>.trans ((mem_fiber q b j).mp hj).symm)
  simpa only [Finset.card_univ] using
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)

/-- The full bounded recursion ingredient: one actual extracted subsequence
works simultaneously for every child fiber, and each child has fewer labels. -/
theorem exists_normalized_cluster_limits [Nontrivial I]
    (a : I) (p : ℕ → I → ℂ) (hp : ∀ n, Function.Injective (p n)) :
    ∃ (q : I → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q) ∧ q a = 0 ∧ ‖q‖ = 1 ∧
      (∃ i j, q i ≠ q j) ∧
      ∀ b : I, (fiber q b).card < Fintype.card I ∧
        Tendsto (fun n ↦ childRadius (fiber q b) b (p (φ n)) / radius a (p (φ n))) atTop (𝓝 0) := by
  obtain ⟨q, φ, hφ, hlim, ha, hq⟩ := exists_normalized_subsequence a p hp
  have hnc := nonconstant_of_normalized a q ha hq
  refine ⟨q, φ, hφ, hlim, ha, hq, hnc, ?_⟩
  intro b
  exact ⟨fiber_card_lt q hnc b,
    child_ratio_tendsto_zero (fiber q b) a b p φ q hlim (fun i hi ↦ (mem_fiber q b i).mp hi)⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedClusterLimits
