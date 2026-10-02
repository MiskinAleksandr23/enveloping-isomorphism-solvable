import EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedClusterLimits

/-! Normalized compact limits respecting an actual label involution and complex
conjugation. The center is real, so the normalization respects the real axis. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterLimits

open Filter Topology ComplexConjugate
open NormalizedClusterLimits (childRadius fiber mem_fiber anchor_mem_fiber fiber_card_lt)
open scoped Classical

variable {I : Type*} [Fintype I]

/-- A real center, rather than translation by a possibly nonreal anchor point. -/
def center (a : I) (p : I → ℂ) : ℝ := (p a).re

def centered (a : I) (p : I → ℂ) : I → ℂ := fun i ↦ p i - (center a p : ℂ)

def radius (a : I) (p : I → ℂ) : ℝ := ‖centered a p‖

def normalized (a : I) (p : I → ℂ) : I → ℂ := (radius a p)⁻¹ • centered a p

theorem radius_nonneg (a : I) (p : I → ℂ) : 0 ≤ radius a p := norm_nonneg _

theorem radius_pos_of_injective [Nontrivial I] (a : I) (p : I → ℂ)
    (hp : Function.Injective p) : 0 < radius a p := by
  apply norm_pos_iff.mpr
  intro h
  obtain ⟨b, hb⟩ := exists_ne a
  have ha : p a - (center a p : ℂ) = 0 := congrFun h a
  have hb' : p b - (center a p : ℂ) = 0 := congrFun h b
  exact hb (hp ((sub_eq_zero.mp hb').trans (sub_eq_zero.mp ha).symm))

theorem norm_normalized (a : I) (p : I → ℂ) (hp : 0 < radius a p) :
    ‖normalized a p‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hp))]
  exact inv_mul_cancel₀ (ne_of_gt hp)

@[simp] theorem normalized_anchor_re (a : I) (p : I → ℂ) : (normalized a p a).re = 0 := by
  simp [normalized, centered, center]

/-- Real centering and real dilation preserve the given reflection relation exactly. -/
theorem normalized_mirror (σ : I → I) (a : I) (p : I → ℂ)
    (hp : ∀ i, p (σ i) = conj (p i)) (i : I) :
    normalized a p (σ i) = conj (normalized a p i) := by
  simp [normalized, centered, Complex.real_smul, hp]

theorem normalized_sub (a i j : I) (p : I → ℂ) :
    normalized a p i - normalized a p j = (radius a p)⁻¹ • (p i - p j) := by
  simp only [normalized, centered, Pi.smul_apply, ← smul_sub]
  congr 1
  abel

theorem dist_normalized (a i j : I) (p : I → ℂ) :
    dist (normalized a p i) (normalized a p j) = dist (p i) (p j) / radius a p := by
  rw [dist_eq_norm, normalized_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg a p)), dist_eq_norm]
  exact (div_eq_inv_mul _ _).symm

/-- Compactness produces the normalized limit, and continuity preserves reflection. -/
theorem exists_reflected_subsequence [Nontrivial I]
    (σ : I → I) (a : I) (p : ℕ → I → ℂ)
    (hp : ∀ n, Function.Injective (p n)) (hmirror : ∀ n i, p n (σ i) = conj (p n i)) :
    ∃ (q : I → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q) ∧
      (∀ i, q (σ i) = conj (q i)) ∧ (q a).re = 0 ∧ ‖q‖ = 1 := by
  have hs (n : ℕ) : normalized a (p n) ∈ Metric.sphere (0 : I → ℂ) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      norm_normalized a (p n) (radius_pos_of_injective a (p n) (hp n))
  obtain ⟨q, hq, φ, hφ, hlim⟩ := (isCompact_sphere (0 : I → ℂ) 1).tendsto_subseq hs
  refine ⟨q, φ, hφ, hlim, ?_, ?_, ?_⟩
  · intro i
    have hl := (continuous_apply (σ i)).tendsto q |>.comp hlim
    have hr := (Complex.continuous_conj.comp (continuous_apply i)).tendsto q |>.comp hlim
    apply tendsto_nhds_unique hl
    convert hr using 1
    funext n
    exact normalized_mirror σ a (p (φ n)) (hmirror (φ n)) i
    rfl
  · have ha := (Complex.continuous_re.comp (continuous_apply a)).tendsto q |>.comp hlim
    have hz : Tendsto (fun n ↦ (normalized a (p (φ n)) a).re) atTop (𝓝 (0 : ℝ)) := by
      simpa only [normalized_anchor_re] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique ha hz
  · simpa only [Metric.mem_sphere, dist_zero_right] using hq

/-- A constant reflected configuration is real; the anchored real part would
then make it zero, contradicting unit norm. -/
theorem nonconstant_of_reflected (σ : I → I) (a : I) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (ha : (q a).re = 0) (hq : ‖q‖ = 1) :
    ∃ i j, q i ≠ q j := by
  by_contra h
  have hc : ∀ i j, q i = q j := by simpa using h
  have hreal : conj (q a) = q a := (hmirror a).symm.trans (hc (σ a) a)
  have hzero : q a = 0 := Complex.ext ha (Complex.conj_eq_iff_im.mp hreal)
  have hz : q = 0 := funext fun i ↦ (hc i a).trans hzero
  rw [hz, norm_zero] at hq
  exact zero_ne_one hq

/-- The actual normalized child radius is its radius divided by the real-centered parent radius. -/
theorem childRadius_div_radius (S : Finset I) (a b : I) (p : I → ℂ) :
    childRadius S b p / radius a p =
      ‖fun i : S ↦ normalized a p i - normalized a p b‖ := by
  have he : (fun i : S ↦ normalized a p i - normalized a p b) =
      (radius a p)⁻¹ • (fun i : S ↦ p i - p b) := by
    funext i
    exact normalized_sub a i b p
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg a p))]
  exact div_eq_inv_mul _ _

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

/-- The radius appropriate for recursively normalizing a reflection-stable child. -/
def realChildRadius (S : Finset I) (b : I) (p : I → ℂ) : ℝ :=
  ‖fun i : S ↦ p i - ((p b).re : ℂ)‖

omit [Fintype I] in
@[simp] theorem radius_restrict (S : Finset I) (b : S) (p : I → ℂ) :
    radius b (fun i : S ↦ p i) = realChildRadius S b p := rfl

/-- Exact real-centered child-radius ratio under the parent's real normalization. -/
theorem realChildRadius_div_radius (S : Finset I) (a b : I) (p : I → ℂ) :
    realChildRadius S b p / radius a p =
      ‖fun i : S ↦ normalized a p i - ((normalized a p b).re : ℂ)‖ := by
  have hr : ((normalized a p b).re : ℂ) =
      (radius a p)⁻¹ • (((p b).re : ℂ) - (center a p : ℂ)) := by
    simp [normalized, centered, Complex.real_smul]
  have he : (fun i : S ↦ normalized a p i - ((normalized a p b).re : ℂ)) =
      (radius a p)⁻¹ • (fun i : S ↦ p i - ((p b).re : ℂ)) := by
    funext i
    rw [hr]
    change (radius a p)⁻¹ • (p i - (center a p : ℂ)) -
      (radius a p)⁻¹ • (((p b).re : ℂ) - (center a p : ℂ)) = _
    rw [← smul_sub]
    congr 1
    abel_nf
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg a p))]
  exact div_eq_inv_mul _ _

/-- Real-valued limit fibers shrink also in their recursive real-centered radius. -/
theorem real_child_ratio_tendsto_zero
    (S : Finset I) (a b : I) (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : I → ℂ)
    (hlim : Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q))
    (hS : ∀ i ∈ S, q i = q b) (hreal : (q b).im = 0) :
    Tendsto (fun n ↦ realChildRadius S b (p (φ n)) / radius a (p (φ n))) atTop (𝓝 0) := by
  have hcont : Continuous (fun x : I → ℂ ↦ (fun i : S ↦ x i - ((x b).re : ℂ))) :=
    continuous_pi fun i ↦ (continuous_apply i.val).sub
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_apply b)))
  have ht := (hcont.tendsto q).comp hlim |>.norm
  have hb : ((q b).re : ℂ) = q b := Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr hreal)
  have hz : (fun i : S ↦ q i - ((q b).re : ℂ)) = 0 := by
    funext i
    rw [hb, hS i i.property, sub_self]
    rfl
  simp only [hz, norm_zero] at ht
  simpa only [realChildRadius_div_radius, Function.comp_def] using ht

/-- Reflection carries a fiber to the fiber at the reflected shape value. -/
theorem mem_fiber_mirror (σ : I → I) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b i : I) :
    σ i ∈ fiber q (σ b) ↔ i ∈ fiber q b := by
  simp only [mem_fiber, hmirror]
  constructor
  · intro h
    simpa using congrArg (fun z : ℂ ↦ conj z) h
  · exact congrArg (fun z : ℂ ↦ conj z)

theorem fiber_image (σ : I → I) (hσ : Function.Involutive σ) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b : I) :
    Finset.image σ (fiber q b) = fiber q (σ b) := by
  ext j
  constructor
  · rintro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_fiber_mirror σ q hmirror b i).mpr hi
  · intro hj
    refine Finset.mem_image.mpr ⟨σ j, ?_, hσ j⟩
    apply (mem_fiber_mirror σ q hmirror b (σ j)).mp
    simpa only [hσ j] using hj

/-- A fiber is stable precisely when its limiting shape value lies on the real axis. -/
theorem fiber_stable_iff_real (σ : I → I) (hσ : Function.Involutive σ) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b : I) :
    Finset.image σ (fiber q b) = fiber q b ↔ (q b).im = 0 := by
  rw [fiber_image σ hσ q hmirror b]
  constructor
  · intro h
    have hb : σ b ∈ fiber q b := h ▸ anchor_mem_fiber q (σ b)
    have he := (mem_fiber q b (σ b)).mp hb
    rw [hmirror b] at he
    exact Complex.conj_eq_iff_im.mp he
  · intro h
    have he : q (σ b) = q b := (hmirror b).trans (Complex.conj_eq_iff_im.mpr h)
    ext i
    simp only [mem_fiber, he]

/-- Restrict the actual reflection to a real-valued limiting fiber. -/
def fiberReflection (σ : I → I) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b : I) (hreal : (q b).im = 0) :
    fiber q b → fiber q b := fun i ↦ ⟨σ i, by
      apply (mem_fiber q b (σ i)).mpr
      rw [hmirror i, (mem_fiber q b i).mp i.property]
      exact Complex.conj_eq_iff_im.mpr hreal⟩

theorem fiberReflection_involutive (σ : I → I) (hσ : Function.Involutive σ) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b : I) (hreal : (q b).im = 0) :
    Function.Involutive (fiberReflection σ q hmirror b hreal) :=
  fun i ↦ Subtype.ext (hσ i)

/-- Original reflected configurations restrict to the constructed child involution. -/
theorem restrict_mirror (σ : I → I) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (b : I) (hreal : (q b).im = 0)
    (p : I → ℂ) (hp : ∀ i, p (σ i) = conj (p i)) (i : fiber q b) :
    p (fiberReflection σ q hmirror b hreal i) = conj (p i) := hp i

omit [Fintype I] in
/-- A reflection-fixed label has real limiting position. -/
theorem real_of_fixed_label (σ : I → I) (q : I → ℂ)
    (hmirror : ∀ i, q (σ i) = conj (q i)) (i : I) (hi : σ i = i) : (q i).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [hi] using (hmirror i).symm

/-- One extracted subsequence works for all reflected fibers and all child-scale ratios. -/
theorem exists_reflected_cluster_limits [Nontrivial I]
    (σ : I → I) (hσ : Function.Involutive σ) (a : I) (p : ℕ → I → ℂ)
    (hp : ∀ n, Function.Injective (p n)) (hmirror : ∀ n i, p n (σ i) = conj (p n i)) :
    ∃ (q : I → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q) ∧
      (∀ i, q (σ i) = conj (q i)) ∧ (q a).re = 0 ∧ ‖q‖ = 1 ∧
      (∃ i j, q i ≠ q j) ∧
      ∀ b : I, (fiber q b).card < Fintype.card I ∧
        Tendsto (fun n ↦ childRadius (fiber q b) b (p (φ n)) / radius a (p (φ n))) atTop (𝓝 0) ∧
        Finset.image σ (fiber q b) = fiber q (σ b) ∧
        (Finset.image σ (fiber q b) = fiber q b ↔ (q b).im = 0) ∧
        ((q b).im = 0 → Tendsto
          (fun n ↦ realChildRadius (fiber q b) b (p (φ n)) / radius a (p (φ n))) atTop (𝓝 0)) := by
  obtain ⟨q, φ, hφ, hlim, hmir, ha, hq⟩ := exists_reflected_subsequence σ a p hp hmirror
  have hnc := nonconstant_of_reflected σ a q hmir ha hq
  refine ⟨q, φ, hφ, hlim, hmir, ha, hq, hnc, ?_⟩
  intro b
  exact ⟨fiber_card_lt q hnc b,
    child_ratio_tendsto_zero (fiber q b) a b p φ q hlim (fun i hi ↦ (mem_fiber q b i).mp hi),
    fiber_image σ hσ q hmir b, fiber_stable_iff_real σ hσ q hmir b,
    fun hb ↦ real_child_ratio_tendsto_zero (fiber q b) a b p φ q hlim
      (fun i hi ↦ (mem_fiber q b i).mp hi) hb⟩

section Ordered

variable {J : Type*} [Preorder J]

/-- Real-coordinate order on any selected labels is preserved by the actual
common real center and positive-real scaling. -/
theorem normalized_re_monotone_on (a : I) (p : I → ℂ) (e : J → I)
    (hp : Monotone (fun j ↦ (p (e j)).re)) :
    Monotone (fun j ↦ (normalized a p (e j)).re) := by
  intro i j hij
  simp only [normalized, centered, Pi.smul_apply, Complex.smul_re, Complex.sub_re,
    Complex.ofReal_re, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hp hij) _) (inv_nonneg.mpr (radius_nonneg a p))

/-- Ordered real boundary labels retain their weak order in the actual limit,
including when the centering anchor is not itself a boundary label. -/
theorem limit_re_monotone_on (a : I) (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : I → ℂ)
    (hlim : Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q)) (e : J → I)
    (hp : ∀ n, Monotone (fun j ↦ (p n (e j)).re)) : Monotone (fun j ↦ (q (e j)).re) := by
  intro i j hij
  have hi : Tendsto (fun n ↦ (normalized a (p (φ n)) (e i)).re) atTop (𝓝 (q (e i)).re) := by
    simpa only [Function.comp_def] using
      (Complex.continuous_re.comp (continuous_apply (e i))).tendsto q |>.comp hlim
  have hj : Tendsto (fun n ↦ (normalized a (p (φ n)) (e j)).re) atTop (𝓝 (q (e j)).re) := by
    simpa only [Function.comp_def] using
      (Complex.continuous_re.comp (continuous_apply (e j))).tendsto q |>.comp hlim
  exact le_of_tendsto_of_tendsto hi hj
    (Eventually.of_forall fun n ↦ normalized_re_monotone_on a (p (φ n)) e (hp (φ n)) hij)

variable [Preorder I]

theorem normalized_re_monotone (a : I) (p : I → ℂ) (hp : Monotone (fun i ↦ (p i).re)) :
    Monotone (fun i ↦ (normalized a p i).re) := normalized_re_monotone_on a p id hp

theorem limit_re_monotone (a : I) (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : I → ℂ)
    (hlim : Tendsto (fun n ↦ normalized a (p (φ n))) atTop (𝓝 q))
    (hp : ∀ n, Monotone (fun i ↦ (p n i).re)) : Monotone (fun i ↦ (q i).re) :=
  limit_re_monotone_on a p φ q hlim id hp

/-- Real fibers of an ordered real limiting configuration are contiguous. -/
theorem mem_fiber_of_between (q : I → ℂ) (hq : Monotone (fun i ↦ (q i).re))
    (hreal : ∀ i, (q i).im = 0) (b : I) {i j l : I} (hij : i ≤ j) (hjl : j ≤ l)
    (hi : i ∈ fiber q b) (hl : l ∈ fiber q b) : j ∈ fiber q b := by
  apply (mem_fiber q b j).mpr
  apply Complex.ext
  · exact le_antisymm (by simpa only [(mem_fiber q b l).mp hl] using hq hjl)
      (by simpa only [(mem_fiber q b i).mp hi] using hq hij)
  · simp only [hreal]

end Ordered

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedClusterLimits
