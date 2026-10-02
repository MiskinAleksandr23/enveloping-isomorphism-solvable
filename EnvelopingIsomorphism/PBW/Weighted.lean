import EnvelopingIsomorphism.PBW.Basis
import EnvelopingIsomorphism.PBW.Support
import Mathlib.Algebra.Algebra.Operations

/-!
# Weighted PBW filtrations in the native enveloping algebra

The one existing PBW normalizer supplies support estimates for the native
PBW coordinates. Upper and lower weight bounds give separate multiplicative
filtrations; weights are allowed to be zero.
-/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder α] (b : Module.Basis α R L)

/-- Native PBW coordinates are the reindexed coordinates of the one normalizer. -/
theorem pbwBasis_repr_wordEval (p : List α →₀ R) :
    (pbwBasis b).repr (wordEval b p) =
      ((reductionSystem b).normalize p).mapDomain (normalIndexEquiv b) := by
  change (quotientPBWBasis b).repr ((presentationEquiv b).symm (wordEval b p)) = _
  rw [← presentationEquiv_mk, LinearEquiv.symm_apply_apply]
  simp only [quotientPBWBasis, Module.Basis.repr_reindex]
  congr 1

/-- PBW coordinates of an arbitrary product of original basis vectors. -/
theorem pbwBasis_repr_word (w : List α) :
    (pbwBasis b).repr ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod) =
      ((reductionSystem b).normalWord w).mapDomain (normalIndexEquiv b) := by
  rw [← wordEval_single_one, pbwBasis_repr_wordEval]
  simp

/-- Ordinary PBW degree never exceeds the length of an input word. -/
theorem pbwBasis_repr_word_support_length_le {w : List α} {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr
      ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod)).support) :
    (orderedWord m).length ≤ w.length := by
  classical
  rw [pbwBasis_repr_word] at hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  have h := normalWord_support_length_le b hv
  change (orderedWord (wordIndex v.val)).length ≤ w.length
  rwa [orderedWord_wordIndex ((normal_iff_pairwise b _).mp v.property)]

theorem pbwBasis_repr_word_support_weight_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    {w : List α} {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr
      ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod)).support) :
    Finsupp.weight ω m ≤ wordWeight ω w := by
  classical
  rw [pbwBasis_repr_word] at hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  exact normalWord_support_weight_le b ω hc hv

theorem pbwBasis_repr_word_support_weight_ge (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    {w : List α} {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr
      ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod)).support) :
    wordWeight ω w ≤ Finsupp.weight ω m := by
  classical
  rw [pbwBasis_repr_word] at hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  exact normalWord_support_weight_ge b ω hc hv

/-- Upper PBW weight submodule. Zero weights are permitted. -/
def weightedUpper (ω : α → ℕ) (d : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R (pbwBasis b '' {m | Finsupp.weight ω m ≤ d})

/-- Lower PBW weight submodule. Zero weights are permitted. -/
def weightedLower (ω : α → ℕ) (d : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R (pbwBasis b '' {m | d ≤ Finsupp.weight ω m})

theorem mem_weightedUpper_iff (ω : α → ℕ) (d : ℕ)
    (x : UniversalEnvelopingAlgebra R L) :
    x ∈ weightedUpper b ω d ↔
      ∀ m ∈ ((pbwBasis b).repr x).support, Finsupp.weight ω m ≤ d :=
  (pbwBasis b).mem_span_image

theorem mem_weightedLower_iff (ω : α → ℕ) (d : ℕ)
    (x : UniversalEnvelopingAlgebra R L) :
    x ∈ weightedLower b ω d ↔
      ∀ m ∈ ((pbwBasis b).repr x).support, d ≤ Finsupp.weight ω m :=
  (pbwBasis b).mem_span_image

theorem word_mem_weightedUpper (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (w : List α) :
    (w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod ∈
      weightedUpper b ω (wordWeight ω w) :=
  (mem_weightedUpper_iff b ω _ _).mpr fun _ hm ↦
    pbwBasis_repr_word_support_weight_le b ω hc hm

theorem word_mem_weightedLower (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    (w : List α) :
    (w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod ∈
      weightedLower b ω (wordWeight ω w) :=
  (mem_weightedLower_iff b ω _ _).mpr fun _ hm ↦
    pbwBasis_repr_word_support_weight_ge b ω hc hm

theorem weightedUpper_mono (ω : α → ℕ) {d e : ℕ} (h : d ≤ e) :
    weightedUpper b ω d ≤ weightedUpper b ω e :=
  Submodule.span_mono (Set.image_mono fun _ hm ↦ hm.trans h)

theorem weightedLower_antitone (ω : α → ℕ) {d e : ℕ} (h : d ≤ e) :
    weightedLower b ω e ≤ weightedLower b ω d :=
  Submodule.span_mono (Set.image_mono fun _ hm ↦ h.trans hm)

theorem pbwBasis_mem_weightedUpper (ω : α → ℕ) {m : α →₀ ℕ} {d : ℕ}
    (hm : Finsupp.weight ω m ≤ d) : pbwBasis b m ∈ weightedUpper b ω d :=
  Submodule.subset_span ⟨m, hm, rfl⟩

theorem pbwBasis_mem_weightedLower (ω : α → ℕ) {m : α →₀ ℕ} {d : ℕ}
    (hm : d ≤ Finsupp.weight ω m) : pbwBasis b m ∈ weightedLower b ω d :=
  Submodule.subset_span ⟨m, hm, rfl⟩

theorem pbwBasis_mul_mem_weightedUpper (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (m n : α →₀ ℕ) :
    pbwBasis b m * pbwBasis b n ∈
      weightedUpper b ω (Finsupp.weight ω m + Finsupp.weight ω n) := by
  simpa only [List.map_append, List.prod_append, wordWeight,
    wordIndex_append, wordIndex_orderedWord, map_add, pbwBasis_apply] using
    word_mem_weightedUpper b ω hc (orderedWord m ++ orderedWord n)

theorem pbwBasis_mul_mem_weightedLower (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    (m n : α →₀ ℕ) :
    pbwBasis b m * pbwBasis b n ∈
      weightedLower b ω (Finsupp.weight ω m + Finsupp.weight ω n) := by
  simpa only [List.map_append, List.prod_append, wordWeight,
    wordIndex_append, wordIndex_orderedWord, map_add, pbwBasis_apply] using
    word_mem_weightedLower b ω hc (orderedWord m ++ orderedWord n)

/-- Multiplication adds upper filtration bounds. -/
theorem weightedUpper_mul_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    (d e : ℕ) :
    weightedUpper b ω d * weightedUpper b ω e ≤ weightedUpper b ω (d + e) := by
  change Submodule.span R _ * Submodule.span R _ ≤ _
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨n, hn, rfl⟩, rfl⟩
  exact weightedUpper_mono b ω (Nat.add_le_add hm hn)
    (pbwBasis_mul_mem_weightedUpper b ω hc m n)

/-- Multiplication adds lower filtration bounds. -/
theorem weightedLower_mul_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    (d e : ℕ) :
    weightedLower b ω d * weightedLower b ω e ≤ weightedLower b ω (d + e) := by
  change Submodule.span R _ * Submodule.span R _ ≤ _
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨n, hn, rfl⟩, rfl⟩
  exact weightedLower_antitone b ω (Nat.add_le_add hm hn)
    (pbwBasis_mul_mem_weightedLower b ω hc m n)

@[simp] theorem weightedLower_zero (ω : α → ℕ) : weightedLower b ω 0 = ⊤ := by
  simp only [weightedLower, Nat.zero_le, Set.setOf_true, Set.image_univ, (pbwBasis b).span_eq]

/-- Every element has an upper PBW weight bound, also when some weights vanish. -/
theorem exists_mem_weightedUpper (ω : α → ℕ) (x : UniversalEnvelopingAlgebra R L) :
    ∃ d, x ∈ weightedUpper b ω d := by
  classical
  refine ⟨((pbwBasis b).repr x).support.sup (Finsupp.weight ω), ?_⟩
  exact (mem_weightedUpper_iff b ω _ x).mpr fun _ hm ↦ Finset.le_sup hm

/-- Lower PBW weight submodules have zero intersection. -/
theorem iInf_weightedLower (ω : α → ℕ) : (⨅ d, weightedLower b ω d) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply (pbwBasis b).repr.injective
    rw [map_zero]
    ext m
    by_contra hm
    have h := (mem_weightedLower_iff b ω (Finsupp.weight ω m + 1) x).mp
      ((iInf_le (fun d ↦ weightedLower b ω d) (Finsupp.weight ω m + 1)) hx) m
      (Finsupp.mem_support_iff.mpr hm)
    omega
  · exact bot_le

/-- The first lower filtration piece generates powers contained in the
corresponding higher pieces. -/
theorem weightedLower_one_pow_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    (d : ℕ) : (weightedLower b ω 1) ^ d ≤ weightedLower b ω d := by
  induction d with
  | zero => rw [weightedLower_zero]; exact le_top
  | succ d ih =>
      rw [pow_succ]
      apply Submodule.mul_le.mpr
      intro x hx y hy
      exact weightedLower_mul_le b ω hc d 1 (Submodule.mul_mem_mul (ih hx) hy)

/-- Unit weight is ordinary word length. -/
@[simp] theorem wordWeight_one (w : List α) : wordWeight (fun _ : α ↦ 1) w = w.length := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, Nat.add_comm]

/-- The ordinary PBW degree estimate, stated directly for exponent vectors. -/
theorem pbwBasis_repr_word_support_degree_le {w : List α} {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr
      ((w.map (UniversalEnvelopingAlgebra.ι R ∘ b)).prod)).support) :
    m.sum (fun _ n ↦ n) ≤ w.length := by
  simpa only [length_orderedWord] using pbwBasis_repr_word_support_length_le b hm

end EnvelopingIsomorphism.PBW
