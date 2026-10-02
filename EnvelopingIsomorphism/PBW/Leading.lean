import EnvelopingIsomorphism.PBW.Weighted

/-! The leading commutative term in PBW straightening. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

/-- Straightening has the sorted input as leading term with coefficient one. -/
theorem normalWord_sub_sorted_mem_supported (w : List α) :
    (reductionSystem b).normalWord w -
      single ((normalIndexEquiv b).symm (wordIndex w)) 1 ∈
    Finsupp.supported R R
      {v : {v // (reductionSystem b).Normal v} | v.val.length < w.length} := by
  classical
  induction w using (reductionSystem b).wellFounded.induction with
  | h w ih =>
    by_cases hw : w.Pairwise (· ≤ ·)
    · have hn := (normal_iff_pairwise b w).2 hw
      have hidx : (normalIndexEquiv b).symm (wordIndex w) = ⟨w, hn⟩ := by
        apply Subtype.ext
        exact orderedWord_wordIndex hw
      rw [(reductionSystem b).normalWord_of_normal hn, hidx, sub_self]
      exact Submodule.zero_mem _
    · obtain ⟨p, i, j, t, rfl, hji⟩ := exists_adjacent_inversion w hw
      have hstep : (reductionSystem b).step (p ++ i :: j :: t) (rhs b p i j t) :=
        ⟨p, i, j, t, hji, rfl, rfl⟩
      rw [(reductionSystem b).normalize_step (reductionSystem_compatible b) hstep,
        rhs, map_add, ReductionSystem.normalize_single_one]
      have hswap := ih (p ++ j :: i :: t) (wordLT_swap p t hji)
      have hidx : wordIndex (p ++ j :: i :: t) = wordIndex (p ++ i :: j :: t) := by
        simp [add_left_comm]
      rw [hidx] at hswap
      have hlen : (p ++ j :: i :: t).length = (p ++ i :: j :: t).length := by simp
      rw [hlen] at hswap
      have hbracket : (reductionSystem b).normalize (insert b p t ⁅b i, b j⁆) ∈
          Finsupp.supported R R {v : {v // (reductionSystem b).Normal v} |
            v.val.length < (p ++ i :: j :: t).length} := by
        apply (reductionSystem b).normalize_mem_supported
          (fun z ↦ z.length < (p ++ i :: j :: t).length)
          (fun z q hq hz u hu ↦ (step_support_length_le b hq hu).trans_lt hz)
        intro z hz
        obtain ⟨a, rfl⟩ := insert_support b hz
        exact length_replacePair_lt p t i j a
      convert Submodule.add_mem _ hswap hbracket using 1; abel

/-- In native PBW coordinates, the only terms of maximal length are the sorted input. -/
theorem pbwBasis_repr_wordEval_sub_single_mem_supported (w : List α) :
    (pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1 ∈
      Finsupp.supported R R {m : α →₀ ℕ | (orderedWord m).length < w.length} := by
  classical
  have heq : (pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1 =
      ((reductionSystem b).normalWord w -
        single ((normalIndexEquiv b).symm (wordIndex w)) 1).mapDomain (normalIndexEquiv b) := by
    rw [pbwBasis_repr_wordEval]
    simp [Finsupp.mapDomain_sub]
  rw [heq]
  intro m hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  have h := normalWord_sub_sorted_mem_supported b w hv
  have hvword : orderedWord (normalIndexEquiv b v) = v.val :=
    orderedWord_wordIndex ((normal_iff_pairwise b _).1 v.property)
  simpa only [Set.mem_setOf_eq, hvword] using h

theorem pbwBasis_repr_wordEval_sub_single_length_lt (w : List α) {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1).support) :
    (orderedWord m).length < w.length :=
  pbwBasis_repr_wordEval_sub_single_mem_supported b w hm

/-- With strictly weight-lowering brackets, the PBW correction has strictly smaller weight.
Weights of individual generators may be zero. -/
theorem normalWord_sub_sorted_mem_supported_weight (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (w : List α) :
    (reductionSystem b).normalWord w -
      single ((normalIndexEquiv b).symm (wordIndex w)) 1 ∈
    Finsupp.supported R R {v : {v // (reductionSystem b).Normal v} |
      wordWeight ω v.val < wordWeight ω w} := by
  classical
  induction w using (reductionSystem b).wellFounded.induction with
  | h w ih =>
    by_cases hw : w.Pairwise (· ≤ ·)
    · have hn := (normal_iff_pairwise b w).2 hw
      have hidx : (normalIndexEquiv b).symm (wordIndex w) = ⟨w, hn⟩ := by
        apply Subtype.ext
        exact orderedWord_wordIndex hw
      rw [(reductionSystem b).normalWord_of_normal hn, hidx, sub_self]
      exact Submodule.zero_mem _
    · obtain ⟨p, i, j, t, rfl, hji⟩ := exists_adjacent_inversion w hw
      have hstep : (reductionSystem b).step (p ++ i :: j :: t) (rhs b p i j t) :=
        ⟨p, i, j, t, hji, rfl, rfl⟩
      rw [(reductionSystem b).normalize_step (reductionSystem_compatible b) hstep,
        rhs, map_add, ReductionSystem.normalize_single_one]
      have hswap := ih (p ++ j :: i :: t) (wordLT_swap p t hji)
      have hidx : wordIndex (p ++ j :: i :: t) = wordIndex (p ++ i :: j :: t) := by
        simp [add_left_comm]
      have hweight : wordWeight ω (p ++ j :: i :: t) =
          wordWeight ω (p ++ i :: j :: t) := by rw [wordWeight, hidx]; rfl
      rw [hidx, hweight] at hswap
      have hbracket : (reductionSystem b).normalize (insert b p t ⁅b i, b j⁆) ∈
          Finsupp.supported R R {v : {v // (reductionSystem b).Normal v} |
            wordWeight ω v.val < wordWeight ω (p ++ i :: j :: t)} := by
        apply (reductionSystem b).normalize_mem_supported
          (fun z ↦ wordWeight ω z < wordWeight ω (p ++ i :: j :: t))
          (fun z q hq hz u hu ↦
            (step_support_weight_le b ω (fun a c e h ↦ (hc a c e h).le) hq hu).trans_lt hz)
        intro z hz
        obtain ⟨a, ha, rfl⟩ := insert_support_coeff b hz
        have hca := hc i j a ha
        simp only [wordWeight_append, wordWeight_cons]
        omega
      convert Submodule.add_mem _ hswap hbracket using 1; abel

/-- Weighted leading-term statement in the native UEA's PBW coefficients. -/
theorem pbwBasis_repr_wordEval_sub_single_mem_supported_weight (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (w : List α) :
    (pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1 ∈
      Finsupp.supported R R {m : α →₀ ℕ | Finsupp.weight ω m < wordWeight ω w} := by
  classical
  have heq : (pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1 =
      ((reductionSystem b).normalWord w -
        single ((normalIndexEquiv b).symm (wordIndex w)) 1).mapDomain (normalIndexEquiv b) := by
    rw [pbwBasis_repr_wordEval]
    simp [Finsupp.mapDomain_sub]
  rw [heq]
  intro m hm
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  exact normalWord_sub_sorted_mem_supported_weight b ω hc w hv

theorem pbwBasis_repr_wordEval_sub_single_weight_lt (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a < ω i + ω j)
    (w : List α) {m : α →₀ ℕ}
    (hm : m ∈ ((pbwBasis b).repr (wordEval b (single w 1)) - single (wordIndex w) 1).support) :
    Finsupp.weight ω m < wordWeight ω w :=
  pbwBasis_repr_wordEval_sub_single_mem_supported_weight b ω hc w hm

end EnvelopingIsomorphism.PBW
