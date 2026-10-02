import EnvelopingIsomorphism.PBW.Rules
import EnvelopingIsomorphism.PBW.WordIndex
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Weight

/-! Support bounds inherited by the PBW normalizer. -/

noncomputable section

namespace EnvelopingIsomorphism.PBW

open Finsupp

namespace ReductionSystem

variable {R W : Type*} [CommRing R] (s : ReductionSystem R W)

/-- Any condition on words preserved by every rule is preserved by normalization. -/
theorem normalWord_mem_supported (P : W → Prop)
    (hp : ∀ w q, s.step w q → P w → ∀ v ∈ q.support, P v)
    {w : W} (hw : P w) :
    s.normalWord w ∈ Finsupp.supported R R {v : {v // s.Normal v} | P v.val} := by
  classical
  induction w using s.wellFounded.induction with
  | h w ih =>
    by_cases hn : s.Normal w
    · rw [s.normalWord_of_normal hn]
      exact Finsupp.single_mem_supported R 1 hw
    · have hn' : ∃ q, s.step w q := not_not.mp hn
      rw [s.normalWord_of_reducible hn']
      simp only [normalize, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Submodule.sum_mem
      intro v hv
      apply Submodule.smul_mem
      exact ih v (s.support_smaller hn'.choose_spec v hv)
        (hp w hn'.choose hn'.choose_spec hw v hv)

/-- The same support preservation for a finite linear combination of words. -/
theorem normalize_mem_supported (P : W → Prop)
    (hp : ∀ w q, s.step w q → P w → ∀ v ∈ q.support, P v)
    {p : W →₀ R} (h : ∀ w ∈ p.support, P w) :
    s.normalize p ∈ Finsupp.supported R R {v : {v // s.Normal v} | P v.val} := by
  classical
  simp only [normalize, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (s.normalWord_mem_supported P hp (h w hw))

end ReductionSystem

variable {R L α : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LinearOrder α] (b : Module.Basis α R L)

theorem step_support_length_le {w : List α} {q : List α →₀ R}
    (hq : Step b w q) {v : List α} (hv : v ∈ q.support) : v.length ≤ w.length := by
  have hlt := step_support_smaller b hq hv
  change Prod.Lex (· < ·) (· < ·) (v.length, inversionCount v)
    (w.length, inversionCount w) at hlt
  rcases Prod.lex_iff.mp hlt with h | ⟨h, _⟩
  · exact Nat.le_of_lt h
  · exact h.le

/-- PBW straightening never increases ordinary word length. -/
theorem normalWord_support_length_le {w : List α}
    {v : {v // (reductionSystem b).Normal v}}
    (hv : v ∈ ((reductionSystem b).normalWord w).support) : v.val.length ≤ w.length := by
  have h := (reductionSystem b).normalWord_mem_supported
    (fun z ↦ z.length ≤ w.length)
    (fun z q hq hz u hu ↦ (step_support_length_le b hq hu).trans hz)
    (le_refl w.length)
  exact h hv

/-- Additive weight of a word, using Mathlib's finitely supported weight map. -/
def wordWeight (ω : α → ℕ) (w : List α) : ℕ := Finsupp.weight ω (wordIndex w)

@[simp] theorem wordWeight_nil (ω : α → ℕ) : wordWeight ω [] = 0 := by
  simp [wordWeight]

@[simp] theorem wordWeight_append (ω : α → ℕ) (u v : List α) :
    wordWeight ω (u ++ v) = wordWeight ω u + wordWeight ω v := by
  simp [wordWeight]

@[simp] theorem wordWeight_cons (ω : α → ℕ) (i : α) (v : List α) :
    wordWeight ω (i :: v) = ω i + wordWeight ω v := by
  simp [wordWeight, Finsupp.weight_single]

theorem step_support_weight_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    {w : List α} {q : List α →₀ R} (hq : Step b w q)
    {v : List α} (hv : v ∈ q.support) : wordWeight ω v ≤ wordWeight ω w := by
  classical
  obtain ⟨p, i, j, s, hji, rfl, rfl⟩ := hq
  rcases Finset.mem_union.mp (Finsupp.support_add hv) with hv | hv
  · have heq : v = p ++ j :: i :: s :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
    simp only [heq, wordWeight_append, wordWeight_cons]
    omega
  · obtain ⟨a, ha, rfl⟩ := insert_support_coeff b hv
    have hc' := hc i j a ha
    simp only [wordWeight_append, wordWeight_cons]
    omega

theorem step_support_weight_ge (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    {w : List α} {q : List α →₀ R} (hq : Step b w q)
    {v : List α} (hv : v ∈ q.support) : wordWeight ω w ≤ wordWeight ω v := by
  classical
  obtain ⟨p, i, j, s, hji, rfl, rfl⟩ := hq
  rcases Finset.mem_union.mp (Finsupp.support_add hv) with hv | hv
  · have heq : v = p ++ j :: i :: s :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
    simp only [heq, wordWeight_append, wordWeight_cons]
    omega
  · obtain ⟨a, ha, rfl⟩ := insert_support_coeff b hv
    have hc' := hc i j a ha
    simp only [wordWeight_append, wordWeight_cons]
    omega

/-- Upper weighted filtrations are preserved, with zero weights permitted. -/
theorem normalWord_support_weight_le (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω a ≤ ω i + ω j)
    {w : List α} {v : {v // (reductionSystem b).Normal v}}
    (hv : v ∈ ((reductionSystem b).normalWord w).support) :
    wordWeight ω v.val ≤ wordWeight ω w := by
  have h := (reductionSystem b).normalWord_mem_supported
    (fun z ↦ wordWeight ω z ≤ wordWeight ω w)
    (fun z q hq hz u hu ↦ (step_support_weight_le b ω hc hq hu).trans hz)
    (le_refl (wordWeight ω w))
  exact h hv

/-- Lower weighted filtrations are preserved, with zero weights permitted. -/
theorem normalWord_support_weight_ge (ω : α → ℕ)
    (hc : ∀ i j a, b.repr ⁅b i, b j⁆ a ≠ 0 → ω i + ω j ≤ ω a)
    {w : List α} {v : {v // (reductionSystem b).Normal v}}
    (hv : v ∈ ((reductionSystem b).normalWord w).support) :
    wordWeight ω w ≤ wordWeight ω v.val := by
  have h := (reductionSystem b).normalWord_mem_supported
    (fun z ↦ wordWeight ω w ≤ wordWeight ω z)
    (fun z q hq hz u hu ↦ hz.trans (step_support_weight_ge b ω hc hq hu))
    (le_refl (wordWeight ω w))
  exact h hv

end EnvelopingIsomorphism.PBW
